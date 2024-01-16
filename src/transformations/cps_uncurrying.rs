use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Value};
use crate::array;
use crate::transformations::{GenSym, GensymContext};
use std::fmt::Display;
use std::ops::Deref;
use std::sync::Arc;

pub struct Context {
    gs: Arc<GensymContext>,
}

impl Context {
    pub fn new(gs: Arc<GensymContext>) -> Self {
        Context { gs }
    }

    pub fn new_context(sym_delim: impl ToString) -> Self {
        Context {
            gs: Arc::new(GensymContext::new(sym_delim)),
        }
    }
}

impl Context {
    pub fn uncurry<V: Clone + PartialEq + Deref<Target = str> + GenSym + Display>(
        &self,
        exp: &Expr<V>,
    ) -> Expr<V> {
        match exp {
            Expr::Record(fields, r, cnt) => {
                Expr::Record(*fields, r.clone(), self.uncurry(cnt).into())
            }

            Expr::Select(idx, r, x, cnt) => {
                Expr::Select(*idx, r.clone(), x.clone(), self.uncurry(cnt).into())
            }

            Expr::Offset(idx, r, x, cnt) => {
                Expr::Offset(*idx, r.clone(), x.clone(), self.uncurry(cnt).into())
            }

            Expr::App(rator, rands) => Expr::App(rator.clone(), *rands),

            Expr::Fix(defs, body) => {
                let mut defs_out: Vec<(V, Ref<[V]>, Ref<Expr<V>>)> = vec![];

                let reduced_bodies: Vec<_> = defs
                    .iter()
                    .map(|(_, _, b)| Ref::new(self.uncurry(b)))
                    .collect();

                for ((f, params, _), fbody) in defs.iter().zip(&reduced_bodies) {
                    match &**fbody {
                        // uncurrying ... this is the transformation on top of page 77
                        Expr::Fix(
                            Ref([(g, Ref([k, b]), gbody)]),
                            Ref(Expr::App(Value::Var(c), Ref([Value::Var(gg) | Value::Label(gg)]))),
                        ) if Some(c) == params.first() && gg == g => {
                            let f_: V = self.gs.gensym(f);
                            let fparams: Vec<V> =
                                params.iter().map(|p| self.gs.gensym(p)).collect();
                            let c_ = fparams
                                .first()
                                .expect("functions need at least one parameter: the continuation")
                                .clone();
                            let g_: V = self.gs.gensym(g);
                            let b_: V = self.gs.gensym(b);
                            let k_: V = self.gs.gensym(k);

                            let mut f_args = vec![Value::Var(k_.clone())];
                            f_args.extend(fparams.iter().map(|p| Value::Var(p.clone())));
                            f_args.push(Value::Var(g_.clone()));
                            f_args.push(Value::Var(b_.clone()));

                            let fbody_out = Expr::Fix(
                                array![(
                                    g_.clone(),
                                    array![k_, b_],
                                    Expr::App(Value::Var(f_.clone()), Ref::array(f_args)).into()
                                )],
                                Expr::App(Value::Var(c_), array![Value::Var(g_)]).into(),
                            );

                            defs_out.push((f.clone(), Ref::array(fparams), fbody_out.into()));

                            let mut f_params = vec![k.clone()];
                            f_params.extend(params.iter().cloned());
                            f_params.push(g.clone());
                            f_params.push(b.clone());

                            defs_out.push((f_, Ref::array(f_params), self.uncurry(gbody).into()));
                        }

                        _ => defs_out.push((f.clone(), *params, *fbody)),
                    }
                }

                let body = self.uncurry(&*body);

                if defs_out.is_empty() {
                    body
                } else {
                    Expr::Fix(Ref::array(defs_out), body.into())
                }
            }

            Expr::Switch(v, arms) => Expr::Switch(
                v.clone(),
                Ref::array(arms.iter().map(|x| self.uncurry(x).into()).collect()),
            ),

            Expr::PrimOp(op, args, res, cnts) => Expr::PrimOp(
                *op,
                *args,
                *res,
                Ref::array(cnts.iter().map(|c| self.uncurry(c).into()).collect()),
            ),

            Expr::Halt(v) => Expr::Halt(v.clone()),

            Expr::Panic(msg) => Expr::Panic(*msg),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{cps_expr, cps_expr_list, cps_ident_list, cps_value, cps_value_list};

    fn uncurry(exp: Expr<Ref<str>>) -> Expr<Ref<str>> {
        let ctx = Box::leak(Box::new(Context::new_context("__".to_string())));
        ctx.uncurry(&exp)
    }

    #[test]
    fn uncurrying() {
        let x = cps_expr!(fix f(c x)=(fix g(k b)=(+ [x b] [r] [(k r)]) in (c g)) in f);
        let y = cps_expr!(fix f(c__1 x__2)=(fix g__3(k__5 b__4)=(f__0 k__5 c__1 x__2 g__3 b__4) in (c__1 g__3)); f__0(k c x g b)=(+ [x b] [r] [(k r)]) in f);
        assert_eq!(uncurry(x), y);
    }
}
