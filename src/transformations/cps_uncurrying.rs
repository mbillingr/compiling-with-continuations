use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{AccessPath, Expr, Value};
use crate::list;
use crate::transformations::GensymContext;

pub struct Context {
    gs: GensymContext,
}

impl Context {
    pub fn new(sym_delim: impl ToString) -> Self {
        Context {
            gs: GensymContext::new(sym_delim),
        }
    }
}

impl Context {
    pub fn uncurry(&self, exp: &Expr<Ref<str>>) -> Expr<Ref<str>> {
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
                let mut defs_out: Vec<(Ref<str>, Ref<[Ref<str>]>, Ref<Expr<Ref<str>>>)> = vec![];

                let reduced_bodies: Vec<_> = defs
                    .iter()
                    .map(|(_, _, b)| Ref::new(self.uncurry(b)))
                    .collect();

                for ((f, params, _), fbody) in defs.iter().zip(&reduced_bodies) {
                    match &**fbody {
                        // uncurrying ... this is the transformation on top of page 77
                        //            ... with the extension that it creates a record for the arguments
                        Expr::Fix(
                            Ref([(g, Ref([b, k]), gbody)]),
                            Ref(Expr::App(Value::Var(c), Ref([Value::Var(gg) | Value::Label(gg)]))),
                        ) if Some(c) == params.last() && gg == g => {
                            let f_ = self.gs.gensym(f);
                            let fparams: Vec<_> =
                                params.iter().map(|p| self.gs.gensym(p)).collect();
                            let c_ = *fparams
                                .last()
                                .expect("functions need at least one parameter: the continuation");
                            let g_ = self.gs.gensym(g);
                            let b_ = self.gs.gensym(b);
                            let k_ = self.gs.gensym(k);
                            let args_ = self.gs.gensym("args");
                            let pars_ = self.gs.gensym("args");

                            let mut f_args: Vec<Value<_>> =
                                fparams.iter().map(|p| Value::Var(*p)).collect();
                            f_args.push(Value::Var(g_));
                            f_args.push(Value::Var(b_));

                            let fbody_out = Expr::Fix(
                                list![(
                                    g_,
                                    list![b_, k_],
                                    Expr::Record(
                                        Ref::array(
                                            f_args
                                                .into_iter()
                                                .map(|f| (f, AccessPath::Ref(0)))
                                                .collect()
                                        ),
                                        args_,
                                        Expr::App(
                                            Value::Var(f_),
                                            Ref::array(vec![Value::Var(args_), Value::Var(k_)])
                                        )
                                        .into()
                                    )
                                    .into()
                                )],
                                Expr::App(Value::Var(c_), list![Value::Var(g_)]).into(),
                            );

                            defs_out.push((f.clone(), Ref::array(fparams), fbody_out.into()));

                            let mut f_params: Vec<_> = params.iter().copied().collect();
                            f_params.push(*g);
                            f_params.push(*b);

                            let mut body_out = Ref::new(self.uncurry(gbody));

                            for (i, p) in f_params.into_iter().enumerate().rev() {
                                body_out = Ref::new(Expr::Select(
                                    i as isize,
                                    Value::Var(pars_),
                                    p,
                                    body_out,
                                ));
                            }

                            defs_out.push((f_, Ref::array(vec![pars_, *k]), body_out));
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
    use crate::{
        cps_expr, cps_expr_list, cps_field, cps_field_list, cps_ident_list, cps_value,
        cps_value_list,
    };

    fn uncurry(exp: Expr<Ref<str>>) -> Expr<Ref<str>> {
        let ctx = Box::leak(Box::new(Context::new("__".to_string())));
        ctx.uncurry(&exp)
    }

    #[test]
    fn uncurrying() {
        let x = cps_expr!(fix f(x c)=(fix g(b k)=(+ [x b] [r] [(k r)]) in (c g)) in f);
        let y = cps_expr!(
            fix f(x__1 c__2)=
                    (fix g__3(b__4 k__5)=
                            (record [x__1 c__2 g__3 b__4] args__6 (f__0 args__6 k__5))
                      in (c__2 g__3));
                f__0(args__7 k)=
                    (select 0 args__7 x
                        (select 1 args__7 c
                            (select 2 args__7 g
                                (select 3 args__7 b
                                    (+ [x b] [r] [(k r)])))))
            in f);
        assert_eq!(uncurry(x), y);
    }
}
