use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Value};
use crate::list;
use crate::transformations::GensymContext;
use std::collections::HashMap;

pub struct Context {
    gs: GensymContext,
}

impl Context {
    pub fn new(sym_delim: &'static str) -> Self {
        Context {
            gs: GensymContext::new(sym_delim),
        }
    }
}

impl Context {
    pub fn eta_reduce(&'static self, exp: &Expr<Ref<str>>) -> Expr<Ref<str>> {
        match exp {
            Expr::Record(fields, r, cnt) => {
                Expr::Record(*fields, r.clone(), self.eta_reduce(cnt).into())
            }

            Expr::Select(idx, r, x, cnt) => {
                Expr::Select(*idx, r.clone(), x.clone(), self.eta_reduce(cnt).into())
            }

            Expr::Offset(idx, r, x, cnt) => {
                Expr::Offset(*idx, r.clone(), x.clone(), self.eta_reduce(cnt).into())
            }

            Expr::App(rator, rands) => Expr::App(rator.clone(), *rands),

            Expr::Fix(defs, body) => {
                let mut defs_out: Vec<(Ref<str>, Ref<[Ref<str>]>, Ref<Expr<Ref<str>>>)> = vec![];

                let mut substitutions: HashMap<_, &Value<_>> = HashMap::new();

                for (f, params, fbody) in defs.iter() {
                    match &**fbody {
                        Expr::App(Value::Var(g) | Value::Label(g), _) if f == g => {}

                        // eta reduction
                        Expr::App(g, args) if args_equal_params(params, args) => {
                            for (_, g_) in &mut substitutions {
                                match g_ {
                                    Value::Var(v) | Value::Label(v) if v == f => *g_ = g,
                                    _ => {}
                                }
                            }
                            substitutions.insert(f, g);
                            continue;
                        }

                        // uncurrying ... this is the transformation on top of page 77
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

                            let mut f_args: Vec<Value<_>> =
                                fparams.iter().map(|p| Value::Var(*p)).collect();
                            f_args.push(Value::Var(g_));
                            f_args.push(Value::Var(b_));
                            f_args.push(Value::Var(k_));

                            let fbody_out = Expr::Fix(
                                list![(
                                    g_,
                                    list![b_, k_],
                                    Expr::App(Value::Var(f_), Ref::array(f_args)).into()
                                )],
                                Expr::App(Value::Var(c_), list![Value::Var(g_)]).into(),
                            );

                            defs_out.push((f.clone(), Ref::array(fparams), fbody_out.into()));

                            let mut f_params: Vec<_> = params.iter().copied().collect();
                            f_params.push(*g);
                            f_params.push(*b);
                            f_params.push(*k);

                            defs_out.push((
                                f_,
                                Ref::array(f_params),
                                self.eta_reduce(gbody).into(),
                            ));

                            continue;
                        }

                        _ => {}
                    }
                    defs_out.push((f.clone(), *params, self.eta_reduce(fbody).into()));
                }

                let mut body = *body;
                for (f, g) in substitutions {
                    body = body.substitute_var(f, g).into();
                    for (_, _, fb) in &mut defs_out {
                        *fb = fb.substitute_var(f, g).into();
                    }
                }

                let body = self.eta_reduce(&*body);

                if defs_out.is_empty() {
                    body
                } else {
                    Expr::Fix(Ref::array(defs_out), body.into())
                }
            }

            Expr::Switch(v, arms) => Expr::Switch(
                v.clone(),
                Ref::array(arms.iter().map(|x| self.eta_reduce(x).into()).collect()),
            ),

            Expr::PrimOp(op, args, res, cnts) => Expr::PrimOp(
                *op,
                *args,
                *res,
                Ref::array(cnts.iter().map(|c| self.eta_reduce(c).into()).collect()),
            ),

            Expr::Panic(msg) => Expr::Panic(*msg),
        }
    }
}

fn args_equal_params<V: PartialEq>(params: &Ref<[V]>, args: &Ref<[Value<V>]>) -> bool {
    params.len() == args.len()
        && params.iter().zip(args.iter()).all(|(p, a)| match a {
            Value::Var(x) => x == p,
            _ => false,
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{cps_expr, cps_expr_list, cps_ident_list, cps_value, cps_value_list};

    #[test]
    fn simple_reduction() {
        let ctx = Box::leak(Box::new(Context::new("__")));

        let x = cps_expr!(fix f(x)=(halt x) in (f z));
        let y = cps_expr!((halt z));
        assert_eq!(ctx.eta_reduce(&x), y);

        let x = cps_expr!(fix f(a b c)=(g a b c) in (f x y z));
        let y = cps_expr!((g x y z));
        assert_eq!(ctx.eta_reduce(&x), y);
    }

    #[test]
    fn reduction_also_in_sibling_functions() {
        let ctx = Box::leak(Box::new(Context::new("__")));

        let x = cps_expr!(fix f(x)=(halt x); g(x)=(f z) in (g z));
        let y = cps_expr!(fix g(x)=(halt z) in (g z));
        assert_eq!(ctx.eta_reduce(&x), y);
    }

    #[test]
    fn no_reduction_allowed() {
        let ctx = Box::leak(Box::new(Context::new("__")));

        let x = cps_expr!(fix f(x)=(f x) in (f z));
        assert_eq!(ctx.eta_reduce(&x), x);
    }

    #[test]
    fn multilevel_reduction() {
        let ctx = Box::leak(Box::new(Context::new("__")));

        let x = cps_expr!(fix g(x)=(f x); f(x)=(halt x) in (g z));
        let y = cps_expr!((halt z));
        assert_eq!(ctx.eta_reduce(&x), y);

        let x = cps_expr!(fix f(x)=(halt x); g(x)=(f x) in (g z));
        let y = cps_expr!((halt z));
        assert_eq!(ctx.eta_reduce(&x), y);
    }

    #[test]
    fn uncurrying() {
        let ctx = Box::leak(Box::new(Context::new("__")));

        let x = cps_expr!(fix f(x c)=(fix g(b k)=(+ [x b] [r] [(k r)]) in (c g)) in f);
        let y = cps_expr!(fix f(x__1 c__2)=(fix g__3(b__4 k__5)=(f__0 x__1 c__2 g__3 b__4 k__5) in (c__2 g__3)); f__0(x c g b k)=(+ [x b] [r] [(k r)]) in f);
        assert_eq!(ctx.eta_reduce(&x), y);
    }
}
