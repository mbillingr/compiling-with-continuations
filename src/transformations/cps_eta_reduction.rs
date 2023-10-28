use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Value};
use std::collections::HashMap;
use std::hash::Hash;

pub struct Context;

impl Context {}

impl Context {
    pub fn eta_reduce<V: Clone + Eq + Hash>(&'static self, exp: &Expr<V>) -> Expr<V> {
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
                let mut defs_out: Vec<(V, Ref<[V]>, Ref<Expr<V>>)> = vec![];

                let mut substitutions = Substitution::new();

                let reduced_bodies: Vec<_> = defs
                    .iter()
                    .map(|(_, _, b)| Ref::new(self.eta_reduce(b)))
                    .collect();

                for ((f, params, _), fbody) in defs.iter().zip(&reduced_bodies) {
                    match &**fbody {
                        Expr::App(Value::Var(g) | Value::Label(g), _) if f == g => {}

                        // eta reduction
                        Expr::App(g, args) if args_equal_params(params, args) => {
                            substitutions.insert(f, g);
                            continue;
                        }

                        _ => {}
                    }
                    defs_out.push((f.clone(), *params, *fbody));
                }

                let mut body = *body;
                for (f, g) in substitutions.iter() {
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

            Expr::Halt(v) => Expr::Halt(v.clone()),

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

struct Substitution<'a, V: 'static>(HashMap<&'a V, &'a Value<V>>);

impl<'a, V: Eq + Hash> Substitution<'a, V> {
    fn new() -> Self {
        Substitution(HashMap::new())
    }

    fn insert(&mut self, key: &'a V, value: &'a Value<V>) {
        for (_, g_) in &mut self.0 {
            match g_ {
                Value::Var(v) | Value::Label(v) if v == key => *g_ = value,
                _ => {}
            }
        }
        match value {
            Value::Var(v) | Value::Label(v) if self.0.contains_key(v) => {
                self.0.insert(key, self.0[v])
            }
            _ => self.0.insert(key, value),
        };
    }

    fn iter(&self) -> impl Iterator<Item = (&&V, &&Value<V>)> + '_ {
        self.0.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{cps_expr, cps_ident_list, cps_value};

    fn eta_reduce(exp: Expr<Ref<str>>) -> Expr<Ref<str>> {
        Context.eta_reduce(&exp)
    }

    #[test]
    fn simple_reduction() {
        let x = cps_expr!(fix f(x)=(g x) in (f z));
        let y = cps_expr!((g z));
        assert_eq!(eta_reduce(x), y);

        let x = cps_expr!(fix f(a b c)=(g a b c) in (f x y z));
        let y = cps_expr!((g x y z));
        assert_eq!(eta_reduce(x), y);
    }

    #[test]
    fn reduction_also_in_sibling_functions() {
        let x = cps_expr!(fix f(x)=(h x); g(x)=(f z) in (g z));
        let y = cps_expr!(fix g(x)=(h z) in (g z));
        assert_eq!(eta_reduce(x), y);
    }

    #[test]
    fn no_reduction_allowed() {
        let x = cps_expr!(fix f(x)=(f x) in (f z));
        let y = x.clone();
        assert_eq!(eta_reduce(x), y);
    }

    #[test]
    fn multilevel_reduction() {
        let x = cps_expr!(fix g(x)=(f x); f(x)=(h x) in (g z));
        let y = cps_expr!((h z));
        assert_eq!(eta_reduce(x), y);

        let x = cps_expr!(fix f(x)=(h x); g(x)=(f x) in (g z));
        let y = cps_expr!((h z));
        assert_eq!(eta_reduce(x), y);

        let x = cps_expr!(fix f(x)=(h x) in (fix g(x)=(f x) in (g z)));
        let y = cps_expr!((h z));
        assert_eq!(eta_reduce(x), y);

        let x = cps_expr!(fix g(x)=(fix f(x)=(h x) in (f x)) in (g z));
        let y = cps_expr!((h z));
        assert_eq!(eta_reduce(x), y);
    }
}
