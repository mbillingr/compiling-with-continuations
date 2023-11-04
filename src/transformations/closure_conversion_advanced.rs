use crate::languages::cps_lang::ast::{Computation, Compute, Expr, Value};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// Requirements:
///   - unique names
///   - labels
struct Context<V, F> {
    vars_free_in_fn: HashMap<F, HashSet<V>>,
    fns_applied_in_fn: HashMap<F, HashSet<F>>,
    known_functions: HashSet<F>, // All functions that never escape, I suppose...
}

impl<V, F> Context<V, F> {
    pub fn new() -> Self {
        Context {
            vars_free_in_fn: Default::default(),
            fns_applied_in_fn: Default::default(),
            known_functions: Default::default(),
        }
    }
}

impl<'e, V: Clone + Eq + Hash, F: Clone + Eq + Hash> Compute<'e, V, F> for Context<V, F> {
    fn visit_expr(&mut self, expr: &'e Expr<V, F>) -> Computation {
        match expr {
            Expr::Fix(defs, _) => {
                self.known_functions
                    .extend(defs.iter().map(|(f, _, _)| f.clone()));

                self.vars_free_in_fn.extend(
                    defs.iter()
                        .map(|(f, p, b)| (f, Expr::function_free_vars_nofns(p, b)))
                        .map(|(f, fvs)| (f.clone(), fvs.into())),
                );

                self.fns_applied_in_fn.extend(defs.iter().map(|(f, _, b)| {
                    let mut applied_in = FnsApplied::new();
                    applied_in.compute_for_expr(b);
                    (f.clone(), applied_in.0)
                }));

                Computation::Continue
            }

            Expr::App(_, args) => {
                self.compute_for_values(args);
                Computation::Done
            }

            _ => Computation::Continue,
        }
    }

    fn visit_value(&mut self, value: &Value<V, F>) {
        match value {
            Value::Label(f) => {
                // This function escapes (unless it's the first value of an App node, which should
                // not call this visitor).
                self.known_functions.remove(f);
            }
            _ => {}
        }
    }

    fn post_visit_expr(&mut self, _: &'e Expr<V, F>) {}
}

struct FnsApplied<F>(HashSet<F>);

impl<F> FnsApplied<F> {
    pub fn new() -> Self {
        FnsApplied(HashSet::new())
    }
}

impl<'e, V: Clone + Eq + Hash, F: Clone + Eq + Hash> Compute<'e, V, F> for FnsApplied<F> {
    fn visit_expr(&mut self, expr: &'e Expr<V, F>) -> Computation {
        match expr {
            Expr::App(Value::Label(f), _) => {
                self.0.insert(f.clone());
                Computation::Done
            }

            Expr::Fix(_, cnt) => {
                self.compute_for_expr(cnt);
                Computation::Done
            }

            _ => Computation::Continue,
        }
    }

    fn visit_value(&mut self, _: &Value<V, F>) {}

    fn post_visit_expr(&mut self, _: &'e Expr<V, F>) {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use map_macro::{hash_map, hash_set};

    #[test]
    fn find_free_vars() {
        let x = Expr::from_str(
            "(fix ((f () (fix ((g () (y))) (x (@ g))))) (fix ((h () (z))) ((@ h))))",
        )
        .unwrap();
        let mut ctx = Context::new();
        ctx.compute_for_expr(&x);
        assert_eq!(
            ctx.vars_free_in_fn,
            hash_map! {
            "h".into() => hash_set!["z".into()],
            "g".into() => hash_set!["y".into()],
            "f".into() => hash_set!["x".into(), "y".into()]}
        )
    }

    #[test]
    fn find_known_functions() {
        let x = Expr::from_str(
            "(fix ((f () (fix ((g () (y (@ f)))) ((@ g))))) (fix ((h () (z))) ((@ g))))",
        )
        .unwrap();
        let mut ctx = Context::new();
        ctx.compute_for_expr(&x);
        assert_eq!(ctx.known_functions, hash_set!["g".into(), "h".into()]) // f escapes
    }

    #[test]
    fn find_applied_in_bodies() {
        let x = Expr::from_str(
            "(fix ((f () (fix ((g () ((@ h)))) ((@ g))))) (fix ((h () ((@ f)))) (halt 0)))",
        )
        .unwrap();
        let mut ctx = Context::new();
        ctx.compute_for_expr(&x);
        assert_eq!(
            ctx.fns_applied_in_fn,
            hash_map! {
            "h".into() => hash_set!["f".into()],
            "g".into() => hash_set!["h".into()],
            "f".into() => hash_set!["g".into()]}
        )
    }
}
