use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Computation, Compute, Expr, Transform, Transformed, Value};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

pub fn purge_dead_functions<V: Clone, F: Clone + Eq + Hash>(
    expr: &Expr<V, F>,
) -> Option<Expr<V, F>> {
    let mns = MarkAndSweep::mark(expr);
    if mns.all_reachable() {
        None
    } else {
        Some(mns.sweep(expr))
    }
}

struct MarkAndSweep<'e, V: 'static, F: 'static> {
    function_bodies: HashMap<F, &'e Expr<V, F>>,
    reachable_fns: HashSet<F>,
}

impl<'e, V: Clone, F: Clone + Eq + Hash> MarkAndSweep<'e, V, F> {
    fn mark(expr: &'e Expr<V, F>) -> Self {
        let mut mns = MarkAndSweep {
            function_bodies: Default::default(),
            reachable_fns: Default::default(),
        };
        mns.compute_for_expr(expr);
        mns
    }

    fn sweep(mut self, expr: &Expr<V, F>) -> Expr<V, F> {
        self.transform_expr(expr)
    }

    fn all_reachable(&self) -> bool {
        self.function_bodies
            .keys()
            .all(|f| self.reachable_fns.contains(f))
    }
}

impl<'e, V: Clone, F: Clone + Eq + Hash> Compute<'e, V, F> for MarkAndSweep<'e, V, F> {
    fn visit_expr(&mut self, expr: &'e Expr<V, F>) -> Computation {
        match expr {
            Expr::Fix(defs, cnt) => {
                for (f, _, b) in defs.iter() {
                    self.function_bodies.insert(f.clone(), b);
                }
                cnt.compute(self);
                Computation::Done
            }
            _ => Computation::Continue,
        }
    }

    fn visit_value(&mut self, value: &Value<V, F>) {
        if let Value::Label(f) = value {
            if self.reachable_fns.contains(f) {
                return;
            }
            self.reachable_fns.insert(f.clone());
            self.function_bodies[f].compute(self);
        }
    }

    fn post_visit_expr(&mut self, _: &'e Expr<V, F>) {}
}

impl<V: Clone, F: Clone + Eq + Hash + PartialEq> Transform<V, F> for MarkAndSweep<'_, V, F> {
    fn visit_expr(&mut self, expr: &Expr<V, F>) -> Transformed<Expr<V, F>> {
        match expr {
            Expr::Fix(defs, cnt) => {
                let mut defs_out = vec![];
                for (f, p, b) in defs.iter() {
                    if self.reachable_fns.contains(f) {
                        defs_out.push((f.clone(), *p, *b));
                    }
                }
                let cnt_out = cnt.transform(self);
                if defs_out.is_empty() {
                    Transformed::Done(cnt_out)
                } else {
                    Transformed::Done(Expr::Fix(Ref::array(defs_out), Ref::new(cnt_out)))
                }
            }
            _ => Transformed::Continue,
        }
    }

    fn visit_value(&mut self, _: &Value<V, F>) -> Transformed<Value<V, F>> {
        Transformed::Continue
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use map_macro::hash_set;

    #[test]
    fn dontmark_unreachable_function() {
        let x = Expr::from_str("(fix ((foo () (halt 0))) (halt 0))").unwrap();
        assert_eq!(MarkAndSweep::mark(&x).reachable_fns, hash_set![]);
    }

    #[test]
    fn mark_reachable_function() {
        let x = Expr::from_str("(fix ((foo () (halt 0))) ((@ foo)))").unwrap();
        assert_eq!(
            MarkAndSweep::mark(&x).reachable_fns,
            hash_set!["foo".into()]
        );
    }

    #[test]
    fn mark_indirectly_reachable_function() {
        let x = Expr::from_str("(fix ((bar () (halt 0)) (foo () ((@ bar)))) ((@ foo)))").unwrap();
        assert_eq!(
            MarkAndSweep::mark(&x).reachable_fns,
            hash_set!["foo".into(), "bar".into()]
        );
    }

    #[test]
    fn dontmark_unreachable_recursion() {
        let x = Expr::from_str("(fix ((foo () ((@ foo)))) (halt 0))").unwrap();
        assert_eq!(MarkAndSweep::mark(&x).reachable_fns, hash_set![]);

        let x = Expr::from_str("(fix ((foo () ((@ bar))) (bar () ((@ foo)))) (halt 0))").unwrap();
        assert_eq!(MarkAndSweep::mark(&x).reachable_fns, hash_set![]);
    }

    #[test]
    fn halt_on_reachable_recursion() {
        let x = Expr::from_str("(fix ((foo () ((@ foo)))) ((@ foo)))").unwrap();
        assert_eq!(
            MarkAndSweep::mark(&x).reachable_fns,
            hash_set!["foo".into()]
        );
    }

    #[test]
    fn remove_unmarked_functions() {
        let x = Expr::from_str("(fix ((foo () (halt 0)) (bar () (halt 0))) (halt 0))").unwrap();
        let y = Expr::from_str("(fix ((foo () (halt 0))) (halt 0))").unwrap();
        assert_eq!(
            MarkAndSweep {
                reachable_fns: hash_set!["foo".into()],
                function_bodies: Default::default()
            }
            .sweep(&x),
            y
        );
    }

    #[test]
    fn remove_empty_fixes() {
        let x = Expr::from_str("(fix ((foo () (halt 0))) (fix () (halt 0)))").unwrap();
        let y = Expr::from_str("(halt 0)").unwrap();
        assert_eq!(
            MarkAndSweep {
                reachable_fns: hash_set![],
                function_bodies: Default::default()
            }
            .sweep(&x),
            y
        );
    }
}
