use crate::core::clicker::Clicker;
use crate::languages::cps_lang::ast::{Expr, Transform, Transformed, Value};
use std::collections::HashSet;
use std::hash::Hash;

pub fn eliminate_dead_code<V: Clone + Eq + Hash, F: Clone>(
    expr: &Expr<V, F>,
    clicker: Clicker,
) -> Expr<V, F> {
    Eliminator::new(clicker).transform_expr(expr)
}

struct Eliminator<V> {
    used_vars: HashSet<V>,
    clicker: Clicker,
}

impl<V: Eq + Hash> Eliminator<V> {
    fn new(clicker: Clicker) -> Self {
        Eliminator {
            clicker,
            used_vars: HashSet::new(),
        }
    }

    fn is_used(&self, var: &V) -> bool {
        self.used_vars.contains(var)
    }
}

impl<V: Clone + Eq + Hash, F: Clone> Transform<V, F> for Eliminator<V> {
    fn visit_expr(&mut self, expr: &Expr<V, F>) -> Transformed<Expr<V, F>> {
        self.used_vars
            .extend(expr.operand_vars().into_iter().cloned());

        let mut cnts: Vec<_> = expr
            .continuation_exprs()
            .into_iter()
            .map(|cnt| self.transform_expr(cnt))
            .collect();

        if cnts.len() == 1 {
            match expr {
                Expr::PrimOp(op, _, _, _) if op.has_side_effect() => {}
                _ => {
                    if !expr.bound_vars().is_empty() {
                        if !expr.bound_vars().into_iter().any(|v| self.is_used(v)) {
                            for v in expr.bound_vars() {
                                self.used_vars.remove(v);
                            }
                            self.clicker.click();
                            return Transformed::Done(cnts.pop().unwrap());
                        }
                    }
                }
            }
        }

        for v in expr.bound_vars() {
            self.used_vars.remove(v);
        }
        Transformed::Done(expr.replace_continuations(cnts))
    }

    fn visit_value(&mut self, _: &Value<V, F>) -> Transformed<Value<V, F>> {
        Transformed::Continue
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nothing_to_do() {
        let x = Expr::from_str("(record () r (halt r))").unwrap();
        assert_eq!(eliminate_dead_code(&x, Clicker::default()), x);

        let x = Expr::from_str("(primop + (1 2) (x) ((halt x)))").unwrap();
        assert_eq!(eliminate_dead_code(&x, Clicker::default()), x);
    }

    #[test]
    fn dont_eliminate_side_effect() {
        let x = Expr::from_str("(primop show-int (42) (x) ((halt 0)))").unwrap();
        assert_eq!(eliminate_dead_code(&x, Clicker::default()), x);
    }

    #[test]
    fn remove_unused_record() {
        let x = Expr::from_str("(record () r (halt 0))").unwrap();
        let y = Expr::from_str("(halt 0)").unwrap();
        assert_eq!(eliminate_dead_code(&x, Clicker::default()), y);
    }

    #[test]
    fn remove_unused_primop() {
        let x = Expr::from_str("(primop + (1 2) (x) ((halt 0)))").unwrap();
        let y = Expr::from_str("(halt 0)").unwrap();
        assert_eq!(eliminate_dead_code(&x, Clicker::default()), y);
    }

    #[test]
    fn detect_usage_inside_branch() {
        let x = Expr::from_str("(primop + (1 2) (x) ((switch 1 (halt 0) (halt 0))))").unwrap();
        let y = Expr::from_str("(switch 1 (halt 0) (halt 0))").unwrap();
        assert_eq!(eliminate_dead_code(&x, Clicker::default()), y);

        let x = Expr::from_str("(primop + (1 2) (x) ((switch 1 (halt x) (halt 0))))").unwrap();
        let y = Expr::from_str("(primop + (1 2) (x) ((switch 1 (halt x) (halt 0))))").unwrap();
        assert_eq!(eliminate_dead_code(&x, Clicker::default()), y);

        let x = Expr::from_str("(primop + (1 2) (x) ((switch 1 (halt 0) (halt x))))").unwrap();
        let y = Expr::from_str("(primop + (1 2) (x) ((switch 1 (halt 0) (halt x))))").unwrap();
        assert_eq!(eliminate_dead_code(&x, Clicker::default()), y);
    }

    #[test]
    fn shadowing() {
        let x = Expr::from_str("(record (1) r (record (2) r (halt r)))").unwrap();
        let y = Expr::from_str("(record (2) r (halt r))").unwrap();
        assert_eq!(eliminate_dead_code(&x, Clicker::default()), y);
    }

    #[test]
    fn later_use() {
        let x = Expr::from_str("(record (1) r1 (record (2) r2 (halt r1)))").unwrap();
        let y = Expr::from_str("(record (1) r1 (halt r1))").unwrap();
        assert_eq!(eliminate_dead_code(&x, Clicker::default()), y);
    }
}
