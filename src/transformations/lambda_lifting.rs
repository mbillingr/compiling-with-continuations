use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Transform, Transformed, Value};
use std::hash::Hash;

pub struct LambdaLifting<V: 'static> {
    functions: Vec<(V, Ref<[V]>, Ref<Expr<V>>)>,
}

pub fn lift_lambdas<V: Clone + Eq + Hash + std::fmt::Debug>(toplevel_expr: &Expr<V>) -> Expr<V> {
    let mut context = LambdaLifting {
        functions: Default::default(),
    };
    let expr = context.transform_expr(toplevel_expr);
    Expr::Fix(Ref::array(context.functions), Ref::new(expr))
}

impl<V: Clone + Eq + Hash + std::fmt::Debug> Transform<V> for LambdaLifting<V> {
    fn visit_expr(&mut self, expr: &Expr<V>) -> Transformed<Expr<V>> {
        match expr {
            Expr::Fix(defs, cnt) => {
                assert!(expr.fix_function_free_vars().is_empty());
                self.functions.extend(defs.iter().cloned());
                Transformed::Again((**cnt).clone())
            }
            _ => Transformed::Continue,
        }
    }

    fn visit_value(&mut self, value: &Value<V>) -> Transformed<Value<V>> {
        Transformed::Continue
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn top_level_fix_invariant() {
        let expr = Expr::from_str("(fix ((f (k) (k 1)) (g (k) (k 2))) (halt 0))").unwrap();
        assert_eq!(lift_lambdas(&expr), expr);
    }

    #[test]
    fn lift_fix_in_continuations() {
        let x = Expr::from_str(
            "(record () r
              (fix ((f (k) (k 1))) 
                (fix ((g (k) (k 2))) 
                  (halt 0))))",
        )
        .unwrap();
        let y = Expr::from_str(
            "(fix ((f (k) (k 1))
                   (g (k) (k 2))) 
               (record () r 
                 (halt 0)))",
        )
        .unwrap();
        assert_eq!(lift_lambdas(&x), y);
    }

    #[test]
    fn lift_fix_in_function_bodies() {
        let x = Expr::from_str(
            "(record () r
              (fix ((f (k) 
                      (fix ((g (k) (k 2))) 
                        (k 1))))                  
                (halt 0)))",
        )
        .unwrap();
        let y = Expr::from_str(
            "(fix ((f (k) (k 1))
                   (g (k) (k 2))) 
               (record () r 
                 (halt 0)))",
        )
        .unwrap();
        assert_eq!(lift_lambdas(&x), y);
    }
}
