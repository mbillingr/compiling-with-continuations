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
                for (f, p, b) in defs.iter() {
                    let fv = Expr::function_free_vars(p, b);
                    if !fv.is_empty() {
                        panic!("function can't lift {f:?} because it has free variables. {fv:?}")
                    }
                }
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
