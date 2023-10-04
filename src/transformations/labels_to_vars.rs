use crate::languages::cps_lang::ast::{Expr, Transform, Transformed, Value};

pub struct LabelsToVars;

impl<V: Clone + PartialEq> Transform<V> for LabelsToVars {
    fn visit_expr(&mut self, _: &Expr<V>) -> Transformed<Expr<V>> {
        Transformed::Continue
    }

    fn visit_value(&mut self, value: &Value<V>) -> Transformed<Value<V>> {
        match value {
            Value::Label(v) => Transformed::Done(Value::Var(v.clone())),
            _ => Transformed::Continue,
        }
    }
}
