use crate::languages::cps_lang::ast::{Expr, Transform, Transformed, Value};
use std::collections::HashMap;
use std::hash::Hash;

pub fn inline<V: Clone + Eq + Hash + PartialEq>(
    expr: &Expr<V, V>,
    inlineable: HashMap<V, (Vec<V>, Expr<V, V>)>,
) -> Expr<V, V> {
    Inliner {
        inlineable_functions: inlineable,
    }
    .transform_expr(expr)
}

struct Inliner<V: 'static> {
    inlineable_functions: HashMap<V, (Vec<V>, Expr<V, V>)>,
}

impl<V: Clone + Eq + Hash + PartialEq> Transform<V, V> for Inliner<V> {
    fn visit_expr(&mut self, expr: &Expr<V, V>) -> Transformed<Expr<V, V>> {
        match expr {
            Expr::App(Value::Label(f), args) => match self.inlineable_functions.get(f) {
                None => Transformed::Continue,
                Some((params, body)) => Transformed::Done(
                    body.clone()
                        .substitute_vars(params.into_iter().cloned().zip(args.iter().cloned())),
                ),
            },
            _ => Transformed::Continue,
        }
    }

    fn visit_value(&mut self, _: &Value<V, V>) -> Transformed<Value<V, V>> {
        Transformed::Continue
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use map_macro::hash_map;

    #[test]
    fn do_not_inline() {
        let x = Expr::from_str("((@ foo))").unwrap();

        assert_eq!(inline(&x, Default::default()), x);
    }

    #[test]
    fn do_inline() {
        let x = Expr::from_str("((@ foo))").unwrap();
        let y = Expr::from_str("(halt 0)").unwrap();
        assert_eq!(
            inline(
                &x,
                hash_map!["foo".into() => (vec![], Expr::from_str("(halt 0)").unwrap())]
            ),
            y
        );
    }

    #[test]
    fn substitute_params() {
        let x = Expr::from_str("((@ foo) 42 (@ bar))").unwrap();
        let y = Expr::from_str("((@ bar) 42)").unwrap();
        assert_eq!(
            inline(
                &x,
                hash_map![
                    "foo".into() => (
                        vec!["x".into(), "y".into()],
                        Expr::from_str("(y x)").unwrap())]
            ),
            y
        );
    }
}
