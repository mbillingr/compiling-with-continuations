use crate::languages::cps_lang::ast::{Expr, Transform, Transformed, Value};
use std::collections::HashMap;
use std::hash::Hash;

/// inline functions used only once. This will crash if there are unused (mutual) recursive functions!
pub fn beta_contraction<V: Clone + Eq + Hash + PartialEq>(expr: &Expr<V, V>) -> Expr<V, V> {
    Inliner {
        inlineable_functions: inline_candidate_bodies(
            expr.collect_all_functions()
                .into_iter()
                .filter(|(_, fninfo)| fninfo.n_app == 1)
                .map(|(f, fninfo)| (f, (fninfo.params.to_vec(), fninfo.body.clone())))
                .collect(),
        ),
    }
    .transform_expr(expr)
}

/// inline functions contain only a single expression
pub fn inline_trivial_fns<V: Clone + Eq + Hash + PartialEq>(expr: &Expr<V, V>) -> Expr<V, V> {
    Inliner {
        inlineable_functions: expr
            .collect_all_functions()
            .into_iter()
            .filter(|(_, fninfo)| match fninfo.body {
                Expr::App(_, _) | Expr::Halt(_) | Expr::Panic(_) => true,
                _ => false,
            })
            .map(|(f, fninfo)| (f, (fninfo.params.to_vec(), fninfo.body.clone())))
            .collect(),
    }
    .transform_expr(expr)
}

pub fn inline<V: Clone + Eq + Hash + PartialEq>(
    expr: &Expr<V, V>,
    inlineable: HashMap<V, (Vec<V>, Expr<V, V>)>,
) -> Expr<V, V> {
    Inliner {
        inlineable_functions: inlineable,
    }
    .transform_expr(expr)
}

/// Don't call this with any kind of recursive functions!
pub fn inline_candidate_bodies<V: Clone + Eq + Hash + PartialEq>(
    mut funcs: HashMap<V, (Vec<V>, Expr<V, V>)>,
) -> HashMap<V, (Vec<V>, Expr<V, V>)> {
    loop {
        let before = funcs.clone();
        funcs = funcs
            .into_iter()
            .map(|(f, (p, b))| (f, (p, inline(&b, before.clone()))))
            .collect();
        if funcs == before {
            return funcs;
        }
    }
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

    #[test]
    fn test_beta_contraction() {
        let x = Expr::from_str("(fix ((foo () (halt 0))) ((@ foo)))").unwrap();
        let y = Expr::from_str("(fix ((foo () (halt 0))) (halt 0))").unwrap();
        assert_eq!(beta_contraction(&x), y);

        let x = Expr::from_str("(fix ((foo () (halt 0)) (bar () ((@ foo)))) ((@ bar)))").unwrap();
        let y = Expr::from_str("(fix ((foo () (halt 0)) (bar () (halt 0))) (halt 0))").unwrap();
        assert_eq!(beta_contraction(&x), y);
    }

    #[test]
    fn test_trivial_inlining() {
        let x = Expr::from_str("(fix ((foo () ((@ bar)))) ((@ foo)))").unwrap();
        let y = Expr::from_str("(fix ((foo () ((@ bar)))) ((@ bar)))").unwrap();
        assert_eq!(inline_trivial_fns(&x), y);

        let x = Expr::from_str("(fix ((foo () (halt 0))) ((@ foo)))").unwrap();
        let y = Expr::from_str("(fix ((foo () (halt 0))) (halt 0))").unwrap();
        assert_eq!(inline_trivial_fns(&x), y);

        let x = Expr::from_str("(fix ((foo () (panic \"\"))) ((@ foo)))").unwrap();
        let y = Expr::from_str("(fix ((foo () (panic \"\"))) (panic \"\"))").unwrap();
        assert_eq!(inline_trivial_fns(&x), y);
    }
}
