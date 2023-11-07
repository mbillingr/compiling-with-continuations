use crate::core::clicker::Clicker;
use crate::languages::cps_lang::ast::{Expr, Transform, Transformed, Value};
use std::collections::HashMap;
use std::hash::Hash;

/// inline functions used only once. This will crash if there are unused (mutual) recursive functions!
pub fn beta_contraction<V: Clone + Eq + Hash + PartialEq>(
    expr: &Expr<V, V>,
    clicker: Clicker,
) -> Expr<V, V> {
    Inliner {
        inlineable_functions: expr
            .collect_all_functions()
            .into_iter()
            .filter(|(_, fninfo)| fninfo.n_app == 1)
            .map(|(f, fninfo)| (f, (fninfo.params.to_vec(), fninfo.body.clone())))
            .collect(),
        heuristic: AlwaysInline,
        recursive: true,
        depth: 0,
        clicker,
    }
    .transform_expr(expr)
}

/// inline functions contain only a single expression
pub fn inline_trivial_fns<V: Clone + Eq + Hash + PartialEq>(
    expr: &Expr<V, V>,
    clicker: Clicker,
) -> Expr<V, V> {
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
        heuristic: AlwaysInline,
        recursive: true,
        depth: 0,
        clicker,
    }
    .transform_expr(expr)
}

/// inline function calls based on heuristics
pub fn heuristic_inline<V: Clone + Eq + Hash + PartialEq>(
    expr: &Expr<V, V>,
    clicker: Clicker,
) -> Expr<V, V> {
    Inliner {
        inlineable_functions: expr
            .collect_all_functions()
            .into_iter()
            .map(|(f, fninfo)| (f, (fninfo.params.to_vec(), fninfo.body.clone())))
            .collect(),
        heuristic: InlineDecision {},
        recursive: false,
        depth: 0,
        clicker,
    }
    .transform_expr(expr)
}

struct Inliner<V: 'static, T: InlineHeuristic<V, V>> {
    inlineable_functions: HashMap<V, (Vec<V>, Expr<V, V>)>,
    heuristic: T,
    /// whether to inline inlined function bodies
    recursive: bool,
    depth: usize,
    clicker: Clicker,
}

impl<V: Clone + Eq + Hash + PartialEq, T: InlineHeuristic<V, V>> Transform<V, V> for Inliner<V, T> {
    fn autoclick(&mut self) {
        self.clicker.click()
    }

    fn visit_expr(&mut self, expr: &Expr<V, V>) -> Transformed<Expr<V, V>> {
        match expr {
            Expr::App(Value::Label(f), args) => match self.inlineable_functions.get(f) {
                Some((params, body)) if self.heuristic.calc(self.depth, args, params, body) => {
                    let mut new_body = body
                        .clone()
                        .substitute_vars(params.into_iter().cloned().zip(args.iter().cloned()));
                    if self.recursive {
                        self.depth += 1;
                        new_body = self.transform_expr(&new_body);
                        self.depth -= 1;
                    }
                    Transformed::Done(new_body)
                }
                _ => Transformed::Continue,
            },
            _ => Transformed::Continue,
        }
    }

    fn visit_value(&mut self, _: &Value<V, V>) -> Transformed<Value<V, V>> {
        Transformed::Continue
    }
}

trait InlineHeuristic<V, F> {
    fn calc(&self, depth: usize, args: &[Value<V, F>], params: &[V], body: &Expr<V, F>) -> bool;
}

impl<V, F, T: Fn(usize, &[Value<V, F>], &[V], &Expr<V, F>) -> bool> InlineHeuristic<V, F> for T {
    fn calc(&self, depth: usize, args: &[Value<V, F>], params: &[V], body: &Expr<V, F>) -> bool {
        self(depth, args, params, body)
    }
}

struct AlwaysInline;

impl<V, F> InlineHeuristic<V, F> for AlwaysInline {
    fn calc(&self, _: usize, _: &[Value<V, F>], _: &[V], _: &Expr<V, F>) -> bool {
        true
    }
}

struct InlineDecision {}

impl<V, F> InlineHeuristic<V, F> for InlineDecision {
    fn calc(&self, depth: usize, args: &[Value<V, F>], _params: &[V], body: &Expr<V, F>) -> bool {
        let const_args = args
            .iter()
            .filter(|a| match a {
                Value::Var(_) => false,
                _ => true,
            })
            .count();

        if const_args < args.len() {
            return false;
        }

        let const_arg_ratio = const_args as f64 / args.len() as f64;

        const INLINE_AGGRESSIVENESS: f64 = 100.0;

        body.size() as f64 + (1 + depth) as f64 / const_arg_ratio <= INLINE_AGGRESSIVENESS
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use map_macro::hash_map;

    pub fn inline<V: Clone + Eq + Hash + PartialEq>(
        expr: &Expr<V, V>,
        inlineable: HashMap<V, (Vec<V>, Expr<V, V>)>,
    ) -> Expr<V, V> {
        Inliner {
            inlineable_functions: inlineable,
            heuristic: AlwaysInline,
            recursive: true,
            depth: 0,
            clicker: Clicker::new(),
        }
        .transform_expr(expr)
    }

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
        assert_eq!(beta_contraction(&x, Default::default()), y);

        let x = Expr::from_str("(fix ((foo () (halt 0)) (bar () ((@ foo)))) ((@ bar)))").unwrap();
        let y = Expr::from_str("(fix ((foo () (halt 0)) (bar () (halt 0))) (halt 0))").unwrap();
        assert_eq!(beta_contraction(&x, Default::default()), y);
    }

    #[test]
    fn test_trivial_inlining() {
        let x = Expr::from_str("(fix ((foo () ((@ bar)))) ((@ foo)))").unwrap();
        let y = Expr::from_str("(fix ((foo () ((@ bar)))) ((@ bar)))").unwrap();
        assert_eq!(inline_trivial_fns(&x, Default::default()), y);

        let x = Expr::from_str("(fix ((foo () (halt 0))) ((@ foo)))").unwrap();
        let y = Expr::from_str("(fix ((foo () (halt 0))) (halt 0))").unwrap();
        assert_eq!(inline_trivial_fns(&x, Default::default()), y);

        let x = Expr::from_str("(fix ((foo () (panic \"\"))) ((@ foo)))").unwrap();
        let y = Expr::from_str("(fix ((foo () (panic \"\"))) (panic \"\"))").unwrap();
        assert_eq!(inline_trivial_fns(&x, Default::default()), y);
    }
}
