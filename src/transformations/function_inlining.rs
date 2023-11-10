use crate::core::clicker::Clicker;
use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Transform, Transformed, Value};
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

/// inline functions used only once. This will crash if there are unused (mutual) recursive functions!
pub fn beta_contraction<V: Clone + Debug + Eq + Hash + PartialEq>(
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
        constant_values: Default::default(),
    }
    .transform_expr(expr)
}

/// inline functions contain only a single expression
pub fn inline_trivial_fns<V: Clone + Debug + Eq + Hash + PartialEq>(
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
        constant_values: Default::default(),
    }
    .transform_expr(expr)
}

/// inline function calls based on heuristics
pub fn heuristic_inline<V: Clone + Debug + Eq + Hash + PartialEq>(
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
        constant_values: Default::default(),
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
    constant_values: HashSet<V>,
}

impl<'e, V: Clone + Debug + Eq + Hash + PartialEq, T: InlineHeuristic<V, V>> Transform<V, V>
    for Inliner<V, T>
{
    fn visit_expr(&mut self, expr: &Expr<V, V>) -> Transformed<Expr<V, V>> {
        match expr {
            Expr::App(Value::Label(f), args) => match self.inlineable_functions.get(dbg!(f)) {
                Some((params, body))
                    if self.heuristic.calc(
                        self.depth,
                        args,
                        params,
                        body,
                        &self.constant_values,
                    ) =>
                {
                    let mut new_body = body
                        .clone()
                        .substitute_vars(params.into_iter().cloned().zip(args.iter().cloned()));
                    if self.recursive {
                        self.depth += 1;
                        new_body = self.transform_expr(&new_body);
                        self.depth -= 1;
                    }
                    self.clicker.click();
                    Transformed::Done(new_body)
                }
                _ => Transformed::Continue,
            },

            Expr::Record(_, v, _) => {
                self.constant_values.insert(v.clone());
                Transformed::Continue
            }

            Expr::Select(_, _, v, _) => {
                // in first approximation we don't know anything about the selected value
                self.constant_values.remove(v);
                Transformed::Continue
            }

            Expr::Offset(_, r, v, _) => {
                // offsetting a known record results in a known record
                if let Value::Var(r_) = r {
                    if self.constant_values.contains(r_) {
                        self.constant_values.insert(v.clone());
                    }
                }
                Transformed::Continue
            }

            Expr::Fix(defs, cnt) => {
                let original_constants = self.constant_values.clone();

                let mut defs_out = vec![];
                for (f, p, b) in defs.iter() {
                    self.constant_values = original_constants.clone();
                    for p_ in p.iter() {
                        // we don't know anything about function arguments
                        self.constant_values.remove(p_);
                    }
                    defs_out.push((f.clone(), *p, Ref::new(self.transform_expr(b))))
                }

                self.constant_values = original_constants;
                Transformed::Done(Expr::Fix(
                    Ref::array(defs_out),
                    self.transform_expr(cnt).into(),
                ))
            }

            Expr::PrimOp(_, args, res, _) => {
                // conservatively assume the result is known if all the results are known
                // (this does not detect 0*x, for example)
                if args.iter().all(|a| match a {
                    Value::Var(v) => self.constant_values.contains(v),
                    _ => true,
                }) {
                    self.constant_values.extend(res.iter().cloned())
                }
                Transformed::Continue
            }

            _ => Transformed::Continue,
        }
    }

    fn visit_value(&mut self, _: &Value<V, V>) -> Transformed<Value<V, V>> {
        Transformed::Continue
    }
}

trait InlineHeuristic<V, F> {
    fn calc(
        &self,
        depth: usize,
        args: &[Value<V, F>],
        params: &[V],
        body: &Expr<V, F>,
        known_vars: &HashSet<V>,
    ) -> bool;
}

struct AlwaysInline;

impl<V, F> InlineHeuristic<V, F> for AlwaysInline {
    fn calc(&self, _: usize, _: &[Value<V, F>], _: &[V], _: &Expr<V, F>, _: &HashSet<V>) -> bool {
        true
    }
}

struct InlineDecision {}

impl<V: Clone + Eq + Hash, F> InlineHeuristic<V, F> for InlineDecision {
    fn calc(
        &self,
        _depth: usize,
        args: &[Value<V, F>],
        params: &[V],
        body: &Expr<V, F>,
        known_vars: &HashSet<V>,
    ) -> bool {
        // always inline very small functions
        if body.size() < 5 {
            return true;
        }

        let mut known_vars = known_vars.clone();

        for (a, p) in args.iter().zip(params) {
            if let Value::Var(v) = a {
                if known_vars.contains(v) {
                    known_vars.insert(p.clone());
                }
            } else {
                known_vars.insert(p.clone());
            }
        }

        let s = estimate_savings(body, &known_vars);

        println!("{s}");

        s > 5
    }
}

fn estimate_cost<V, F>(expr: &Expr<V, F>) -> usize {
    // I'm following the book's estimate of the approximate number of machine code instructions.
    // This will likely require some fine tuning. Maybe it's possible to empirically determine
    // these costs?
    match expr {
        Expr::Record(v, _, cnt) => v.len() + 2 + estimate_cost(cnt),
        Expr::Select(_, _, _, cnt) => 1 + estimate_cost(cnt),
        Expr::Offset(_, _, _, cnt) => 1 + estimate_cost(cnt),
        Expr::App(_, args) => 1 + args.len(),
        Expr::Fix(defs, cnt) => {
            defs.iter()
                .map(|(_, _, b)| estimate_cost(b) + 1)
                .sum::<usize>()
                + estimate_cost(cnt)
        }
        Expr::Switch(_, cnts) => {
            4 + cnts
                .iter()
                .map(|cnt| estimate_cost(cnt))
                .map(|c| c + 1usize)
                .sum::<usize>()
        }
        Expr::PrimOp(_, args, rs, cnts) => {
            args.len() + rs.len() + cnts.iter().map(|cnt| estimate_cost(cnt)).sum::<usize>()
        }
        Expr::Halt(_) => 2,
        Expr::Panic(_) => 1,
    }
}

fn estimate_savings<V: Eq + Hash, F>(expr: &Expr<V, F>, known_vars: &HashSet<V>) -> usize {
    match expr {
        Expr::Record(_, _, cnt) => estimate_savings(cnt, known_vars),
        Expr::Select(_, v, _, cnt) => {
            (if let Value::Var(v_) = v {
                if known_vars.contains(v_) {
                    1
                } else {
                    0
                }
            } else {
                0
            }) + estimate_savings(cnt, known_vars)
        }
        Expr::Offset(_, _, _, cnt) => estimate_savings(cnt, known_vars),
        Expr::App(_, _) => 1,
        Expr::Fix(_, cnt) => estimate_savings(cnt, known_vars),
        Expr::Switch(k, cnts) => {
            if let Value::Var(k_) = k {
                if !known_vars.contains(k_) {
                    return cnts.iter().map(|c| estimate_savings(c, known_vars)).sum();
                }
            }
            let n = cnts.len() as f64;
            (estimate_cost(expr) as f64 * (n - 1.0) / n).round() as usize
        }

        // non-branching
        Expr::PrimOp(_, _, _, Ref([cnt])) => 1 + estimate_savings(cnt, known_vars),

        // branching
        Expr::PrimOp(_, args, _, cnts) => {
            let n_known = args
                .iter()
                .filter(|a| {
                    if let Value::Var(a_) = a {
                        known_vars.contains(a_)
                    } else {
                        true
                    }
                })
                .count() as f64
                / args.len() as f64;
            let n = cnts.len() as f64;
            (estimate_cost(expr) as f64 * n_known * (n - 1.0) / n) as usize
        }

        Expr::Halt(_) => 0,
        Expr::Panic(_) => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use map_macro::hash_map;

    pub fn inline<V: Clone + Debug + Eq + Hash + PartialEq>(
        expr: &Expr<V, V>,
        inlineable: HashMap<V, (Vec<V>, Expr<V, V>)>,
    ) -> Expr<V, V> {
        Inliner {
            inlineable_functions: inlineable,
            heuristic: AlwaysInline,
            recursive: true,
            depth: 0,
            clicker: Clicker::new(),
            constant_values: Default::default(),
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
