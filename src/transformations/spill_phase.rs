use crate::core::reference::Ref;
use crate::core::sets::Set;
use crate::languages::cps_lang::ast::{AccessPath, Expr, Transform, Transformed, Value};
use crate::set;
use crate::transformations::{GenSym, GensymContext};
use std::collections::{HashMap, VecDeque};
use std::hash::Hash;
use std::sync::Arc;

#[derive(Debug)]
pub struct Spill<V: Clone + Eq + Hash> {
    n_registers: usize,

    /// The results R bound by the immediately previous operator
    previous_result: Set<V>,

    /// The current spill record S
    current_spill_record: SpillRecord<V>,

    /// The uniquely bound variables U
    unspilled_vars: Set<V>,

    /// The duplicate variables D are still in registers and in the record
    duplicate_vars: Set<V>,

    gs: Arc<GensymContext>,
}

impl<V: Clone + Eq + Hash> Spill<V> {
    pub fn new(n_registers: usize, gs: Arc<GensymContext>) -> Self {
        Spill {
            n_registers,
            previous_result: set![],
            current_spill_record: SpillRecord::NoSpill,
            unspilled_vars: set![],
            duplicate_vars: set![],
            gs,
        }
    }

    pub fn new_context(n_registers: usize, gensym_delimiter: impl ToString) -> Self {
        Spill {
            n_registers,
            previous_result: set![],
            current_spill_record: SpillRecord::NoSpill,
            unspilled_vars: set![],
            duplicate_vars: set![],
            gs: Arc::new(GensymContext::new(gensym_delimiter)),
        }
    }
}

impl<V: Clone + Eq + Hash + Ord + GenSym + std::fmt::Debug> Transform<V> for Spill<V> {
    fn visit_expr(&mut self, expr: &Expr<V>) -> Transformed<Expr<V>> {
        Transformed::Done(self.transform_expr(expr))
    }

    fn visit_value(&mut self, _: &Value<V>) -> Transformed<Value<V>> {
        Transformed::Continue
    }

    fn transform_expr(&mut self, expr: &Expr<V>) -> Expr<V>
    where
        Self: Sized,
    {
        Self::transform_expr(self, expr)
    }
}

impl<V: Clone + Eq + Hash + Ord + GenSym + std::fmt::Debug> Spill<V> {
    pub fn spill_toplevel(&self, expr: &Expr<V>) -> Expr<V> {
        if let Expr::Fix(defs, cnt) = expr {
            todo!()
        } else {
            panic!("not a fixture")
        }
    }

    pub fn transform_expr(&self, expr: &Expr<V>) -> Expr<V> {
        if let Expr::Fix(_, _) = expr {
            panic!("Encountered fixture form during spill phase. Did you forget to do closure conversion and lambda lifting first?")
        }
        SpillStep::new(self, expr)
            .discard_duplicates()
            .build_expression()
    }
}

struct SpillStep<'a, V: 'static + Eq + Hash> {
    expr: &'a Expr<V>,
    n_registers: usize,
    previous_result: &'a Set<V>,
    unspilled_vars: &'a Set<V>,
    duplicate_vars: Set<V>,
    args: Set<V>,
    w: Set<V>,
    v_before: Set<V>,
    v_after: Set<V>,
    s_before: &'a SpillRecord<V>,
    s_after: SpillRecord<V>,

    gs: Arc<GensymContext>,
}

impl<'a, V: Eq + Hash + Clone + GenSym + Ord + std::fmt::Debug> SpillStep<'a, V> {
    fn new(spill: &'a Spill<V>, expr: &'a Expr<V>) -> Self {
        // todo: is this correct, or should we include a set item for every argument to the expr,
        //       even if it's not a variable?
        let args = Set::from(expr.operand_vars().into_iter().cloned().collect::<Vec<_>>());
        let w = Set::from(expr.bound_vars().into_iter().cloned().collect::<Vec<_>>());

        let v_before = Set::from(expr.free_vars());
        let v_after = expr
            .continuation_exprs()
            .into_iter()
            .map(Expr::free_vars)
            .map(Set::from)
            .fold(set![], |acc, fv| acc.union(&fv));

        let s_after = if spill.current_spill_record.is_still_useful(&v_after) {
            spill.current_spill_record.clone()
        } else {
            SpillRecord::NoSpill
        };

        SpillStep {
            expr,
            n_registers: spill.n_registers,
            previous_result: &spill.previous_result,
            unspilled_vars: &spill.unspilled_vars,
            duplicate_vars: spill.duplicate_vars.clone(),
            args,
            w,
            v_before,
            v_after,
            s_before: &spill.current_spill_record,
            s_after,
            gs: spill.gs.clone(),
        }
    }

    fn discard_duplicates(mut self) -> Self {
        let n_dup = self.n_registers
            - self.s_before.bound_var_as_set().len()
            - self
                .unspilled_vars
                .intersection(&self.v_before)
                .union(&self.previous_result)
                .len();

        if n_dup < self.duplicate_vars.len() {
            // discard most distantly used members of duplicate_vars
            let dups_to_drop = remove_n_next_used_vars_from(
                self.duplicate_vars.clone(),
                self.expr,
                self.duplicate_vars.len() - n_dup,
            );
            self.duplicate_vars = self.duplicate_vars.difference(&dups_to_drop);
        }

        self
    }

    fn build_expression(self) -> Expr<V> {
        if self.must_spill() {
            return self.make_spill_record();
        }

        let must_fetch = self
            .args
            .difference(&self.unspilled_vars.union(&self.duplicate_vars));
        match must_fetch.len() {
            0 => self.continue_without_fetch(),
            1 => {
                let new_spill_record = self.s_after.clone();
                let v = must_fetch.pop().unwrap();
                self.make_fetch(&v, new_spill_record)
            }
            _ => {
                let new_spill_record = self.s_before.clone();
                let v = must_fetch.pop().unwrap();
                self.make_fetch(&v, new_spill_record)
            }
        }
    }

    fn make_spill_record(self) -> Expr<V> {
        let sv: V = self.gs.gensym("spill");
        let currently_in_registers = self.unspilled_vars.union(&self.duplicate_vars);
        let (spill_fields, new_record) =
            self.s_before
                .build_new_record(self.v_before.clone(), &sv, &currently_in_registers);
        let new_state = Spill {
            n_registers: self.n_registers,
            previous_result: set![],
            unspilled_vars: set![],
            duplicate_vars: currently_in_registers.intersection(&self.v_before),
            current_spill_record: new_record,
            gs: self.gs.clone(),
        };
        let expr_ = new_state.transform_expr(self.expr);
        Expr::Record(Ref::array(spill_fields), sv, Ref::new(expr_))
    }

    fn continue_without_fetch(self) -> Expr<V> {
        // In contrast to the book, I add W to the unspilled vars. I think this is necessary to
        // actually populate the unspilled_vars field, where would they come from otherwise?
        let new_state = Spill {
            n_registers: self.n_registers,
            unspilled_vars: self
                .unspilled_vars
                .union(&self.w)
                .intersection(&self.v_after),
            previous_result: self.w,
            duplicate_vars: self.duplicate_vars,
            current_spill_record: self.s_after,
            gs: self.gs.clone(),
        };
        self.expr.replace_continuations(
            self.expr
                .continuation_exprs()
                .into_iter()
                .map(|c| new_state.transform_expr(c)),
        )
    }

    fn make_fetch(self, v: &V, new_spill_record: SpillRecord<V>) -> Expr<V> {
        let v_: V = self.gs.gensym(&v);
        let i = self.s_before.get_index(&v);
        let new_state = Spill {
            n_registers: self.n_registers,
            previous_result: set![],
            unspilled_vars: self.unspilled_vars.intersection(&self.v_before),
            duplicate_vars: self.duplicate_vars.add(v_.clone()),
            current_spill_record: new_spill_record.substitute(&v, v_.clone()),
            gs: self.gs.clone(),
        };
        let expr_ =
            new_state.transform_expr(&self.expr.substitute_var(&v, &Value::Var(v_.clone())));
        Expr::Select(
            i,
            Value::Var(
                self.s_before
                    .bound_var()
                    .expect("attempting fetch without spill record")
                    .clone(),
            ),
            v_,
            Ref::new(expr_),
        )
    }

    fn must_spill(&self) -> bool {
        let need_more_registers_for_arguments = self
            .args
            .union(&self.unspilled_vars.intersection(&self.v_after))
            .len()
            > self.n_registers - self.s_after.bound_var_as_set().len();

        let need_more_registers_for_results = self
            .w
            .union(&self.unspilled_vars.intersection(&self.v_after))
            .len()
            > self.n_registers - self.s_after.bound_var_as_set().len();

        need_more_registers_for_arguments | need_more_registers_for_results
    }
}

impl<V: Clone + Eq + Hash + Ord + GenSym + std::fmt::Debug> Spill<V> {
    pub fn with_unspilled(mut self, vars: Set<V>) -> Self {
        self.unspilled_vars = vars;
        self
    }
}

fn remove_n_next_used_vars_from<V: Eq + Hash + Clone>(
    mut vars: Set<V>,
    expr: &Expr<V>,
    n_to_remove: usize,
) -> Set<V> {
    // breath first traversal of the expression tree to find earliest uses of variables
    let mut exprs_to_visit = VecDeque::from(vec![expr]);
    while vars.len() > n_to_remove && !exprs_to_visit.is_empty() {
        let expr = exprs_to_visit.pop_front().unwrap();

        for var in expr.operand_vars() {
            vars = vars.remove(var);
            if vars.len() <= n_to_remove {
                return vars;
            }
        }

        for cnt in expr.continuation_exprs() {
            exprs_to_visit.push_back(cnt);
        }
    }
    vars
}

#[derive(Debug, Clone)]
pub enum SpillRecord<V: Eq + Hash> {
    NoSpill,
    Spilled {
        bound_var: V,
        contained_vars: Set<V>,
        indices: HashMap<V, isize>,
    },
}

impl<V: Eq + Hash + Clone + Ord + std::fmt::Debug> SpillRecord<V> {
    fn get_index(&self, v: &V) -> isize {
        if let SpillRecord::Spilled { indices, .. } = self {
            if let Some(idx) = indices.get(v) {
                return *idx;
            }
        }

        panic!("{v:?} not found in spill record")
    }

    fn is_still_useful(&self, used_vars: &Set<V>) -> bool {
        match self {
            SpillRecord::NoSpill => false,
            SpillRecord::Spilled { contained_vars, .. } => {
                !contained_vars.intersection(used_vars).is_empty()
            }
        }
    }

    fn substitute(self, old_var: &V, new_var: V) -> Self {
        match self {
            SpillRecord::NoSpill => self,
            SpillRecord::Spilled {
                bound_var,
                contained_vars,
                mut indices,
            } => {
                let idx = indices[old_var];
                indices.remove(old_var);
                indices.insert(new_var.clone(), idx);
                SpillRecord::Spilled {
                    bound_var,
                    contained_vars: contained_vars.remove(old_var).add(new_var),
                    indices,
                }
            }
        }
    }

    fn bound_var(&self) -> Option<&V> {
        match self {
            SpillRecord::NoSpill => None,
            SpillRecord::Spilled { bound_var, .. } => Some(bound_var),
        }
    }

    fn bound_var_as_set(&self) -> Set<V> {
        match self {
            SpillRecord::NoSpill => set![],
            SpillRecord::Spilled { bound_var, .. } => set![bound_var.clone()],
        }
    }

    fn build_new_record(
        &self,
        vars_to_spill: Set<V>,
        record_var: &V,
        currently_in_registers: &Set<V>,
    ) -> (Vec<(Value<V>, AccessPath)>, SpillRecord<V>) {
        let mut vars: Vec<_> = vars_to_spill.iter().cloned().collect();
        vars.sort_unstable();

        let indices = vars
            .iter()
            .enumerate()
            .map(|(i, v)| (v.clone(), i as isize))
            .collect();

        let new_record = SpillRecord::Spilled {
            bound_var: record_var.clone(),
            contained_vars: vars_to_spill,
            indices,
        };

        let spill_fields = vars
            .into_iter()
            .map(|v| {
                if currently_in_registers.contains(&v) {
                    (Value::Var(v), AccessPath::Ref(0))
                } else {
                    (
                        Value::Var(self.bound_var().unwrap().clone()),
                        AccessPath::Sel(self.get_index(&v), Ref::new(AccessPath::Ref(0))),
                    )
                }
            })
            .collect();

        (spill_fields, new_record)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::either::{either, Or};
    use map_macro::hash_map;

    #[test]
    fn expr_unchanged_if_nothing_to_spill() {
        let expr = Expr::from_str("(halt 0)").unwrap();
        assert_eq!(expr.transform(&mut Spill::new_context(5, "__")), expr);
    }

    #[test]
    fn no_spill_needed_because_variables_are_no_longer_used() {
        let expr =
            Expr::from_str("(primop + () (a b c d e) ((primop + () (f) ((halt a)))))").unwrap();
        assert_eq!(expr.transform(&mut Spill::new_context(5, "__")), expr);
    }

    #[test]
    fn no_spill_needed_because_vars_fit_exactly_in_registers() {
        let expr =
            Expr::from_str("(primop + () (a b c d) ((primop + () (e) ((a b c d e)))))").unwrap();
        assert_eq!(expr.transform(&mut Spill::new_context(5, "__")), expr);
    }

    #[test]
    fn spill_decision() {
        assert_eq!(
            SpillStep {
                expr: &Expr::Panic("dummy".into()),
                n_registers: 2,
                previous_result: &set![],
                unspilled_vars: &set!["x"],
                duplicate_vars: set![],
                args: set!["a"],
                w: set!["w"],
                v_before: set![],
                v_after: set!["x"],
                s_before: &SpillRecord::NoSpill,
                s_after: SpillRecord::NoSpill,
                gs: Arc::new(GensymContext::new("__"))
            }
            .must_spill(),
            false
        );

        // need all registers for args
        assert_eq!(
            SpillStep {
                expr: &Expr::Panic("dummy".into()),
                n_registers: 2,
                previous_result: &set![],
                unspilled_vars: &set!["x"],
                duplicate_vars: set![],
                args: set!["a", "b"],
                w: set!["w"],
                v_before: set![],
                v_after: set!["x"],
                s_before: &SpillRecord::NoSpill,
                s_after: SpillRecord::NoSpill,
                gs: Arc::new(GensymContext::new("__"))
            }
            .must_spill(),
            true
        );

        // need all registers for results
        assert_eq!(
            SpillStep {
                expr: &Expr::Panic("dummy".into()),
                n_registers: 2,
                previous_result: &set![],
                unspilled_vars: &set!["x"],
                duplicate_vars: set![],
                args: set!["a"],
                w: set!["v", "w"],
                v_before: set![],
                v_after: set!["x"],
                s_before: &SpillRecord::NoSpill,
                s_after: SpillRecord::NoSpill,
                gs: Arc::new(GensymContext::new("__"))
            }
            .must_spill(),
            true
        );

        // need to preserve existing values
        assert_eq!(
            SpillStep {
                expr: &Expr::Panic("dummy".into()),
                n_registers: 2,
                previous_result: &set![],
                unspilled_vars: &set!["x", "y"],
                duplicate_vars: set![],
                args: set!["a"],
                w: set!["w"],
                v_before: set![],
                v_after: set!["x", "y"],
                s_before: &SpillRecord::NoSpill,
                s_after: SpillRecord::NoSpill,
                gs: Arc::new(GensymContext::new("__"))
            }
            .must_spill(),
            true
        );

        // need to preserve spill record
        assert_eq!(
            SpillStep {
                expr: &Expr::Panic("dummy".into()),
                n_registers: 2,
                previous_result: &set![],
                unspilled_vars: &set!["x"],
                duplicate_vars: set![],
                args: set!["a"],
                w: set!["w"],
                v_before: set![],
                v_after: set!["x"],
                s_before: &SpillRecord::NoSpill,
                s_after: SpillRecord::Spilled {
                    bound_var: "s",
                    contained_vars: set![],
                    indices: Default::default(),
                },
                gs: Arc::new(GensymContext::new("__"))
            }
            .must_spill(),
            true
        );
    }

    #[test]
    fn must_spill() {
        let expr = Expr::from_str(
            "(primop ~ () (a m) (
            (select 0 a b 
              (select 1 a c 
                (select 2 a d 
                  (select 3 a e 
                    (select 4 a f 
                      (select 5 a g 
                        (primop + (b c) (h) (
                          (primop + (d e) (i) (
                            (primop + (f g) (j) (
                              (primop + (h i) (k) (
                                (primop + (k j) (l) (
                                  (m l)))))))))))))))))))",
        )
        .unwrap();
        let expect = Expr::from_str(
            "(primop ~ () (a m) (
            (select 0 a b 
              (select 1 a c 
                (select 2 a d
                  (record ((a (ref 0)) (b (ref 0)) (c (ref 0)) (d (ref 0)) (m (ref 0))) spill__0
                    (select 3 a e 
                      (select 4 a f 
                        (select 5 a g 
                          (record ((b (ref 0)) 
                                   (spill__0 (sel 2 (ref 0))) 
                                   (spill__0 (sel 3 (ref 0)))
                                   (e (ref 0)) (f (ref 0)) (g (ref 0)) 
                                   (spill__0 (sel 4 (ref 0)))) spill__1
                            (select 1 spill__1 c__2
                              (primop + (b c__2) (h) (
                                (select 2 spill__1 d__3
                                  (primop + (d__3 e) (i) (
                                    (select 5 spill__1 g__4
                                      (primop + (f g__4) (j) (
                                        (primop + (h i) (k) (
                                          (primop + (k j) (l) (
                                            (select 6 spill__1 m__5
                                              (m__5 l)))))))))))))))))))))))))",
        )
        .unwrap();
        assert_eq!(expr.transform(&mut Spill::new_context(5, "__")), expect);
    }

    #[test]
    fn last_fetch() {
        let spill = Spill {
            n_registers: 5,
            previous_result: set![],
            current_spill_record: SpillRecord::Spilled {
                bound_var: Ref::from("s"),
                contained_vars: set![Ref::from("f")],
                indices: hash_map![Ref::from("f") => 0],
            },
            unspilled_vars: set![],
            duplicate_vars: set![],
            gs: Arc::new(GensymContext::new("__")),
        };
        assert_eq!(
            spill.transform_expr(&Expr::from_str("(f)").unwrap()),
            Expr::from_str("(select 0 s f__0 (f__0))").unwrap()
        )
    }

    #[test]
    fn fetch_args_from_spill() {
        let spill = Spill {
            n_registers: 5,
            previous_result: set![],
            current_spill_record: SpillRecord::Spilled {
                bound_var: Ref::from("s"),
                contained_vars: set![Ref::from("f"), Ref::from("x")],
                indices: hash_map![Ref::from("f") => 0, Ref::from("x") => 1],
            },
            unspilled_vars: set![],
            duplicate_vars: set![],
            gs: Arc::new(GensymContext::new("__")),
        };
        assert_eq!(
            spill.transform_expr(&Expr::from_str("(f x)").unwrap()),
            either(Expr::from_str("(select 0 s f__0 (select 1 s x__1 (f__0 x__1)))").unwrap())
                .or(Expr::from_str("(select 1 s x__0 (select 0 s f__1 (f__1 x__0)))").unwrap())
        )
    }

    impl<V, A: PartialEq<Expr<V>>, B: PartialEq<Expr<V>>> PartialEq<Or<A, B>> for Expr<V> {
        fn eq(&self, other: &Or<A, B>) -> bool {
            other == self
        }
    }
}
