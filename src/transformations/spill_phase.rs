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
        println!("entering {:?}", expr);
        println!("{:?}", self);

        let step = SpillStep::new(self, expr);

        /*let (sv_after, sc_after, si_after) = if step.is_spill_record_still_useful() {
            let s = self.current_spill_record.clone().unwrap();
            (Some(s.bound_var), s.contained_vars, s.indices)
        } else {
            (None, set![], Default::default())
        };*/

        let s_after = if step.is_spill_record_still_useful() {
            self.current_spill_record.clone()
        } else {
            SpillRecord::NoSpill
        };

        let n_dup = self.n_registers
            - step.s_before.len()
            - self
                .unspilled_vars
                .intersection(&step.v_before)
                .union(&self.previous_result)
                .len();

        let new_dups = if n_dup < self.duplicate_vars.len() {
            // discard most distantly used members of duplicate_vars
            let dups_to_drop = remove_n_next_used_vars_from(
                self.duplicate_vars.clone(),
                expr,
                self.duplicate_vars.len() - n_dup,
            );
            println!("dropping dups: {:?}", dups_to_drop);
            self.duplicate_vars.difference(&dups_to_drop)
        } else {
            self.duplicate_vars.clone()
        };

        let new_expr = if self.must_spill(
            &step.args,
            &step.w,
            &step.v_after,
            &s_after.bound_var_as_set(),
        ) {
            let sv: V = self.gs.gensym("spill");
            let currently_in_registers = self.unspilled_vars.union(&new_dups);
            let (spill_fields, new_record) =
                self.build_spill_record(step.v_before.clone(), &sv, &currently_in_registers);
            let mut new_state = Spill {
                n_registers: self.n_registers,
                previous_result: set![],
                unspilled_vars: set![],
                duplicate_vars: currently_in_registers.intersection(&step.v_before),
                current_spill_record: new_record,
                gs: self.gs.clone(),
            };
            let expr_ = new_state.transform_expr(expr);
            Expr::Record(Ref::array(spill_fields), sv, Ref::new(expr_))
        } else {
            let must_fetch = step.args.difference(&self.unspilled_vars.union(&new_dups));
            match must_fetch.len() {
                0 => {
                    // no fetch needed.
                    // In contrast to the book, I add W to the unspilled vars.
                    let mut new_state = Spill {
                        n_registers: self.n_registers,
                        unspilled_vars: self
                            .unspilled_vars
                            .union(&step.w)
                            .intersection(&step.v_after),
                        previous_result: step.w,
                        duplicate_vars: new_dups,
                        current_spill_record: s_after,
                        gs: self.gs.clone(),
                    };
                    expr.replace_continuations(
                        expr.continuation_exprs()
                            .into_iter()
                            .map(|c| new_state.transform_expr(c)),
                    )
                }

                f => {
                    let s = &self.current_spill_record;
                    let v = must_fetch.pop().unwrap();
                    let v_: V = self.gs.gensym(&v);
                    let i = s.get_index(&v);
                    let new_spill_record = if f == 1 {
                        // discard spill record if this is the last fetch from it
                        s_after
                    } else {
                        self.current_spill_record.clone()
                    };
                    let mut new_state = Spill {
                        n_registers: self.n_registers,
                        previous_result: set![],
                        unspilled_vars: self.unspilled_vars.intersection(&step.v_before),
                        duplicate_vars: new_dups.add(v_.clone()),
                        current_spill_record: new_spill_record.substitute(&v, v_.clone()),
                        gs: self.gs.clone(),
                    };
                    let expr_ =
                        new_state.transform_expr(&expr.substitute_var(&v, &Value::Var(v_.clone())));
                    Expr::Select(
                        i,
                        Value::Var(
                            s.bound_var()
                                .expect("attempting fetch without spill record")
                                .clone(),
                        ),
                        v_,
                        Ref::new(expr_),
                    )
                }
            }
        };
        Transformed::Done(new_expr)
    }

    fn visit_value(&mut self, _value: &Value<V>) -> Transformed<Value<V>> {
        Transformed::Continue
    }
}

struct SpillStep<'a, V: Eq + Hash> {
    args: Set<V>,
    w: Set<V>,
    v_before: Set<V>,
    v_after: Set<V>,
    s_before: Set<V>,
    current_spill_record: &'a SpillRecord<V>,
}

impl<'a, V: Eq + Hash + Clone + std::fmt::Debug> SpillStep<'a, V> {
    fn new(spill: &'a Spill<V>, expr: &Expr<V>) -> Self {
        // todo: is this correct, or should we include a set item for every argument to the expr,
        //       even if it's not a variable?
        let args = Set::from(expr.operand_vars().into_iter().cloned().collect::<Vec<_>>());
        let w = Set::from(expr.bound_vars().into_iter().cloned().collect::<Vec<_>>());

        let v_before: Set<V> = expr.free_vars().into();
        let v_after = expr
            .continuation_exprs()
            .into_iter()
            .map(Expr::free_vars)
            .map(Set::from)
            .fold(set![], |acc, fv| acc.union(&fv));

        let s_before = if let SpillRecord::Spilled { bound_var, .. } = &spill.current_spill_record {
            set![bound_var.clone()]
        } else {
            set![]
        };

        SpillStep {
            args,
            w,
            v_before,
            v_after,
            s_before,
            current_spill_record: &spill.current_spill_record,
        }
    }

    fn is_spill_record_still_useful(&self) -> bool {
        self.current_spill_record
            .spilled_vars()
            .map(|vars| vars.intersection(&self.v_after))
            .map(|used_fields| !used_fields.is_empty())
            .unwrap_or(false)
    }
}

impl<V: Clone + Eq + Hash + Ord + GenSym + std::fmt::Debug> Spill<V> {
    pub fn with_unspilled(mut self, vars: Set<V>) -> Self {
        self.unspilled_vars = vars;
        self
    }

    fn must_spill(&self, args: &Set<V>, w: &Set<V>, v_after: &Set<V>, sv_after: &Set<V>) -> bool {
        println!(
            "A: {:?}",
            args.union(&self.unspilled_vars.intersection(&v_after))
        );

        println!(
            "B: {:?}",
            w.union(&self.unspilled_vars.intersection(&v_after))
        );

        let need_more_registers_for_arguments = args
            .union(&self.unspilled_vars.intersection(&v_after))
            .len()
            > self.n_registers - sv_after.len();

        let need_more_registers_for_results =
            w.union(&self.unspilled_vars.intersection(&v_after)).len()
                > self.n_registers - sv_after.len();

        need_more_registers_for_arguments | need_more_registers_for_results
    }

    fn build_spill_record(
        &self,
        v_before: Set<V>,
        sv: &V,
        currently_in_registers: &Set<V>,
    ) -> (Vec<(Value<V>, AccessPath)>, SpillRecord<V>) {
        let spill = &self.current_spill_record;

        let mut vars: Vec<_> = v_before.iter().cloned().collect();
        vars.sort_unstable();

        let indices = vars
            .iter()
            .enumerate()
            .map(|(i, v)| (v.clone(), i as isize))
            .collect();

        let new_record = SpillRecord::Spilled {
            bound_var: sv.clone(),
            contained_vars: v_before,
            indices,
        };

        let spill_fields = vars
            .into_iter()
            .map(|v| {
                if currently_in_registers.contains(&v) {
                    (Value::Var(v), AccessPath::Ref(0))
                } else {
                    (
                        Value::Var(spill.bound_var().unwrap().clone()),
                        AccessPath::Sel(spill.get_index(&v), Ref::new(AccessPath::Ref(0))),
                    )
                }
            })
            .collect();

        (spill_fields, new_record)
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

impl<V: Eq + Hash + Clone + std::fmt::Debug> SpillRecord<V> {
    fn get_index(&self, v: &V) -> isize {
        if let SpillRecord::Spilled { indices, .. } = self {
            if let Some(idx) = indices.get(v) {
                return *idx;
            }
        }

        panic!("{v:?} not found in spill record")
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

    fn spilled_vars(&self) -> Option<&Set<V>> {
        match self {
            SpillRecord::NoSpill => None,
            SpillRecord::Spilled { contained_vars, .. } => Some(contained_vars),
        }
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
            Spill::new_context(2, "__")
                .with_unspilled(set!["x"])
                .must_spill(&set!["a"], &set!["w"], &set!["x"], &set![]),
            false
        );

        // need all registers for args
        assert_eq!(
            Spill::new_context(2, "__")
                .with_unspilled(set!["x"])
                .must_spill(&set!["a", "b"], &set!["w"], &set!["x"], &set![]),
            true
        );

        // need all registers for results
        assert_eq!(
            Spill::new_context(2, "__")
                .with_unspilled(set!["x"])
                .must_spill(&set!["a"], &set!["v", "w"], &set!["x"], &set![]),
            true
        );

        // need to preserve existing values
        assert_eq!(
            Spill::new_context(2, "__")
                .with_unspilled(set!["x", "y"])
                .must_spill(&set!["a"], &set!["v"], &set!["x", "y"], &set![]),
            true
        );

        // need to preserve spill record
        assert_eq!(
            Spill::new_context(2, "__")
                .with_unspilled(set!["x"])
                .must_spill(&set!["a"], &set!["v"], &set!["x"], &set!["s"]),
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
        let mut spill = Spill {
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
        let mut spill = Spill {
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
