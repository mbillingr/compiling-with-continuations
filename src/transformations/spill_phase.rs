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
    current_spill_record: Option<SpillRecord<V>>,

    /// The uniquely bound variables U
    unspilled_vars: Set<V>,

    /// The duplicate variables D are still in registers and in the record
    duplicate_vars: Set<V>,

    gs: Arc<GensymContext>,
}

#[derive(Debug, Clone)]
pub struct SpillRecord<V: Eq + Hash> {
    bound_var: V,
    contained_vars: Set<V>,
    indices: HashMap<V, isize>,
}

impl<V: Clone + Eq + Hash> Spill<V> {
    pub fn new(n_registers: usize, gs: Arc<GensymContext>) -> Self {
        Spill {
            n_registers,
            previous_result: set![],
            current_spill_record: None,
            unspilled_vars: set![],
            duplicate_vars: set![],
            gs,
        }
    }

    pub fn new_context(n_registers: usize, gensym_delimiter: impl ToString) -> Self {
        Spill {
            n_registers,
            previous_result: set![],
            current_spill_record: None,
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

        /* the first assertion here does not know if a spill will actually be needed, and falsely
           fail in some edge cases.
        if self.current_spill_record.is_none() {
            // need to reserve one register for the spill record
            assert!(self.duplicate_vars.len() + self.unspilled_vars.len() < self.n_registers);
        } else {
            assert!(self.duplicate_vars.len() + self.unspilled_vars.len() <= self.n_registers);
        }*/

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

        println!("v_after = {:?}", v_after);

        let s_before = if let Some(SpillRecord { bound_var, .. }) = &self.current_spill_record {
            set![bound_var.clone()]
        } else {
            set![]
        };

        let spill_record_still_useful = self
            .current_spill_record
            .as_ref()
            .map(|s| s.contained_vars.intersection(&v_after))
            .map(|used_fields| !used_fields.is_empty())
            .unwrap_or(false);

        let (sv_after, sc_after, si_after) = if spill_record_still_useful {
            let s = self.current_spill_record.clone().unwrap();
            (Some(s.bound_var), s.contained_vars, s.indices)
        } else {
            (None, set![], Default::default())
        };

        let n_dup = self.n_registers
            - s_before.len()
            - self
                .unspilled_vars
                .intersection(&v_before)
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
            // is it enough to compute new_dups, or is there something we need to do?
            self.duplicate_vars.difference(&dups_to_drop)
        } else {
            self.duplicate_vars.clone()
        };

        if self.must_spill(&args, &w, &v_after, &sv_after) {
            let sv: V = self.gs.gensym("spill");
            let currently_in_registers = self.unspilled_vars.union(&new_dups);
            let (spill_fields, new_record) =
                self.build_spill_record(v_before.clone(), &sv, &currently_in_registers);
            let mut new_state = Spill {
                n_registers: self.n_registers,
                previous_result: set![],
                unspilled_vars: set![],
                duplicate_vars: currently_in_registers.intersection(&v_before),
                current_spill_record: Some(new_record),
                gs: self.gs.clone(),
            };
            let expr_ = new_state.transform_expr(expr);
            let spill_record = Expr::Record(Ref::array(spill_fields), sv, Ref::new(expr_));
            Transformed::Done(spill_record)
        } else {
            let must_fetch = args.difference(&self.unspilled_vars.union(&new_dups));
            // In contrast to the book, I add W to the unspilled vars.
            match must_fetch.len() {
                0 => {
                    let mut new_state = Spill {
                        n_registers: self.n_registers,
                        unspilled_vars: self.unspilled_vars.union(&w).intersection(&v_after),
                        previous_result: w,
                        duplicate_vars: new_dups,
                        current_spill_record: sv_after.map(|bound_var| SpillRecord {
                            bound_var,
                            contained_vars: sc_after,
                            indices: si_after,
                        }),
                        gs: self.gs.clone(),
                    };
                    Transformed::Done(
                        expr.replace_continuations(
                            expr.continuation_exprs()
                                .into_iter()
                                .map(|c| new_state.transform_expr(c)),
                        ),
                    )
                }
                1 => {
                    let s = self.current_spill_record.as_ref().unwrap();
                    let v = must_fetch.get_singleton().unwrap();
                    let v_: V = self.gs.gensym(&v);
                    let i = s.get_index(&v);
                    let mut new_state = Spill {
                        n_registers: self.n_registers,
                        previous_result: set![],
                        unspilled_vars: self.unspilled_vars.intersection(&v_before),
                        duplicate_vars: new_dups.add(v_.clone()),
                        current_spill_record: sv_after.map(|bound_var| SpillRecord {
                            bound_var,
                            contained_vars: sc_after,
                            indices: si_after,
                        }),
                        gs: self.gs.clone(),
                    };
                    let expr_ =
                        new_state.transform_expr(&expr.substitute_var(&v, &Value::Var(v_.clone())));
                    let select_expr =
                        Expr::Select(i, Value::Var(s.bound_var.clone()), v_, Ref::new(expr_));
                    Transformed::Done(select_expr)
                }
                _ => Transformed::Continue, // this is wrong. todo!("fetch variables from spill"),
            }
        }
    }

    fn visit_value(&mut self, _value: &Value<V>) -> Transformed<Value<V>> {
        Transformed::Continue
    }
}

impl<V: Clone + Eq + Hash + Ord + GenSym + std::fmt::Debug> Spill<V> {
    pub fn with_unspilled(mut self, vars: Set<V>) -> Self {
        self.unspilled_vars = vars;
        self
    }

    fn must_spill(
        &self,
        args: &Set<V>,
        w: &Set<V>,
        v_after: &Set<V>,
        sv_after: &Option<V>,
    ) -> bool {
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
            > self.n_registers - len(&sv_after);

        let need_more_registers_for_results =
            w.union(&self.unspilled_vars.intersection(&v_after)).len()
                > self.n_registers - len(&sv_after);

        need_more_registers_for_arguments | need_more_registers_for_results
    }

    fn build_spill_record(
        &mut self,
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

        let new_record = SpillRecord {
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
                    let s = spill.as_ref().unwrap();
                    (
                        Value::Var(s.bound_var.clone()),
                        AccessPath::Sel(s.get_index(&v), Ref::new(AccessPath::Ref(0))),
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

fn len<T>(opt: &Option<T>) -> usize {
    match opt {
        None => 0,
        Some(_) => 1,
    }
}

fn get<V: Eq + Hash + Clone + Ord>(
    vars: &Set<V>,
    in_register: &Set<V>,
    spill: &Option<SpillRecord<V>>,
) -> Vec<(Value<V>, AccessPath)> {
    let mut vars: Vec<_> = vars.iter().cloned().collect();
    vars.sort_unstable();
    vars.into_iter()
        .map(|v| {
            if in_register.contains(&v) {
                (Value::Var(v), AccessPath::Ref(0))
            } else {
                let s = spill.as_ref().unwrap();
                (
                    Value::Var(s.bound_var.clone()),
                    AccessPath::Sel(s.get_index(&v), Ref::new(AccessPath::Ref(0))),
                )
            }
        })
        .collect()
}

impl<V: Eq + Hash> SpillRecord<V> {
    fn get_index(&self, v: &V) -> isize {
        *self.indices.get(v).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
                .must_spill(&set!["a"], &set!["w"], &set!["x"], &None),
            false
        );

        // need all registers for args
        assert_eq!(
            Spill::new_context(2, "__")
                .with_unspilled(set!["x"])
                .must_spill(&set!["a", "b"], &set!["w"], &set!["x"], &None),
            true
        );

        // need all registers for results
        assert_eq!(
            Spill::new_context(2, "__")
                .with_unspilled(set!["x"])
                .must_spill(&set!["a"], &set!["v", "w"], &set!["x"], &None),
            true
        );

        // need to preserve existing values
        assert_eq!(
            Spill::new_context(2, "__")
                .with_unspilled(set!["x", "y"])
                .must_spill(&set!["a"], &set!["v"], &set!["x", "y"], &None),
            true
        );

        // need to preserve spill record
        assert_eq!(
            Spill::new_context(2, "__")
                .with_unspilled(set!["x"])
                .must_spill(&set!["a"], &set!["v"], &set!["x"], &Some("s")),
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
}
