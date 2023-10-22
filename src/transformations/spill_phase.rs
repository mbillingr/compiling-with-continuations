use crate::core::sets::Set;
use crate::languages::cps_lang::ast::{Expr, Transform, Transformed, Value};
use crate::set;
use std::collections::VecDeque;
use std::hash::Hash;

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
}

#[derive(Debug, Clone)]
pub struct SpillRecord<V: Eq + Hash> {
    bound_var: V,
    contained_vars: Set<V>,
}

impl<V: Clone + Eq + Hash> Spill<V> {
    pub fn new(n_registers: usize) -> Self {
        Spill {
            n_registers,
            previous_result: set![],
            current_spill_record: None,
            unspilled_vars: set![],
            duplicate_vars: set![],
        }
    }
}

impl<V: Clone + Eq + Hash + std::fmt::Debug> Transform<V> for Spill<V> {
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

        let (sv_after, sc_after) = if spill_record_still_useful {
            let s = self.current_spill_record.clone().unwrap();
            (Some(s.bound_var), s.contained_vars)
        } else {
            (None, set![])
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
            todo!("must crate new spill record")
        } else {
            let must_fetch = args.difference(&self.unspilled_vars.union(&new_dups));
            // In contrast to the book, I add W to the unspilled vars.
            match must_fetch.len() {
                0 => {
                    self.unspilled_vars = self.unspilled_vars.union(&w).intersection(&v_after);
                    self.previous_result = w;
                    self.duplicate_vars = new_dups;
                    self.current_spill_record = sv_after.map(|bound_var| SpillRecord {
                        bound_var,
                        contained_vars: sc_after,
                    });
                    Transformed::Continue
                }
                1 => todo!("fetch variables from spill {:?}", expr),
                _ => todo!("fetch variables from spill"),
            }
        }
    }

    fn visit_value(&mut self, _value: &Value<V>) -> Transformed<Value<V>> {
        Transformed::Continue
    }
}

impl<V: Clone + Eq + Hash + std::fmt::Debug> Spill<V> {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expr_unchanged_if_nothing_to_spill() {
        let expr = Expr::from_str("(halt 0)").unwrap();
        assert_eq!(expr.transform(&mut Spill::new(5)), expr);
    }

    #[test]
    fn no_spill_needed_because_variables_are_no_longer_used() {
        let expr =
            Expr::from_str("(primop + () (a b c d e) ((primop + () (f) ((halt a)))))").unwrap();
        assert_eq!(expr.transform(&mut Spill::new(5)), expr);
    }

    #[test]
    fn no_spill_needed_because_vars_fit_exactly_in_registers() {
        let expr =
            Expr::from_str("(primop + () (a b c d) ((primop + () (e) ((a b c d e)))))").unwrap();
        assert_eq!(expr.transform(&mut Spill::new(5)), expr);
    }

    #[test]
    fn spill_decision() {
        assert_eq!(
            Spill::<&str> {
                n_registers: 2,
                previous_result: Set::empty(),
                current_spill_record: None,
                unspilled_vars: Set::empty(),
                duplicate_vars: Set::empty(),
            }
            .must_spill(&Set::empty(), &Set::empty(), &Set::empty(), &None),
            false
        );

        todo!("check all relevant cases")
    }

    #[test]
    fn must_spill() {
        let expr = Expr::from_str(
            "(primop + () (a b c d) (
              (primop + () (e f) (
                (a b c d e f)))))",
        )
        .unwrap();
        let expect = Expr::from_str(
            "(primop + () (a b c d) (
              (record () spill 
                (primop + () (e f) (
                  (select 3 spill d_ (a b c d_ e f)))))))",
        )
        .unwrap();
        assert_eq!(expr.transform(&mut Spill::new(5)), expect);
    }
}
