use crate::core::sets::Set;
use crate::languages::cps_lang::ast::{Expr, Transform, Transformed, Value};
use crate::set;
use std::collections::VecDeque;
use std::hash::Hash;

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

#[derive(Clone)]
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

impl<V: Clone + Eq + Hash> Transform<V> for Spill<V> {
    fn visit_expr(&mut self, expr: &Expr<V>) -> Transformed<Expr<V>> {
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
            (set![s.bound_var], s.contained_vars)
        } else {
            (set![], set![])
        };

        let n_dup = self.n_registers
            - s_before.len()
            - self
                .unspilled_vars
                .intersection(&v_before)
                .union(&self.previous_result)
                .len();

        if n_dup < self.duplicate_vars.len() {
            let new_dups = self.duplicate_vars.clone();
            // discard most distantly used members of duplicate_vars
            let dups_to_drop = remove_n_next_used_vars_from(
                self.duplicate_vars.clone(),
                expr,
                self.duplicate_vars.len() - n_dup,
            );
            // is it enough to compute new_dups, or is there something we need to do?
            let new_dups = self.duplicate_vars.difference(&dups_to_drop);
        }

        let need_more_registers_for_arguments = args
            .union(&self.unspilled_vars.intersection(&v_after))
            .len()
            > self.n_registers - sv_after.len();
        let need_more_registers_for_results =
            w.union(&self.unspilled_vars.intersection(&v_after)).len()
                > self.n_registers - sv_after.len();

        if need_more_registers_for_arguments | need_more_registers_for_results {
            todo!("must crate new spill record")
        } else {
            todo!("fetch variables from spill if necessary")
        }
    }

    fn visit_value(&mut self, value: &Value<V>) -> Transformed<Value<V>> {
        Transformed::Continue
    }
}

fn remove_n_next_used_vars_from<V: Eq + Hash + Clone>(
    mut vars: Set<V>,
    expr: &Expr<V>,
    n_to_remove: usize,
) -> Set<V> {
    /// breath first traversal of the expression tree to find earliest
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expr_unchanged_if_nothing_to_spill() {
        let expr = Expr::from_str("(halt 0)").unwrap();
        assert_eq!(expr.transform(&mut Spill::new(5)), expr);
    }
}
