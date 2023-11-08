use crate::core::clicker::Clicker;
use crate::core::reference::Ref;
use crate::languages::common_primops::PrimOp;
use crate::languages::cps_lang::ast::{Expr, Transform, Transformed, Value};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::hash::Hash;

#[derive(Clone)]
pub struct ConstantFolder<V> {
    clicker: Clicker,
    env: HashMap<V, ValueInfo<V>>,
}

impl<V> Default for ConstantFolder<V> {
    fn default() -> Self {
        ConstantFolder {
            clicker: Default::default(),
            env: Default::default(),
        }
    }
}

impl<V: Clone + Eq + Hash> ConstantFolder<V> {
    pub fn new(clicker: Clicker) -> Self {
        ConstantFolder {
            clicker,
            env: Default::default(),
        }
    }

    pub fn fold<F: Clone + PartialEq>(&self, expr: &Expr<V, F>) -> Expr<V, F> {
        match expr {
            Expr::App(rator, rands) => {
                Expr::App(self.substitute_value(rator), self.substitute_values(rands))
            }

            Expr::Switch(k, cnts) => {
                let k_ = self.inform(k);
                match k_ {
                    ValueInfo::ConstInt(idx) => self.fold(&cnts[idx as usize]),
                    _ => Expr::Switch(
                        k.clone(),
                        Ref::array(cnts.iter().map(|c| self.fold(c)).map(Ref::new).collect()),
                    ),
                }
            }

            Expr::PrimOp(op, args @ Ref([a, b]), vars, Ref([no, yes])) if op.is_branching() => {
                match op {
                    PrimOp::ISame | PrimOp::FSame | PrimOp::SSame => {
                        self.fold_comparison(ValueInfo::is_eq, a, b, yes, no)
                    }
                    PrimOp::ILess => self.fold_comparison(ValueInfo::is_less, a, b, yes, no),
                    _ => todo!(),
                }
                .unwrap_or_else(|| {
                    Expr::PrimOp(
                        *op,
                        self.substitute_values(args),
                        *vars,
                        Ref::array(vec![self.fold(no).into(), self.fold(yes).into()]),
                    )
                })
            }

            Expr::PrimOp(op, args @ Ref([a, b]), Ref([res]), Ref([cnt])) => match op {
                _ => todo!(),
            },

            Expr::Halt(val) => Expr::Halt(self.substitute_value(val)),

            _ => todo!(),
        }
    }

    fn fold_comparison<F: Clone + PartialEq>(
        &self,
        op: impl Fn(&ValueInfo<V>, &ValueInfo<V>) -> Option<bool>,
        a: &Value<V, F>,
        b: &Value<V, F>,
        yes: &Expr<V, F>,
        no: &Expr<V, F>,
    ) -> Option<Expr<V, F>> {
        let a_ = self.inform(a);
        let b_ = self.inform(b);

        match op(&a_, &b_) {
            None => None,
            Some(true) => Some(self.fold(yes)),
            Some(false) => Some(self.fold(no)),
        }
    }

    fn inform<F>(&self, val: &Value<V, F>) -> ValueInfo<V> {
        match val {
            Value::Int(x) => ValueInfo::ConstInt(*x),
            Value::Real(x) => ValueInfo::ConstReal(*x),
            Value::String(x) => ValueInfo::ConstStr(*x),
            Value::Var(v) => self
                .env
                .get(v)
                .cloned()
                .unwrap_or_else(|| ValueInfo::Unknown(v.clone())),
            _ => todo!(),
        }
    }

    fn substitute_value<F: Clone>(&self, val: &Value<V, F>) -> Value<V, F> {
        match val {
            Value::Var(name) => {
                match self.env.get(name) {
                    None => val.clone(),
                    Some(ValueInfo::Unknown(v)) => Value::Var(v.clone()), // could also return original name... don't know which is better
                    Some(ValueInfo::ConstInt(x)) => Value::Int(*x),
                    Some(ValueInfo::ConstReal(x)) => Value::Real(*x),
                    Some(ValueInfo::ConstStr(x)) => Value::String(*x),
                }
            }
            _ => val.clone(),
        }
    }

    fn substitute_values<F: Clone>(&self, vals: &[Value<V, F>]) -> Ref<[Value<V, F>]> {
        Ref::array(vals.iter().map(|v| self.substitute_value(v)).collect())
    }
}

#[derive(Clone, Debug, PartialEq)]
enum ValueInfo<V> {
    Unknown(V),
    ConstInt(i64),
    ConstReal(f64),
    ConstStr(Ref<String>),
}

impl<V: PartialEq> ValueInfo<V> {
    fn is_eq(&self, other: &Self) -> Option<bool> {
        self.partial_cmp(other).map(|o| o == Ordering::Equal)
    }

    fn is_less(&self, other: &Self) -> Option<bool> {
        self.partial_cmp(other).map(|o| o == Ordering::Less)
    }
}

impl<V: PartialEq> PartialOrd for ValueInfo<V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (ValueInfo::Unknown(a), ValueInfo::Unknown(b)) if a == b => Some(Ordering::Equal),
            (ValueInfo::Unknown(_), _) | (_, ValueInfo::Unknown(_)) => None,
            (ValueInfo::ConstInt(a), ValueInfo::ConstInt(b)) => i64::partial_cmp(a, b),
            (ValueInfo::ConstReal(a), ValueInfo::ConstReal(b)) => f64::partial_cmp(a, b),
            (ValueInfo::ConstStr(a), ValueInfo::ConstStr(b)) => str::partial_cmp(a, b),
            _ => None,
        }
    }
}

impl<V: Clone + PartialEq, F: Clone + PartialEq> Transform<V, F> for ConstantFolder<V> {
    fn autoclick(&mut self) {
        self.clicker.click()
    }

    fn visit_expr(&mut self, expr: &Expr<V, F>) -> Transformed<Expr<V, F>> {
        match expr {
            Expr::Switch(Value::Int(idx), cnts) => {
                Transformed::Again((*cnts[*idx as usize]).clone())
            }

            Expr::PrimOp(
                PrimOp::ISame | PrimOp::FSame | PrimOp::SSame,
                Ref([a, b]),
                _,
                Ref([_, yes]),
            ) if a == b => Transformed::Again((**yes).clone()),

            // Variables may have any value, so we can never know in advance if they are the same
            Expr::PrimOp(
                PrimOp::ISame | PrimOp::FSame | PrimOp::SSame,
                Ref([Value::Var(_), _] | [_, Value::Var(_)]),
                _,
                Ref([_, _]),
            ) => Transformed::Continue,

            Expr::PrimOp(
                PrimOp::ISame | PrimOp::FSame | PrimOp::SSame,
                Ref([_, _]),
                _,
                Ref([no, _]),
            ) => Transformed::Again((**no).clone()),

            Expr::PrimOp(PrimOp::ILess, Ref([Value::Int(a), Value::Int(b)]), _, Ref([no, yes])) => {
                if a < b {
                    Transformed::Again((**yes).clone())
                } else {
                    Transformed::Again((**no).clone())
                }
            }

            Expr::PrimOp(PrimOp::ILess, Ref([Value::Var(a), Value::Var(b)]), _, Ref([no, _]))
                if a == b =>
            {
                Transformed::Again((**no).clone())
            }

            Expr::PrimOp(
                PrimOp::IAdd,
                Ref([Value::Int(a), Value::Int(b)]),
                Ref([var]),
                Ref([cnt]),
            ) => Transformed::Again((**cnt).substitute_var(var, &Value::Int(*a + *b))),

            Expr::PrimOp(PrimOp::IAdd, Ref([Value::Int(0), x]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, x))
            }

            Expr::PrimOp(PrimOp::IAdd, Ref([x, Value::Int(0)]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, x))
            }

            Expr::PrimOp(
                PrimOp::ISub,
                Ref([Value::Int(a), Value::Int(b)]),
                Ref([var]),
                Ref([cnt]),
            ) => Transformed::Again((**cnt).substitute_var(var, &Value::Int(*a - *b))),

            Expr::PrimOp(PrimOp::ISub, Ref([x, Value::Int(0)]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, x))
            }

            Expr::PrimOp(
                PrimOp::IMul,
                Ref([Value::Int(a), Value::Int(b)]),
                Ref([var]),
                Ref([cnt]),
            ) => Transformed::Again((**cnt).substitute_var(var, &Value::Int(*a * *b))),

            Expr::PrimOp(PrimOp::IMul, Ref([x, Value::Int(1)]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, x))
            }

            Expr::PrimOp(PrimOp::IMul, Ref([Value::Int(1), x]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, x))
            }

            Expr::PrimOp(PrimOp::IMul, Ref([_, Value::Int(0)]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, &Value::Int(0)))
            }

            Expr::PrimOp(PrimOp::IMul, Ref([Value::Int(0), _]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, &Value::Int(0)))
            }

            Expr::PrimOp(
                PrimOp::IDiv,
                Ref([Value::Int(a), Value::Int(b)]),
                Ref([var]),
                Ref([cnt]),
            ) => Transformed::Again((**cnt).substitute_var(var, &Value::Int(*a / *b))),

            Expr::PrimOp(PrimOp::IDiv, Ref([x, Value::Int(1)]), Ref([var]), Ref([cnt])) => {
                Transformed::Again((**cnt).substitute_var(var, x))
            }

            _ => Transformed::Continue,
        }
    }

    fn visit_value(&mut self, _: &Value<V, F>) -> Transformed<Value<V, F>> {
        Transformed::Continue
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use map_macro::hash_map;

    #[test]
    fn fold_switch_over_constant() {
        let x = Expr::from_str("(switch 1 (halt 10) (halt 20) (halt 30))").unwrap();
        let y = Expr::from_str("(halt 20)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let cf = ConstantFolder {
            clicker: Default::default(),
            env: hash_map!["k".into() => ValueInfo::ConstInt(2)],
        };
        let x = Expr::from_str("(switch k (halt 10) (halt 20) (halt 30))").unwrap();
        let y = Expr::from_str("(halt 30)").unwrap();
        assert_eq!(cf.fold(&x), y);
    }

    #[test]
    fn fold_constant_equality() {
        let x = Expr::from_str("(primop = (0 0) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(yes)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop = (0 1) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(no)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop =f (0.0 0.0) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(yes)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop =f (1.0 0.1) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(no)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop =s (\"foo\" \"foo\") () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(yes)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop =s (\"foo\" \"bar\") () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(no)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);
    }

    #[test]
    fn fold_integer_comparison() {
        let x = Expr::from_str("(primop < (0 0) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(no)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop < (0 1) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(yes)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop < (x x) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(no)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop < (x y) () ((no) (yes)))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), x);

        let x = Expr::from_str("(primop < (0 x) () ((no) (yes)))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), x);

        let x = Expr::from_str("(primop < (x 0) () ((no) (yes)))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), x);
    }

    #[test]
    fn fold_comparison_over_variables() {
        let x = Expr::from_str("(primop = (x x) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(yes)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop = (x y) () ((no) (yes)))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), x);

        let x = Expr::from_str("(primop = (x 0) () ((no) (yes)))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), x);

        let x = Expr::from_str("(primop = (0 x) () ((no) (yes)))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), x);
    }

    #[test]
    fn fold_comparison_over_bound_variables() {
        let cf = ConstantFolder {
            clicker: Default::default(),
            env: hash_map![
                "a".into() => ValueInfo::ConstInt(1),
                "b".into() => ValueInfo::ConstInt(2),
                "c".into() => ValueInfo::ConstInt(2),
            ],
        };

        let x = Expr::from_str("(primop = (a a) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(yes)").unwrap();
        assert_eq!(cf.clone().fold(&x), y);

        let x = Expr::from_str("(primop = (b c) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(yes)").unwrap();
        assert_eq!(cf.clone().fold(&x), y);

        let x = Expr::from_str("(primop = (a b) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(no)").unwrap();
        assert_eq!(cf.fold(&x), y);
    }

    #[test]
    fn fold_integer_arithmetic() {
        let x = Expr::from_str("(primop + (1 2) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt 3)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop - (2 1) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt 1)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop * (2 2) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt 4)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop / (6 2) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt 3)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop + (0 x) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt x)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop + (x 0) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt x)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop - (x 0) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt x)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop * (x 1) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt x)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop * (1 x) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt x)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop / (x 1) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt x)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop * (x 0) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt 0)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(primop * (0 x) (r) ((halt r)))").unwrap();
        let y = Expr::from_str("(halt 0)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        // fold-cascade
        let x = Expr::from_str("(primop + (1 2) (y) ((primop + (y y) (z) ((halt z)))))").unwrap();
        let y = Expr::from_str("(halt 6)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);
    }
}
