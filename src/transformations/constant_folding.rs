use crate::core::clicker::Clicker;
use crate::core::reference::Ref;
use crate::languages::common_primops::PrimOp;
use crate::languages::cps_lang::ast::{AccessPath, Expr, Value};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;
use std::sync::Arc;

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

impl<V: Clone + Eq + Hash + std::fmt::Debug> ConstantFolder<V> {
    pub fn new(clicker: Clicker) -> Self {
        ConstantFolder {
            clicker,
            env: Default::default(),
        }
    }

    pub fn fold<F: Clone + PartialEq>(&mut self, expr: &Expr<V, F>) -> Expr<V, F> {
        match expr {
            Expr::Record(fields, var, cnt) => Expr::Record(
                Ref::array(
                    fields
                        .iter()
                        .map(|fap| self.substitute_field(fap))
                        .collect(),
                ),
                var.clone(),
                {
                    let info = ValueInfo::Record(
                        0,
                        Arc::new(fields.iter().map(|(f, _)| self.inform(f)).collect()),
                    );
                    self.env.insert(var.clone(), info);
                    self.fold(cnt).into()
                },
            ),

            Expr::Select(idx, rec, var, cnt) => match self.inform(rec) {
                ValueInfo::Record(ofs, fields) => {
                    self.env
                        .insert(var.clone(), fields[(ofs + idx) as usize].clone());
                    self.fold(cnt)
                }
                ValueInfo::Unknown(v) => {
                    Expr::Select(*idx, self.substitute_value(rec), var.clone(), {
                        self.env
                            .insert(var.clone(), ValueInfo::Select(vec![*idx], v));
                        self.fold(cnt).into()
                    })
                }
                ValueInfo::Select(mut path, v) => {
                    path.push(*idx);
                    Expr::Select(*idx, self.substitute_value(rec), var.clone(), {
                        self.env.insert(var.clone(), ValueInfo::Select(path, v));
                        self.fold(cnt).into()
                    })
                }
                ValueInfo::Offset(ofs, v) => {
                    Expr::Select(ofs + idx, Value::Var(v.clone()), var.clone(), {
                        self.env
                            .insert(var.clone(), ValueInfo::Select(vec![ofs + idx], v));
                        self.fold(cnt).into()
                    })
                }
                _ => unimplemented!(),
            },

            Expr::Offset(0, Value::Var(rec), var, cnt) => {
                self.env.insert(var.clone(), ValueInfo::Alias(rec.clone()));
                println!("{:?}", self.env);
                self.fold(cnt)
            }

            Expr::Offset(idx, rec, var, cnt) => match self.inform(rec) {
                ValueInfo::Record(ofs, fields) => {
                    self.env
                        .insert(var.clone(), ValueInfo::Record(ofs + idx, fields));
                    Expr::Offset(
                        *idx,
                        self.substitute_value(rec),
                        var.clone(),
                        self.fold(cnt).into(),
                    )
                }
                ValueInfo::Unknown(v) => {
                    self.env.insert(var.clone(), ValueInfo::Offset(*idx, v));
                    Expr::Offset(
                        *idx,
                        self.substitute_value(rec),
                        var.clone(),
                        self.fold(cnt).into(),
                    )
                }
                ValueInfo::Select(_, _) => {
                    let v = if let Value::Var(v) = rec {
                        v.clone()
                    } else {
                        unreachable!()
                    };
                    self.env.insert(var.clone(), ValueInfo::Offset(*idx, v));
                    Expr::Offset(
                        *idx,
                        self.substitute_value(rec),
                        var.clone(),
                        self.fold(cnt).into(),
                    )
                }
                ValueInfo::Offset(ofs, v) => {
                    self.env
                        .insert(var.clone(), ValueInfo::Offset(ofs + idx, v.clone()));
                    Expr::Offset(ofs + idx, Value::Var(v), var.clone(), self.fold(cnt).into())
                }
                _ => todo!(),
            },

            Expr::App(rator, rands) => {
                Expr::App(self.substitute_value(rator), self.substitute_values(rands))
            }

            Expr::Fix(defs, cnt) => {
                let mut defs_out = vec![];
                for (f, p, b) in defs.iter() {
                    defs_out.push((f.clone(), *p, self.fold(b).into()))
                }
                Expr::Fix(Ref::array(defs_out), self.fold(cnt).into())
            }

            Expr::Switch(k, cnts) => {
                let k_ = self.inform(k);
                match k_ {
                    ValueInfo::ConstInt(idx) => {
                        self.clicker.click();
                        self.fold(&cnts[idx as usize])
                    }
                    _ => Expr::Switch(
                        k.clone(),
                        Ref::array(cnts.iter().map(|c| self.fold(c)).map(Ref::new).collect()),
                    ),
                }
            }

            Expr::PrimOp(
                op @ (PrimOp::ShowInt | PrimOp::ShowReal | PrimOp::ShowStr),
                args @ Ref([x]),
                r @ Ref([res]),
                Ref([cnt]),
            ) => {
                let x_ = self.inform(x);
                self.env.insert(res.clone(), x_);
                Expr::PrimOp(
                    *op,
                    self.substitute_values(args),
                    *r,
                    Ref::array(vec![self.fold(cnt).into()]),
                )
            }

            Expr::PrimOp(op, args @ Ref([a]), vars, Ref([no, yes])) if op.is_branching() => {
                match op {
                    PrimOp::IsZero => self.fold_predicate(ValueInfo::is_zero, a, yes, no),
                    PrimOp::CorP => self.fold_predicate(ValueInfo::is_ptr, a, yes, no),
                    _ => todo!("{op:?}"),
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

            Expr::PrimOp(op, args @ Ref([a, b]), vars, Ref([no, yes])) if op.is_branching() => {
                match op {
                    PrimOp::ISame | PrimOp::FSame | PrimOp::SSame => {
                        self.fold_comparison(ValueInfo::is_eq, a, b, yes, no)
                    }
                    PrimOp::ILess => self.fold_comparison(ValueInfo::is_less, a, b, yes, no),
                    _ => todo!("{op:?}"),
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

            Expr::PrimOp(op, args @ Ref([a]), rr @ Ref([res]), Ref([cnt])) => match op {
                _ => {
                    let a_ = self.inform(a);

                    match op {
                        PrimOp::INeg => ValueInfo::neg(&a_),
                        PrimOp::Untag => ValueInfo::untag(&a_),
                        _ => todo!("{op:?}"),
                    }
                    .map(|r| {
                        self.clicker.click();
                        self.env.insert(res.clone(), r);
                        self.fold(cnt)
                    })
                    .unwrap_or_else(|| {
                        Expr::PrimOp(
                            *op,
                            self.substitute_values(args),
                            *rr,
                            Ref::array(vec![self.fold(cnt).into()]),
                        )
                    })
                }
            },

            Expr::PrimOp(op, args @ Ref([a, b]), rr @ Ref([res]), Ref([cnt])) => match op {
                _ => {
                    let a_ = self.inform(a);
                    let b_ = self.inform(b);

                    match op {
                        PrimOp::IAdd => ValueInfo::add(&a_, &b_),
                        PrimOp::ISub => ValueInfo::sub(&a_, &b_),
                        PrimOp::IMul => ValueInfo::mul(&a_, &b_),
                        PrimOp::IDiv => ValueInfo::div(&a_, &b_),
                        _ => todo!("{op:?}"),
                    }
                    .map(|r| {
                        self.clicker.click();
                        self.env.insert(res.clone(), r);
                        self.fold(cnt)
                    })
                    .unwrap_or_else(|| {
                        Expr::PrimOp(
                            *op,
                            self.substitute_values(args),
                            *rr,
                            Ref::array(vec![self.fold(cnt).into()]),
                        )
                    })
                }
            },

            Expr::PrimOp(op, _, _, _) => todo!("{op:?}"),

            Expr::Halt(val) => Expr::Halt(self.substitute_value(val)),

            Expr::Panic(msg) => Expr::Panic(*msg),
        }
    }

    fn fold_predicate<F: Clone + PartialEq>(
        &mut self,
        op: impl Fn(&ValueInfo<V>) -> Option<bool>,
        a: &Value<V, F>,
        yes: &Expr<V, F>,
        no: &Expr<V, F>,
    ) -> Option<Expr<V, F>> {
        let a_ = self.inform(a);

        let branch = if op(&a_)? { yes } else { no };

        self.clicker.click();
        Some(self.fold(branch))
    }

    fn fold_comparison<F: Clone + PartialEq>(
        &mut self,
        op: impl Fn(&ValueInfo<V>, &ValueInfo<V>) -> Option<bool>,
        a: &Value<V, F>,
        b: &Value<V, F>,
        yes: &Expr<V, F>,
        no: &Expr<V, F>,
    ) -> Option<Expr<V, F>> {
        let a_ = self.inform(a);
        let b_ = self.inform(b);

        let branch = if op(&a_, &b_)? { yes } else { no };

        self.clicker.click();
        Some(self.fold(branch))
    }

    fn inform<F>(&self, val: &Value<V, F>) -> ValueInfo<V> {
        let mut vi = match val {
            Value::Int(x) => ValueInfo::ConstInt(*x),
            Value::Real(x) => ValueInfo::ConstReal(*x),
            Value::String(x) => ValueInfo::ConstStr(*x),
            Value::Var(v) => self
                .env
                .get(v)
                .cloned()
                .unwrap_or_else(|| ValueInfo::Unknown(v.clone())),
            _ => todo!(),
        };

        let mut seen_names = HashSet::new();

        while let ValueInfo::Alias(v) = vi {
            if seen_names.contains(&v) {
                panic!("alias loop detected")
            }

            vi = self
                .env
                .get(&v)
                .cloned()
                .unwrap_or_else(|| ValueInfo::Unknown(v.clone()));

            seen_names.insert(v);
        }

        vi
    }

    fn substitute_field<F: Clone>(
        &self,
        (f, ap): &(Value<V, F>, AccessPath),
    ) -> (Value<V, F>, AccessPath) {
        let f_ = self.inform(f);
        match f_ {
            ValueInfo::Select(path, r) => (Value::Var(r), ap.preselect(&path)),
            _ => (self.substitute_value(f), ap.clone()),
        }
    }

    fn substitute_value<F: Clone>(&self, val: &Value<V, F>) -> Value<V, F> {
        let result = match val {
            Value::Var(name) => {
                let mut name = name;
                loop {
                    let r = match self.env.get(name) {
                        None => return val.clone(),
                        Some(ValueInfo::Unknown(v)) => Value::Var(v.clone()), // could also return original name... don't know which is better
                        Some(ValueInfo::Alias(v)) => {
                            if v == name {
                                panic!("alias loop detected")
                            }
                            name = v;
                            continue;
                        }
                        Some(ValueInfo::ConstInt(x)) => Value::Int(*x),
                        Some(ValueInfo::ConstReal(x)) => Value::Real(*x),
                        Some(ValueInfo::ConstStr(x)) => Value::String(*x),
                        Some(ValueInfo::Record(_, _)) => return Value::Var(name.clone()),
                        Some(ValueInfo::Offset(_, _)) => return Value::Var(name.clone()),
                        Some(ValueInfo::Select(_, _)) => return Value::Var(name.clone()),
                    };
                    break r;
                }
            }
            _ => return val.clone(),
        };

        self.clicker.click();
        result
    }

    fn substitute_values<F: Clone>(&self, vals: &[Value<V, F>]) -> Ref<[Value<V, F>]> {
        Ref::array(vals.iter().map(|v| self.substitute_value(v)).collect())
    }
}

#[derive(Clone, Debug, PartialEq)]
enum ValueInfo<V> {
    Unknown(V),
    Alias(V),
    ConstInt(i64),
    ConstReal(f64),
    ConstStr(Ref<String>),
    Record(isize, Arc<Vec<Self>>),
    Offset(isize, V),
    Select(Vec<isize>, V),
}

impl<V: Clone + PartialEq> ValueInfo<V> {
    fn is_zero(&self) -> Option<bool> {
        match self {
            ValueInfo::Alias(_) => unreachable!(),
            ValueInfo::Unknown(_) => None,
            ValueInfo::ConstInt(x) => Some(*x == 0),
            ValueInfo::ConstReal(x) => Some(*x == 0.0),
            ValueInfo::ConstStr(_) => Some(false),
            ValueInfo::Record(_, _) => Some(false),
            ValueInfo::Offset(_, _) => Some(false),
            ValueInfo::Select(_, _) => None,
        }
    }

    fn is_ptr(&self) -> Option<bool> {
        match self {
            ValueInfo::Alias(_) => unreachable!(),
            ValueInfo::Unknown(_) => None,
            ValueInfo::ConstInt(_) => Some(false),
            ValueInfo::ConstReal(_) => Some(false),
            ValueInfo::ConstStr(_) => Some(false), // not sure...
            ValueInfo::Record(_, _) => Some(true),
            ValueInfo::Offset(_, _) => Some(true),
            ValueInfo::Select(_, _) => None,
        }
    }

    fn is_eq(&self, other: &Self) -> Option<bool> {
        self.partial_cmp(other).map(|o| o == Ordering::Equal)
    }

    fn is_less(&self, other: &Self) -> Option<bool> {
        self.partial_cmp(other).map(|o| o == Ordering::Less)
    }

    fn neg(&self) -> Option<Self> {
        match self {
            ValueInfo::Alias(_) => unreachable!(),
            ValueInfo::Unknown(_) => None,
            ValueInfo::ConstInt(x) => Some(ValueInfo::ConstInt(-x)),
            ValueInfo::ConstReal(x) => Some(ValueInfo::ConstReal(-x)),
            ValueInfo::ConstStr(_) => None,
            ValueInfo::Record(_, _) => None,
            ValueInfo::Offset(_, _) => None,
            ValueInfo::Select(_, _) => None,
        }
    }

    fn untag(&self) -> Option<Self> {
        match self {
            ValueInfo::Alias(_) => unreachable!(),
            ValueInfo::Unknown(_) => None,
            ValueInfo::ConstInt(x) => Some(ValueInfo::ConstInt((x - 1) / 2)),
            ValueInfo::ConstReal(_) => None,
            ValueInfo::ConstStr(_) => None,
            ValueInfo::Record(_, _) => None,
            ValueInfo::Offset(_, _) => None,
            ValueInfo::Select(_, _) => None,
        }
    }

    fn add(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (ValueInfo::ConstInt(0), x) | (x, ValueInfo::ConstInt(0)) => Some(x.clone()),
            (ValueInfo::ConstReal(y), x) | (x, ValueInfo::ConstReal(y)) if *y == 0.0 => {
                Some(x.clone())
            }
            (ValueInfo::ConstInt(a), ValueInfo::ConstInt(b)) => Some(ValueInfo::ConstInt(a + b)),
            (ValueInfo::ConstReal(a), ValueInfo::ConstReal(b)) => Some(ValueInfo::ConstReal(a + b)),
            _ => None,
        }
    }

    fn sub(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (x, ValueInfo::ConstInt(0)) => Some(x.clone()),
            (x, ValueInfo::ConstReal(y)) if *y == 0.0 => Some(x.clone()),
            (ValueInfo::ConstInt(a), ValueInfo::ConstInt(b)) => Some(ValueInfo::ConstInt(a - b)),
            (ValueInfo::ConstReal(a), ValueInfo::ConstReal(b)) => Some(ValueInfo::ConstReal(a - b)),
            _ => None,
        }
    }

    fn mul(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (ValueInfo::ConstInt(0), _) | (_, ValueInfo::ConstInt(0)) => {
                Some(ValueInfo::ConstInt(0))
            }
            (ValueInfo::ConstReal(y), _) | (_, ValueInfo::ConstReal(y)) if *y == 0.0 => {
                Some(ValueInfo::ConstReal(0.0))
            }
            (ValueInfo::ConstInt(1), x) | (x, ValueInfo::ConstInt(1)) => Some(x.clone()),
            (ValueInfo::ConstReal(y), x) | (x, ValueInfo::ConstReal(y)) if *y == 1.0 => {
                Some(x.clone())
            }
            (ValueInfo::ConstInt(a), ValueInfo::ConstInt(b)) => Some(ValueInfo::ConstInt(a * b)),
            (ValueInfo::ConstReal(a), ValueInfo::ConstReal(b)) => Some(ValueInfo::ConstReal(a * b)),
            _ => None,
        }
    }

    fn div(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (x, ValueInfo::ConstInt(1)) => Some(x.clone()),
            (x, ValueInfo::ConstReal(y)) if *y == 1.0 => Some(x.clone()),
            (ValueInfo::ConstInt(a), ValueInfo::ConstInt(b)) => Some(ValueInfo::ConstInt(a / b)),
            (ValueInfo::ConstReal(a), ValueInfo::ConstReal(b)) => Some(ValueInfo::ConstReal(a / b)),
            _ => None,
        }
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

#[cfg(test)]
mod tests {
    use super::*;
    use map_macro::hash_map;

    #[test]
    fn fold_switch_over_constant() {
        let x = Expr::from_str("(switch 1 (halt 10) (halt 20) (halt 30))").unwrap();
        let y = Expr::from_str("(halt 20)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let mut cf = ConstantFolder {
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
        let mut cf = ConstantFolder {
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

    #[test]
    fn fold_records() {
        let x = Expr::from_str("(primop const/ptr? (123) () ((no) (yes)))").unwrap();
        let y = Expr::from_str("(no)").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(record () r (primop const/ptr? (r) () ((no) (yes))))").unwrap();
        let y = Expr::from_str("(record () r (yes))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(record (1 2 3) r (select 0 r x (halt x)))").unwrap();
        let y = Expr::from_str("(record (1 2 3) r (halt 1))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(record (1 z 3) r (select 1 r x (halt x)))").unwrap();
        let y = Expr::from_str("(record (1 z 3) r (halt z))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(record (1 2 3) r (offset 1 r s (halt s)))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), x);

        let x = Expr::from_str("(record (1 2 3) r (offset 0 r s (halt s)))").unwrap();
        let y = Expr::from_str("(record (1 2 3) r (halt r))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x =
            Expr::from_str("(record (1 2 3) r (offset 0 r s (select 1 r x (halt x))))").unwrap();
        let y = Expr::from_str("(record (1 2 3) r (halt 2))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x =
            Expr::from_str("(record (1 2 3) r (offset 1 r s (select 0 s x (halt x))))").unwrap();
        let y = Expr::from_str("(record (1 2 3) r (offset 1 r s (halt 2)))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x =
            Expr::from_str("(record (1 2 3) r (offset -1 r s (select 2 s x (halt x))))").unwrap();
        let y = Expr::from_str("(record (1 2 3) r (offset -1 r s (halt 2)))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);
    }

    #[test]
    fn fold_access() {
        let x = Expr::from_str("(select 1 r x (record (x) s (halt s)))").unwrap();
        let y = Expr::from_str("(select 1 r x (record ((r (sel 1 (ref 0)))) s (halt s)))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(select 2 r y (select 1 y x (record (x) s (halt s))))").unwrap();
        let y = Expr::from_str(
            "(select 2 r y (select 1 y x (record ((r (sel 1 (sel 2 (ref 0))))) s (halt s))))",
        )
        .unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(offset 2 r y (offset 1 y x (record (x) s (halt s))))").unwrap();
        let y = Expr::from_str("(offset 2 r y (offset 3 r x (record (x) s (halt s))))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(offset 2 r y (select 1 y x (record (x) s (halt s))))").unwrap();
        let y = Expr::from_str(
            "(offset 2 r y (select 3 r x (record ((r (sel 3 (ref 0)))) s (halt s))))",
        )
        .unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(select 2 r y (offset 1 y x (record (x) s (halt s))))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), x);

        let x = Expr::from_str("(select 1 r x (primop + (x 0) (y) ((halt y))))").unwrap();
        let y = Expr::from_str("(select 1 r x (halt x))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);
    }
}
