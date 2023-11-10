use crate::core::clicker::Clicker;
use crate::core::reference::Ref;
use crate::languages::common_primops::PrimOp;
use crate::languages::cps_lang::ast::{AccessPath, Expr, Value};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Clone)]
pub struct ConstantFolder<V: 'static, F: 'static> {
    clicker: Clicker,
    env: HashMap<V, ValueInfo<V, F>>,
}

impl<V, F> Default for ConstantFolder<V, F> {
    fn default() -> Self {
        ConstantFolder {
            clicker: Default::default(),
            env: Default::default(),
        }
    }
}

impl<V: Clone + Debug + Eq + Hash + PartialOrd, F: Clone + Debug + PartialOrd>
    ConstantFolder<V, F>
{
    pub fn new(clicker: Clicker) -> Self {
        ConstantFolder {
            clicker,
            env: Default::default(),
        }
    }

    pub fn fold(&mut self, expr: &Expr<V, F>) -> Expr<V, F> {
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
                    let info = ValueInfo::new_record(
                        var,
                        fields.iter().map(|(f, _)| {
                            // todo: include access paths
                            self.inform(f)
                        }),
                    );
                    self.env.insert(var.clone(), info);
                    self.fold(cnt).into()
                },
            ),

            Expr::Select(idx, rec, var, cnt) => {
                let rec_ = self.inform(rec);

                let out = rec_.select(var, *idx);

                if rec_.has_known_value() {
                    self.clicker.click();
                    self.env.insert(var.clone(), out);
                    self.fold(cnt)
                } else {
                    let (src, idx) = if let Some((src, [idx])) = out.known_path() {
                        (src.clone(), *idx)
                    } else {
                        (rec_.value, *idx)
                    };
                    self.env.insert(var.clone(), out);
                    Expr::Select(idx, src, var.clone(), self.fold(cnt).into())
                }
            }

            Expr::Offset(0, rec, var, cnt) => {
                self.clicker.click();
                let rec_ = self.inform(rec);
                self.env.insert(var.clone(), rec_);
                self.fold(cnt)
            }

            Expr::Offset(ofs, rec, var, cnt) => {
                let rec_ = self.inform(rec);
                let out = rec_.offset(var, *ofs);
                let (src_, ofs_) = out.known_offset().unwrap();
                self.env.insert(var.clone(), out.clone());
                Expr::Offset(ofs_, src_.clone(), var.clone(), self.fold(cnt).into())
            }

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
                match k_.known_int() {
                    Some(idx) => {
                        self.clicker.click();
                        self.fold(&cnts[idx as usize])
                    }
                    None => Expr::Switch(
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

    fn fold_predicate(
        &mut self,
        op: impl Fn(&ValueInfo<V, F>) -> Option<bool>,
        a: &Value<V, F>,
        yes: &Expr<V, F>,
        no: &Expr<V, F>,
    ) -> Option<Expr<V, F>> {
        let a_ = self.inform(a);

        let branch = if op(&a_)? { yes } else { no };

        self.clicker.click();
        Some(self.fold(branch))
    }

    fn fold_comparison(
        &mut self,
        op: impl Fn(&ValueInfo<V, F>, &ValueInfo<V, F>) -> Option<bool>,
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

    fn inform(&self, val: &Value<V, F>) -> ValueInfo<V, F> {
        match val {
            Value::Var(v) => self
                .env
                .get(v)
                .cloned()
                .unwrap_or_else(|| ValueInfo::unknown(v)),
            _ => ValueInfo::new_value(val.clone()),
        }
    }

    fn substitute_field(&self, (f, ap): &(Value<V, F>, AccessPath)) -> (Value<V, F>, AccessPath) {
        let f_ = self.inform(f);
        f_.extend_access(ap)
    }

    fn substitute_value(&self, val: &Value<V, F>) -> Value<V, F> {
        match val {
            Value::Var(name) => match self.env.get(name) {
                Some(vi) => {
                    let v_out = vi.concrete_value();
                    if &v_out != val {
                        self.clicker.click();
                    }
                    v_out
                }
                None => val.clone(),
            },
            _ => val.clone(),
        }
    }

    fn substitute_values(&self, vals: &[Value<V, F>]) -> Ref<[Value<V, F>]> {
        Ref::array(vals.iter().map(|v| self.substitute_value(v)).collect())
    }
}

#[derive(Clone, Debug, PartialEq)]
struct ValueInfo<V: 'static, F: 'static> {
    value: Value<V, F>,
    fields: Option<(Vec<Self>, isize)>,
    access: AccessInfo<V, F>,
}

#[derive(Clone, Debug, PartialEq)]
enum AccessInfo<V: 'static, F: 'static> {
    Nothing,
    Offset(isize, Value<V, F>),
    Path(Vec<isize>, Value<V, F>),
}

impl<V: Clone + PartialOrd, F: Clone + PartialOrd> ValueInfo<V, F> {
    fn unknown(var: &V) -> Self {
        ValueInfo {
            value: Value::Var(var.clone()),
            fields: None,
            access: AccessInfo::Nothing,
        }
    }

    fn new_value(val: Value<V, F>) -> Self {
        ValueInfo {
            value: val,
            fields: None,
            access: AccessInfo::Nothing,
        }
    }

    fn new_record(var: &V, fields: impl Iterator<Item = Self>) -> Self {
        // todo: take access paths into account!?
        ValueInfo {
            value: Value::Var(var.clone()),
            fields: Some((fields.collect(), 0)),
            access: AccessInfo::Offset(0, Value::Var(var.clone())),
        }
    }

    fn select(&self, var: &V, idx: isize) -> Self {
        let access = match self.access.clone() {
            AccessInfo::Nothing => AccessInfo::Path(vec![idx], self.value.clone()),
            AccessInfo::Offset(ofs, src) => AccessInfo::Path(vec![ofs + idx], src),
            AccessInfo::Path(mut path, src) => {
                path.push(idx);
                AccessInfo::Path(path, src)
            }
        };

        match &self.fields {
            Some((fields, ofs)) => {
                let vi = fields[(ofs + idx) as usize].clone();
                ValueInfo { access, ..vi }
            }
            None => ValueInfo {
                value: Value::Var(var.clone()),
                fields: None,
                access,
            },
        }
    }

    fn offset(&self, var: &V, ofs: isize) -> Self {
        let access = match self.access.clone() {
            AccessInfo::Offset(o0, src) => AccessInfo::Offset(o0 + ofs, src),
            _ => AccessInfo::Offset(ofs, self.value.clone()),
        };
        ValueInfo {
            value: Value::Var(var.clone()),
            fields: self.fields.clone().map(|(fields, o)| (fields, o + ofs)),
            access,
        }
    }

    fn extend_access(&self, ap: &AccessPath) -> (Value<V, F>, AccessPath) {
        match &self.access {
            AccessInfo::Nothing => (self.value.clone(), AccessPath::Ref(0)),
            AccessInfo::Offset(ofs, v) => (v.clone(), AccessPath::Ref(*ofs)),
            AccessInfo::Path(path, v) => (v.clone(), ap.preselect(path)),
        }
    }

    fn has_known_value(&self) -> bool {
        match &self.value {
            Value::Var(_) => self.fields.is_some(),
            _ => true,
        }
    }

    fn is_record(&self) -> bool {
        self.fields.is_some()
    }

    fn known_int(&self) -> Option<i64> {
        match &self.value {
            Value::Int(x) => Some(*x),
            _ => None,
        }
    }

    fn known_real(&self) -> Option<f64> {
        match &self.value {
            Value::Real(x) => Some(*x),
            _ => None,
        }
    }

    fn known_path(&self) -> Option<(&Value<V, F>, &[isize])> {
        match &self.access {
            AccessInfo::Path(path, src) => Some((src, path)),
            _ => None,
        }
    }

    fn known_offset(&self) -> Option<(&Value<V, F>, isize)> {
        match &self.access {
            AccessInfo::Offset(ofs, src) => Some((src, *ofs)),
            _ => None,
        }
    }

    fn concrete_value(&self) -> Value<V, F> {
        self.value.clone()
    }

    fn is_zero(&self) -> Option<bool> {
        match &self.value {
            Value::Var(_) => None,
            Value::Label(_) => Some(false),
            Value::Int(x) => Some(*x == 0),
            Value::Real(x) => Some(*x == 0.0),
            Value::String(_) => Some(false),
        }
    }

    fn is_ptr(&self) -> Option<bool> {
        if self.has_known_value() {
            Some(self.is_record())
        } else {
            None
        }
    }

    fn is_eq(&self, other: &Self) -> Option<bool> {
        self.partial_cmp(other).map(|o| o == Ordering::Equal)
    }

    fn is_less(&self, other: &Self) -> Option<bool> {
        self.partial_cmp(other).map(|o| o == Ordering::Less)
    }

    fn neg(&self) -> Option<Self> {
        self.known_int()
            .map(|x| Value::Int(-x))
            .or_else(|| self.known_real().map(|x| Value::Real(-x)))
            .map(Self::new_value)
    }

    fn untag(&self) -> Option<Self> {
        self.known_int()
            .map(|x| Value::Int((x - 1) / 2))
            .map(Self::new_value)
    }

    fn add(&self, other: &Self) -> Option<Self> {
        match (&self.value, &other.value) {
            (Value::Int(0), x) | (x, Value::Int(0)) => Some(x.clone()),
            (Value::Real(y), x) | (x, Value::Real(y)) if *y == 0.0 => Some(x.clone()),
            (Value::Int(a), Value::Int(b)) => Some(Value::Int(a + b)),
            (Value::Real(a), Value::Real(b)) => Some(Value::Real(a + b)),
            _ => None,
        }
        .map(Self::new_value)
    }

    fn sub(&self, other: &Self) -> Option<Self> {
        match (&self.value, &other.value) {
            (x, Value::Int(0)) => Some(x.clone()),
            (x, Value::Real(y)) if *y == 0.0 => Some(x.clone()),
            (Value::Int(a), Value::Int(b)) => Some(Value::Int(a - b)),
            (Value::Real(a), Value::Real(b)) => Some(Value::Real(a - b)),
            _ => None,
        }
        .map(Self::new_value)
    }

    fn mul(&self, other: &Self) -> Option<Self> {
        match (&self.value, &other.value) {
            (Value::Int(0), _) | (_, Value::Int(0)) => Some(Value::Int(0)),
            (Value::Real(y), _) | (_, Value::Real(y)) if *y == 0.0 => Some(Value::Real(0.0)),
            (Value::Int(1), x) | (x, Value::Int(1)) => Some(x.clone()),
            (Value::Real(y), x) | (x, Value::Real(y)) if *y == 1.0 => Some(x.clone()),
            (Value::Int(a), Value::Int(b)) => Some(Value::Int(a * b)),
            (Value::Real(a), Value::Real(b)) => Some(Value::Real(a * b)),
            _ => None,
        }
        .map(Self::new_value)
    }

    fn div(&self, other: &Self) -> Option<Self> {
        match (&self.value, &other.value) {
            (x, Value::Int(1)) => Some(x.clone()),
            (x, Value::Real(y)) if *y == 1.0 => Some(x.clone()),
            (Value::Int(a), Value::Int(b)) => Some(Value::Int(a / b)),
            (Value::Real(a), Value::Real(b)) => Some(Value::Real(a / b)),
            _ => None,
        }
        .map(Self::new_value)
    }
}

impl<V: PartialOrd, F: PartialOrd> PartialOrd for ValueInfo<V, F> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (&self.value, &other.value) {
            (Value::Var(a), Value::Var(b)) if a == b => Some(Ordering::Equal),
            (Value::Var(_), _) | (_, Value::Var(_)) => None,
            (Value::Label(a), Value::Label(b)) => F::partial_cmp(a, b),
            (Value::Int(a), Value::Int(b)) => i64::partial_cmp(a, b),
            (Value::Real(a), Value::Real(b)) => f64::partial_cmp(a, b),
            (Value::String(a), Value::String(b)) => str::partial_cmp(a, b),
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
            env: hash_map!["k".into() => ValueInfo::new_value(Value::Int(2))],
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
                "a".into() => ValueInfo::new_value(Value::Int(1)),
                "b".into() => ValueInfo::new_value(Value::Int(2)),
                "c".into() => ValueInfo::new_value(Value::Int(2)),
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
        let y = Expr::from_str("(offset 2 r y (offset 3 r x (record ((r (ref 3))) s (halt s))))")
            .unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(offset 2 r y (select 1 y x (record (x) s (halt s))))").unwrap();
        let y = Expr::from_str(
            "(offset 2 r y (select 3 r x (record ((r (sel 3 (ref 0)))) s (halt s))))",
        )
        .unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(select 2 r y (offset 1 y x (record (x) s (halt s))))").unwrap();
        let y = Expr::from_str("(select 2 r y (offset 1 y x (record ((y (ref 1))) s (halt s))))")
            .unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);

        let x = Expr::from_str("(select 1 r x (primop + (x 0) (y) ((halt y))))").unwrap();
        let y = Expr::from_str("(select 1 r x (halt x))").unwrap();
        assert_eq!(ConstantFolder::default().fold(&x), y);
    }
}
