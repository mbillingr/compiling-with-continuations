use crate::core::reference::Ref;
use crate::languages::common_primops::PrimOp;
use crate::languages::cps_lang::ast::{AccessPath, Expr, Value};
use crate::transformations::{GenSym, GensymContext};
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::sync::Arc;

#[derive(Debug)]
pub enum Op<V, F> {
    Label(F),
    BeginRecord(usize),
    PushRecord(Rand<V, F>),
    EndRecord(R<V>),
    Select(isize, Rand<V, F>, R<V>),
    Offset(isize, Rand<V, F>, R<V>),
    Tailcall(Rand<V, F>),
    Switch(Rand<V, F>, Vec<F>),
    If(Rand<V, F>, F, F),
    Halt(Rand<V, F>),
    Panic(Ref<str>),

    Copy(Rand<V, F>, R<V>),

    IsPtr(Rand<V, F>, R<V>),
    Untag(Rand<V, F>, R<V>),

    IntShow(Rand<V, F>),
    IntRead(R<V>),
    IntIsEq(Rand<V, F>, Rand<V, F>, R<V>),
    IntIsLess(Rand<V, F>, Rand<V, F>, R<V>),
    IntNegate(Rand<V, F>, R<V>),
    IntAdd(Rand<V, F>, Rand<V, F>, R<V>),
    IntSub(Rand<V, F>, Rand<V, F>, R<V>),
    IntMul(Rand<V, F>, Rand<V, F>, R<V>),
    IntDiv(Rand<V, F>, Rand<V, F>, R<V>),

    FloatShow(Rand<V, F>),
    FloatIsEq(Rand<V, F>, Rand<V, F>, R<V>),

    StrShow(Rand<V, F>),
    StrIsEq(Rand<V, F>, Rand<V, F>, R<V>),
}

#[derive(Debug, Clone)]
pub enum Rand<V, F> {
    Label(F),
    Register(R<V>),
    Int(i64),
    Real(f64),
    String(Ref<String>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum R<V> {
    R(V),
    Tmp,
    Tmp2,
}

pub struct Context<V, F> {
    standard_arg_registers: Vec<R<V>>,
    functions: HashMap<F, KnownFunction<V>>,
    gs: Arc<GensymContext>,
}

impl<V: Clone + PartialEq + Debug + Display, F: Clone + Eq + Hash + GenSym + Debug + Display>
    Context<V, F>
{
    pub fn new(
        standard_arg_registers: impl IntoIterator<Item = V>,
        gs: Arc<GensymContext>,
    ) -> Self {
        Context {
            standard_arg_registers: standard_arg_registers.into_iter().map(R::R).collect(),
            functions: Default::default(),
            gs,
        }
    }

    pub fn linearize_toplevel(&mut self, expr: &Expr<V, F>) -> Vec<Op<V, F>> {
        self.linearize(expr, vec![])
    }

    fn linearize(&mut self, expr: &Expr<V, F>, mut ops: Vec<Op<V, F>>) -> Vec<Op<V, F>> {
        match expr {
            Expr::Record(fields, var, cnt) => {
                ops.push(Op::BeginRecord(fields.len()));
                for (val, ap) in fields.iter() {
                    ops = self.linearize_access(val, ap, ops);
                }
                ops.push(Op::EndRecord(R::R(var.clone())));
                self.linearize(cnt, ops)
            }

            Expr::Select(idx, rec, var, cnt) => {
                let r = self.generate_operand(rec);
                ops.push(Op::Select(*idx, r, R::R(var.clone())));
                self.linearize(cnt, ops)
            }

            Expr::Offset(idx, rec, var, cnt) => {
                let r = self.generate_operand(rec);
                ops.push(Op::Select(*idx, r, R::R(var.clone())));
                self.linearize(cnt, ops)
            }

            Expr::App(Value::Label(f), rands) => {
                let arg_registers = self.functions[f].arg_registers.as_ref();
                ops = self.set_values(arg_registers, rands, ops);
                ops.push(Op::Tailcall(Rand::Label(f.clone())));
                ops
            }

            Expr::App(Value::Var(f), rands) => {
                ops = self.set_values(&self.standard_arg_registers, rands, ops);
                ops.push(Op::Tailcall(Rand::Register(R::R(f.clone()))));
                ops
            }

            Expr::Fix(defs, cnt) => {
                for (f, p, _) in defs.iter() {
                    self.functions.insert(f.clone(), KnownFunction::new(p));
                }

                let mut ops = self.linearize(cnt, ops);

                for (f, _, body) in defs.iter() {
                    ops.push(Op::Label(self.generate_unique_label("fix", f)));
                    ops = self.linearize(body, ops);
                }
                ops
            }

            Expr::Switch(val, cnts) => {
                let value = self.generate_operand(val);
                let labels = self.generate_unique_labels("switch", cnts.len());
                ops.push(Op::Switch(value, labels.clone()));
                for (c, lbl) in cnts.iter().zip(labels) {
                    ops.push(Op::Label(lbl));
                    ops = self.linearize(c, ops);
                }
                ops
            }

            Expr::PrimOp(PrimOp::CorP, Ref([a]), Ref([]), Ref([const_cnt, ptr_cnt])) => {
                ops.push(Op::IsPtr(self.generate_operand(a), R::Tmp));
                self.linearize_if(ptr_cnt, const_cnt, ops)
            }

            Expr::PrimOp(PrimOp::Untag, Ref([a]), Ref([var]), Ref([cnt])) => {
                ops.push(Op::Untag(self.generate_operand(a), R::R(var.clone())));
                self.linearize(cnt, ops)
            }

            Expr::PrimOp(PrimOp::INeg, Ref([a]), Ref([var]), Ref([cnt])) => {
                ops.push(Op::IntNegate(self.generate_operand(a), R::R(var.clone())));
                self.linearize(cnt, ops)
            }

            Expr::PrimOp(PrimOp::IAdd, Ref([a, b]), Ref([var]), Ref([cnt])) => {
                self.binary_primop(Op::IntAdd, a, b, var, cnt, ops)
            }

            Expr::PrimOp(PrimOp::ISub, Ref([a, b]), Ref([var]), Ref([cnt])) => {
                self.binary_primop(Op::IntSub, a, b, var, cnt, ops)
            }

            Expr::PrimOp(PrimOp::IMul, Ref([a, b]), Ref([var]), Ref([cnt])) => {
                self.binary_primop(Op::IntMul, a, b, var, cnt, ops)
            }

            Expr::PrimOp(PrimOp::IDiv, Ref([a, b]), Ref([var]), Ref([cnt])) => {
                self.binary_primop(Op::IntDiv, a, b, var, cnt, ops)
            }

            Expr::PrimOp(PrimOp::IsZero, Ref([a]), Ref([]), Ref([else_cnt, then_cnt])) => {
                ops.push(Op::IntIsEq(self.generate_operand(a), Rand::Int(0), R::Tmp));
                self.linearize_if(then_cnt, else_cnt, ops)
            }

            Expr::PrimOp(PrimOp::ISame, Ref([a, b]), Ref([]), Ref([else_cnt, then_cnt])) => {
                ops.push(Op::IntIsEq(
                    self.generate_operand(a),
                    self.generate_operand(b),
                    R::Tmp,
                ));
                self.linearize_if(then_cnt, else_cnt, ops)
            }

            Expr::PrimOp(PrimOp::ILess, Ref([a, b]), Ref([]), Ref([else_cnt, then_cnt])) => {
                ops.push(Op::IntIsLess(
                    self.generate_operand(a),
                    self.generate_operand(b),
                    R::Tmp,
                ));
                self.linearize_if(then_cnt, else_cnt, ops)
            }

            Expr::PrimOp(PrimOp::FSame, Ref([a, b]), Ref([]), Ref([else_cnt, then_cnt])) => {
                ops.push(Op::FloatIsEq(
                    self.generate_operand(a),
                    self.generate_operand(b),
                    R::Tmp,
                ));
                self.linearize_if(then_cnt, else_cnt, ops)
            }

            Expr::PrimOp(PrimOp::SSame, Ref([a, b]), Ref([]), Ref([else_cnt, then_cnt])) => {
                ops.push(Op::StrIsEq(
                    self.generate_operand(a),
                    self.generate_operand(b),
                    R::Tmp,
                ));
                self.linearize_if(then_cnt, else_cnt, ops)
            }

            Expr::PrimOp(PrimOp::ShowInt, Ref([a]), Ref([var]), Ref([cnt])) => {
                let a_ = self.generate_operand(a);
                ops.push(Op::IntShow(a_.clone()));
                ops.push(Op::Copy(a_, R::R(var.clone())));
                self.linearize(cnt, ops)
            }

            Expr::PrimOp(PrimOp::ShowReal, Ref([a]), Ref([var]), Ref([cnt])) => {
                let a_ = self.generate_operand(a);
                ops.push(Op::FloatShow(a_.clone()));
                ops.push(Op::Copy(a_, R::R(var.clone())));
                self.linearize(cnt, ops)
            }

            Expr::PrimOp(PrimOp::ShowStr, Ref([a]), Ref([var]), Ref([cnt])) => {
                let a_ = self.generate_operand(a);
                ops.push(Op::StrShow(a_.clone()));
                ops.push(Op::Copy(a_, R::R(var.clone())));
                self.linearize(cnt, ops)
            }

            Expr::PrimOp(PrimOp::ReadInt, Ref([_]), Ref([var]), Ref([cnt])) => {
                ops.push(Op::IntRead(R::R(var.clone())));
                self.linearize(cnt, ops)
            }

            Expr::Halt(value) => {
                ops.push(Op::Halt(self.generate_operand(value)));
                ops
            }

            Expr::Panic(msg) => {
                ops.push(Op::Panic(*msg));
                ops
            }

            _ => todo!("{expr:?}"),
        }
    }

    fn binary_primop(
        &mut self,
        op: impl Fn(Rand<V, F>, Rand<V, F>, R<V>) -> Op<V, F>,
        a: &Value<V, F>,
        b: &Value<V, F>,
        var: &V,
        cnt: &Expr<V, F>,
        mut ops: Vec<Op<V, F>>,
    ) -> Vec<Op<V, F>> {
        ops.push(op(
            self.generate_operand(a),
            self.generate_operand(b),
            R::R(var.clone()),
        ));
        self.linearize(cnt, ops)
    }

    fn linearize_if(
        &mut self,
        then_cnt: &Expr<V, F>,
        else_cnt: &Expr<V, F>,
        mut ops: Vec<Op<V, F>>,
    ) -> Vec<Op<V, F>> {
        let then_label = self.generate_unique_label("if", "then");
        let else_label = self.generate_unique_label("if", "else");
        ops.push(Op::If(
            Rand::Register(R::Tmp),
            then_label.clone(),
            else_label.clone(),
        ));
        ops.push(Op::Label(else_label));
        ops = self.linearize(else_cnt, ops);
        ops.push(Op::Label(then_label));
        self.linearize(then_cnt, ops)
    }

    fn generate_operand(&self, value: &Value<V, F>) -> Rand<V, F> {
        match value {
            Value::Int(i) => Rand::Int(*i),
            Value::Real(r) => Rand::Real(*r),
            Value::String(s) => Rand::String(*s),
            Value::Var(v) => Rand::Register(R::R(v.clone())),
            Value::Label(v) => Rand::Label(v.clone()),
        }
    }

    fn generate_unique_label(&mut self, prefix: impl Display, suffix: impl Display) -> F {
        self.gs.gensym2(prefix, suffix)
    }

    fn generate_unique_labels(&mut self, prefix: impl Display, n: usize) -> Vec<F> {
        (0..n).map(|_| self.gs.gensym(&prefix)).collect()
    }

    fn linearize_access(
        &self,
        value: &Value<V, F>,
        ap: &AccessPath,
        ops: Vec<Op<V, F>>,
    ) -> Vec<Op<V, F>> {
        let val = self.generate_operand(value);
        let (val, mut ops) = self.linearize_access_(val, ap, ops);
        ops.push(Op::PushRecord(val));
        ops
    }

    fn linearize_access_(
        &self,
        value: Rand<V, F>,
        ap: &AccessPath,
        mut ops: Vec<Op<V, F>>,
    ) -> (Rand<V, F>, Vec<Op<V, F>>) {
        match ap {
            AccessPath::Ref(0) => (value, ops),
            AccessPath::Ref(i) => {
                ops.push(Op::Offset(*i, value, R::Tmp2));
                (Rand::Register(R::Tmp2), ops)
            }
            AccessPath::Sel(i, ap) => {
                let (value_, mut ops) = self.linearize_access_(value, ap, ops);
                ops.push(Op::Select(*i, value_, R::Tmp2));
                (Rand::Register(R::Tmp2), ops)
            }
        }
    }

    fn set_values(
        &self,
        targets: &[R<V>],
        values: &[Value<V, F>],
        mut ops: Vec<Op<V, F>>,
    ) -> Vec<Op<V, F>> {
        let mut pending_copies: Vec<_> = Default::default();

        for (tgt, v) in targets.iter().zip(values) {
            match v {
                Value::Var(r) => {
                    let r = R::R(r.clone());
                    if &r != tgt {
                        pending_copies.push((r, tgt.clone()));
                    }
                }
                _ => {
                    ops.push(Op::Copy(self.generate_operand(v), tgt.clone()));
                }
            }
        }

        let actual_copies = Self::shuffle_registers(pending_copies);

        for (src, tgt) in actual_copies {
            ops.push(Op::Copy(Rand::Register(src), tgt))
        }

        ops
    }

    fn shuffle_registers(mut pending_copies: Vec<(R<V>, R<V>)>) -> Vec<(R<V>, R<V>)> {
        let mut actual_copies = vec![];

        while pending_copies.len() > 0 {
            // copy into all unoccupied target registers
            let mut i = 0;
            while i < pending_copies.len() {
                let (_, tgt) = &pending_copies[i];
                if pending_copies.iter().find(|(s, _)| s == tgt).is_none() {
                    let (src, tgt) = pending_copies.swap_remove(i);
                    actual_copies.push((src.clone(), tgt.clone()));

                    // make src available as target by replacing all other occurrences of src
                    for (s, _) in pending_copies.iter_mut() {
                        if s == &src {
                            *s = tgt.clone();
                        }
                    }
                    i = 0;
                } else {
                    i += 1;
                }
            }

            if pending_copies.len() > 0 {
                assert!(pending_copies.iter().find(|(s, _)| s == &R::Tmp).is_none());

                let (src, tgt) = pending_copies.pop().unwrap();
                actual_copies.push((tgt.clone(), R::Tmp));
                actual_copies.push((src.clone(), tgt.clone()));
                // make src available as target by replacing all other occurrences of src
                for (s, _) in pending_copies.iter_mut() {
                    if s == &src {
                        *s = tgt.clone();
                    }
                }
                // make tgt available as target by replacing all its source occurrences
                for (s, _) in pending_copies.iter_mut() {
                    if s == &tgt {
                        *s = R::Tmp;
                    }
                }
            }
        }
        actual_copies
    }
}

struct KnownFunction<V> {
    arg_registers: Vec<R<V>>,
}

impl<V: Clone> KnownFunction<V> {
    fn new(params: &[V]) -> Self {
        KnownFunction {
            arg_registers: params.into_iter().cloned().map(R::R).collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check_shuffler(input: &[(&str, &str)]) {
        let inputs: Vec<_> = input.iter().map(|(s, t)| (R::R(*s), R::R(*t))).collect();
        let assignments = Context::<&str, &str>::shuffle_registers(inputs.clone());

        let mut outputs: HashMap<_, _> =
            inputs.iter().map(|(s, _)| (s.clone(), s.clone())).collect();
        for (src, tgt) in assignments {
            let val = outputs[&src].clone();
            outputs.insert(tgt, val);
        }
        let outputs: HashMap<_, _> = inputs
            .iter()
            .map(|(_, t)| (t.clone(), outputs.remove(t).unwrap()))
            .collect();

        let expected: HashMap<_, _> = inputs.into_iter().map(|(s, t)| (t, s)).collect();

        assert_eq!(outputs, expected);
    }

    #[test]
    fn no_shuffling_to_do() {
        assert_eq!(Context::<&str, &str>::shuffle_registers(vec![]), vec![]);
    }

    #[test]
    fn shuffle_into_multiple_registers() {
        check_shuffler(&[("a", "b"), ("a", "c"), ("a", "d")]);
    }

    #[test]
    fn shuffle_cycle() {
        check_shuffler(&[("a", "b"), ("b", "c"), ("c", "a")]);
    }

    #[test]
    fn shuffle_multiple_cycle() {
        check_shuffler(&[
            ("a", "b"),
            ("b", "c"),
            ("c", "a"),
            ("d", "e"),
            ("e", "f"),
            ("f", "d"),
        ]);
    }

    #[test]
    fn shuffle_mixed() {
        check_shuffler(&[
            ("a", "b"),
            ("a", "c"),
            ("b", "a"),
            ("b", "d"),
            ("e", "f"),
            ("f", "e"),
            ("g", "g"),
        ]);
    }
}
