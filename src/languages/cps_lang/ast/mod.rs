mod count_nodes;

use crate::core::reference::Ref;
use crate::languages::common_primops::PrimOp;

#[derive(Debug, PartialEq, Clone)]
pub enum Value<V: 'static> {
    Var(V),
    Int(i64),
    Real(f64),
    String(Ref<String>),
    Halt, // this represents a continuation that stops the program when called
}

type List<T> = Ref<[T]>;

#[derive(Debug, PartialEq)]
pub enum Expr<V: 'static> {
    Record(List<(Value<V>, AccessPath)>, V, Ref<Expr<V>>),
    Select(isize, Value<V>, V, Ref<Expr<V>>),
    Offset(isize, Value<V>, V, Ref<Expr<V>>),
    App(Value<V>, List<Value<V>>),
    Fix(List<(V, List<V>, Ref<Expr<V>>)>, Ref<Expr<V>>),
    Switch(Value<V>, List<Ref<Expr<V>>>),
    PrimOp(PrimOp, List<Value<V>>, List<V>, List<Ref<Expr<V>>>),
    Panic(&'static str),
}

#[derive(Debug, Clone, PartialEq)]
pub enum AccessPath {
    Ref(isize),
    Sel(isize, Ref<AccessPath>),
}
