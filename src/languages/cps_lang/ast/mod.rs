mod accessors;
mod check_bindings_unique;
mod count_nodes;
mod deser;
mod free_vars;
mod pretty_print;
mod substitute;
mod transform;

use crate::core::reference::Ref;
use crate::languages::common_primops::PrimOp;
pub use transform::{Transform, Transformed};

#[derive(Debug, PartialEq, Clone)]
pub enum Value<V: 'static> {
    Var(V),
    Label(V),
    Int(i64),
    Real(f64),
    String(Ref<String>),
}

type List<T> = Ref<[T]>;

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<V: 'static> {
    Record(List<(Value<V>, AccessPath)>, V, Ref<Expr<V>>),
    Select(isize, Value<V>, V, Ref<Expr<V>>),
    Offset(isize, Value<V>, V, Ref<Expr<V>>),
    App(Value<V>, List<Value<V>>),
    Fix(List<(V, List<V>, Ref<Expr<V>>)>, Ref<Expr<V>>),
    Switch(Value<V>, List<Ref<Expr<V>>>),
    PrimOp(PrimOp, List<Value<V>>, List<V>, List<Ref<Expr<V>>>),
    Halt(Value<V>),
    Panic(Ref<str>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum AccessPath {
    Ref(isize),
    Sel(isize, Ref<AccessPath>),
}
