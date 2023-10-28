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
pub enum Value<V: 'static, F = V> {
    Var(V),
    Label(F),
    Int(i64),
    Real(f64),
    String(Ref<String>),
}

type List<T> = Ref<[T]>;

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<V: 'static, F: 'static = V> {
    Record(List<(Value<V, F>, AccessPath)>, V, Ref<Expr<V, F>>),
    Select(isize, Value<V, F>, V, Ref<Expr<V, F>>),
    Offset(isize, Value<V, F>, V, Ref<Expr<V, F>>),
    App(Value<V, F>, List<Value<V, F>>),
    Fix(List<(F, List<V>, Ref<Expr<V, F>>)>, Ref<Expr<V, F>>),
    Switch(Value<V, F>, List<Ref<Expr<V, F>>>),
    PrimOp(PrimOp, List<Value<V, F>>, List<V>, List<Ref<Expr<V, F>>>),
    Halt(Value<V, F>),
    Panic(Ref<str>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum AccessPath {
    Ref(isize),
    Sel(isize, Ref<AccessPath>),
}
