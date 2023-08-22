use crate::core::reference::Ref;

pub mod ast;


pub enum Value<V:'static> {
    Var(V),
    Label(V),
    Int(i64),
    Real(f64),
    String(Ref<String>)
}

type List<T> = Ref<[T]>;

pub enum Expr<V: 'static> {
    Record(List<Value<V>>, V, Ref<Expr<V>>),
    Select(isize, Value<V>, V, Ref<Expr<V>>),
    Offset(isize, Value<V>, V, Ref<Expr<V>>),
    App(Value<V>, List<Value<V>>),
    Fix(List<(V, List<V>, Expr<V>)>, Ref<Expr<V>>),
    Switch(Value<V>, List<Expr<V>>),
    PrimOp(PrimOp, List<Value<V>>, List<V>, List<Expr<V>>)
}

pub enum PrimOp {}