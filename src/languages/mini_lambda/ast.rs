use crate::core::reference::Ref;
use crate::languages::common_primops;

#[derive(Debug, Clone)]
pub enum Expr<V: 'static> {
    Var(V),
    Fn(V, Ref<Expr<V>>),
    Fix(Ref<[V]>, Ref<[Expr<V>]>, Ref<Expr<V>>),
    App(Ref<Expr<V>>, Ref<Expr<V>>),
    Int(i64),
    Real(f64),
    String(Ref<String>),
    Switch(
        Ref<Expr<V>>,
        Ref<[ConRep]>,
        Ref<[(Con, Expr<V>)]>,
        Option<Ref<Expr<V>>>,
    ),
    Con(ConRep, Ref<Expr<V>>),
    DeCon(ConRep, Ref<Expr<V>>),
    Record(Ref<[Expr<V>]>),
    Select(isize, Ref<Expr<V>>),
    Prim(PrimOp),
}

#[derive(Debug, Copy, Clone)]
pub enum ConRep {
    Tagged(usize),
    Constant(usize),
    Transparent,
}

#[derive(Debug, Copy, Clone)]
pub enum Con {
    Data(ConRep),
    Int(i64),
    Real(f64),
    String(Ref<str>),
}

#[derive(Debug, Copy, Clone)]
pub enum PrimOp {
    Unary(common_primops::Unary),
    Binary(common_primops::Binary),
}
