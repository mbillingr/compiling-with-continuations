use crate::core::reference::Ref;

#[derive(Debug)]
pub enum Expr<V: 'static> {
    Var(V),
    Fn(V, Ref<Expr<V>>),
    Fix(Ref<[V]>, Ref<[Expr<V>]>, Ref<Expr<V>>),
    App(Ref<Expr<V>>, Ref<Expr<V>>),
    Int(i64),
    Real(f64),
    String(Ref<str>),
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

#[derive(Debug)]
pub enum ConRep {
    Undecided,
    Tagged(usize),
    Constant(i64),
    Transparent,
    Cell,
}

#[derive(Debug)]
pub enum Con {
    Data(ConRep),
    Int(i64),
    Real(f64),
    String(Ref<str>),
}

#[derive(Debug)]
pub enum PrimOp {
    INeg,
    ISub,
}
