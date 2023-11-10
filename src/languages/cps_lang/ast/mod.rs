mod accessors;
mod check_bindings_unique;
mod collect_functions;
mod compute;
mod count_nodes;
mod deser;
mod free_vars;
mod free_vars_nofns;
mod pretty_print;
mod size;
mod substitute;
mod transform;

use crate::core::reference::Ref;
use crate::languages::common_primops::PrimOp;
pub use compute::{Computation, Compute};
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

impl AccessPath {
    pub fn preselect(&self, path: &[isize]) -> Self {
        match (self, path) {
            (AccessPath::Ref(0), []) => AccessPath::Ref(0),
            (AccessPath::Ref(0), [p]) => AccessPath::Sel(*p, Ref::new(AccessPath::Ref(0))),
            (AccessPath::Ref(0), [ps @ .., p]) => {
                AccessPath::Sel(*p, Ref::new(AccessPath::Ref(0).preselect(ps)))
            }
            (AccessPath::Ref(_), _) => unimplemented!(),
            (AccessPath::Sel(i, ap), _) => AccessPath::Sel(*i, Ref::new(ap.preselect(path))),
        }
    }
}
