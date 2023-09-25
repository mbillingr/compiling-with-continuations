use crate::core::reference::Ref;
use crate::languages::common_primops::PrimOp;
use std::collections::HashMap;

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

#[derive(Debug, PartialEq)]
pub enum AccessPath {
    Ref(isize),
    Sel(isize, Ref<AccessPath>),
}

impl<V> Value<V> {
    pub fn count_nodes(&self) -> HashMap<&'static str, usize> {
        let key = match self {
            Value::Var(_) => "var",
            Value::Int(_) => "int",
            Value::Real(_) => "real",
            Value::String(_) => "string",
            Value::Halt => "halt",
        };
        inc(key, Default::default())
    }
}
impl<V> Expr<V> {
    pub fn count_nodes(&self) -> HashMap<&'static str, usize> {
        match self {
            Expr::Record(fs, _, c) => inc(
                "record",
                add(
                    c.count_nodes(),
                    fs.iter()
                        .map(|(v, _)| v)
                        .map(Value::count_nodes)
                        .reduce(add)
                        .unwrap_or_default(),
                ),
            ),
            Expr::Select(_, r, _, c) => inc("select", add(c.count_nodes(), r.count_nodes())),
            Expr::Offset(_, r, _, c) => inc("offset", add(c.count_nodes(), r.count_nodes())),
            Expr::App(rator, rands) => inc(
                "app",
                add(
                    rator.count_nodes(),
                    rands
                        .iter()
                        .map(Value::count_nodes)
                        .reduce(add)
                        .unwrap_or_default(),
                ),
            ),
            Expr::Fix(defs, body) => inc(
                "fix",
                add(
                    body.count_nodes(),
                    defs.iter()
                        .map(|(_, _, fb)| fb.count_nodes())
                        .reduce(add)
                        .unwrap_or_default(),
                ),
            ),
            Expr::Switch(v, arms) => inc(
                "switch",
                add(
                    v.count_nodes(),
                    arms.iter()
                        .map(|x| x.count_nodes())
                        .reduce(add)
                        .unwrap_or_default(),
                ),
            ),
            Expr::PrimOp(_, vs, _, c) => inc(
                "primop",
                vs.iter()
                    .map(Value::count_nodes)
                    .chain(c.iter().map(|x| x.count_nodes()))
                    .reduce(add)
                    .unwrap_or_default(),
            ),
            Expr::Panic(_) => inc("panic", Default::default()),
        }
    }
}

fn inc(
    key: &'static str,
    mut counts: HashMap<&'static str, usize>,
) -> HashMap<&'static str, usize> {
    *counts.entry(key).or_insert(0) += 1;
    counts
}

fn add(
    mut this: HashMap<&'static str, usize>,
    other: HashMap<&'static str, usize>,
) -> HashMap<&'static str, usize> {
    for (k, c) in other {
        *this.entry(k).or_insert(0) += c;
    }
    this
}
