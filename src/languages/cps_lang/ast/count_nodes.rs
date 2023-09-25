use std::collections::HashMap;
use crate::languages::cps_lang::ast::{Expr, Value};

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

pub fn inc(
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
