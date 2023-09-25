use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Value};

impl<V: Clone + PartialEq> Expr<V> {
    pub fn substitute_var(&self, var: &V, val: &Value<V>) -> Self {
        match self {
            Expr::Record(fs, r, c) => {
                let fs = fs
                    .iter()
                    .map(|(v, ap)| (v.substitute_var(var, val), ap.clone()));
                if r == var {
                    Expr::Record(Ref::array(fs.collect()), r.clone(), *c)
                } else {
                    Expr::Record(
                        Ref::array(fs.collect()),
                        r.clone(),
                        c.substitute_var(var, val).into(),
                    )
                }
            }
            Expr::App(rator, rands) => Expr::App(
                rator.substitute_var(var, val),
                rands.substitute_var(var, val),
            ),
            _ => todo!(),
        }
    }
}

impl<V: Clone + PartialEq> Value<V> {
    pub fn substitute_var(&self, var: &V, val: &Value<V>) -> Self {
        match self {
            Value::Var(v) if v == var => val.clone(),
            _ => self.clone(),
        }
    }
}

impl<V: Clone + PartialEq> Ref<[Value<V>]> {
    pub fn substitute_var(&self, var: &V, val: &Value<V>) -> Self {
        Ref::array(self.iter().map(|v| v.substitute_var(var, val)).collect())
    }
}