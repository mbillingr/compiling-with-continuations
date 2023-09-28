use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Value};
use std::collections::HashSet;
use std::hash::Hash;
use map_macro::hash_set;

impl<V: std::fmt::Debug + Clone + PartialEq + Eq + Hash> Expr<V> {
    pub fn free_vars(&self) -> HashSet<V> {
        match self {
            Expr::App(fun, args) => args.iter().fold(fun.free_vars(), |mut fvs, a| {fvs.extend(a.free_vars()); fvs}),
            _ => todo!("{:?}", self),
        }
    }
}

impl<V: std::fmt::Debug + Clone + PartialEq + Eq + Hash> Value<V> {
    pub fn free_vars(&self) -> HashSet<V> {
        let mut fvs = HashSet::new();
        match self {
            Value::Var(v) | Value::Label(v) => {
                fvs.insert(v.clone());
            }
            _ => {}
        }
        fvs
    }
}

#[cfg(test)]
mod tests {
    use crate::{cps_expr, cps_value};
    use super::*;

    #[test]
    fn app() {
        assert_eq!(cps_expr!((f x y)).free_vars(), hash_set!["f", "x", "y"])
    }
}
