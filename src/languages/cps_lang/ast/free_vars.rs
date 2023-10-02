use crate::core::reference::Ref;
use crate::languages::cps_lang::ast::{Expr, Value};
use map_macro::hash_set;
use std::collections::HashSet;
use std::hash::Hash;

impl<V: std::fmt::Debug + Clone + PartialEq + Eq + Hash> Expr<V> {
    pub fn free_vars(&self) -> FreeVars<V> {
        match self {
            Expr::Record(fields, r, cnt) => cnt
                .free_vars()
                .without(r)
                .merge_values(fields.iter().map(|(x, _)| x)),

            Expr::Select(_, r, x, cnt) | Expr::Offset(_, r, x, cnt) => {
                cnt.free_vars().without(x).union(r.free_vars())
            }

            Expr::App(fun, args) => fun.free_vars().merge_values(args.iter()),

            Expr::Fix(defs, body) => body
                .free_vars()
                .union(self.fix_function_free_vars())
                .merge(defs.iter().map(|(_, p, b)| Self::function_free_vars(p, b)))
                .without_these(defs.iter().map(|(f, _, _)| f)),

            Expr::Switch(cond, cnts) => cond.free_vars().merge_exprs(cnts.iter().map(|x| &**x)),

            Expr::PrimOp(_, args, xs, cnts) => {
                let mut fvs = FreeVars::empty().merge_exprs(cnts.iter().map(|x| &**x));
                for x in xs.iter() {
                    fvs = fvs.without(x)
                }
                fvs.merge_values(args.iter())
            }

            Expr::Panic(_) => FreeVars::empty(),
        }
    }

    pub fn fix_function_free_vars(&self) -> FreeVars<V> {
        match self {
            Expr::Fix(defs, body) => FreeVars::empty()
                .merge(defs.iter().map(|(_, p, b)| Self::function_free_vars(p, b)))
                .without_these(defs.iter().map(|(f, _, _)| f)),
            _ => panic!("Expected fix"),
        }
    }

    pub fn function_free_vars(params: &Ref<[V]>, body: &Expr<V>) -> FreeVars<V> {
        body.free_vars().without_these(params.iter())
    }
}

impl<V: std::fmt::Debug + Clone + PartialEq + Eq + Hash> Value<V> {
    pub fn free_vars(&self) -> FreeVars<V> {
        match self {
            Value::Var(v) | Value::Label(v) => FreeVars::singleton(v.clone()),
            _ => FreeVars::empty(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct FreeVars<V: Eq + Hash>(HashSet<V>);

impl<V: Eq + Hash> FreeVars<V> {
    pub fn empty() -> Self {
        FreeVars(HashSet::new())
    }
    pub fn singleton(v: V) -> Self {
        FreeVars(hash_set![v])
    }

    pub fn without(mut self, v: &V) -> Self {
        self.0.remove(v);
        self
    }

    pub fn union(mut self, other: Self) -> Self {
        self.0.extend(other.0);
        self
    }

    pub fn merge(self, fvs: impl Iterator<Item = Self>) -> Self {
        fvs.fold(self, Self::union)
    }

    pub fn iter(&self) -> impl Iterator<Item=&V> {
        self.0.iter()
    }
}
impl<V: Eq + Hash + 'static> FreeVars<V> {
    pub fn without_these<'a>(mut self, vs: impl Iterator<Item = &'a V>) -> Self {
        for v in vs {
            self = self.without(v)
        }
        self
    }
}

impl<V: std::fmt::Debug + Clone + Eq + Hash + 'static> FreeVars<V> {
    fn merge_values<'a>(self, vals: impl Iterator<Item = &'a Value<V>>) -> Self {
        self.merge(vals.map(Value::free_vars))
    }

    fn merge_exprs<'a>(self, vals: impl Iterator<Item = &'a Expr<V>>) -> Self {
        self.merge(vals.map(Expr::free_vars))
    }
}

impl<V: Eq + Hash + Clone> From<&V> for FreeVars<V> {
    fn from(value: &V) -> Self {
        FreeVars::singleton(value.clone())
    }
}

impl<V: Eq + Hash> From<HashSet<V>> for FreeVars<V> {
    fn from(value: HashSet<V>) -> Self {
        FreeVars(value)
    }
}

impl<V: Eq + Hash> Into<HashSet<V>> for FreeVars<V> {
    fn into(self) -> HashSet<V> {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        cps_expr, cps_expr_list, cps_field, cps_field_list, cps_ident_list, cps_value,
        cps_value_list,
    };

    #[test]
    fn exprs() {
        assert_eq!(
            cps_expr!((record [x (int 1)] r (f r))).free_vars(),
            hash_set!["f", "x"].into()
        );

        assert_eq!(
            cps_expr!((select 0 r x (f x))).free_vars(),
            hash_set!["f", "r"].into()
        );

        assert_eq!(
            cps_expr!((offset 0 r x (f r x))).free_vars(),
            hash_set!["f", "r"].into()
        );

        assert_eq!(
            cps_expr!((f x y)).free_vars(),
            hash_set!["f", "x", "y"].into()
        );

        assert_eq!(
            cps_expr!(fix f(x)=(g a x); g(y)=(x) in (f b)).free_vars(),
            hash_set!["a", "b", "x"].into()
        );

        assert_eq!(
            cps_expr!((switch x [(a b) (c d)])).free_vars(),
            hash_set!["x", "a", "b", "c", "d"].into()
        );

        assert_eq!(
            cps_expr!((set [a b] [x y] [(x y) (y z)])).free_vars(),
            hash_set!["a", "b", "z"].into()
        );
    }
}
