use crate::core::reference::Ref;
use crate::core::sets::Set;
use crate::languages::cps_lang::ast::compute::{Computation, Compute};
use crate::languages::cps_lang::ast::{Expr, Value};
use map_macro::hash_set;
use std::collections::HashSet;
use std::hash::Hash;

impl<'e, V: Clone + Eq + Hash> Compute<'e, V, V> for FreeVars<V> {
    fn visit_expr(&mut self, expr: &'e Expr<V, V>) -> Computation {
        match expr {
            Expr::Fix(defs, cnt) => {
                for (_, params, body) in defs.iter() {
                    body.compute(self);
                    for p in params.iter() {
                        // This is not 100% correct. If p was free in another function we should
                        // not remove it. Only if all names are unique, this is no problem.
                        self.0.remove(p);
                    }
                }

                cnt.compute(self);

                for (f, _, _) in defs.iter() {
                    self.0.remove(f);
                }

                Computation::Done
            }
            _ => Computation::Continue,
        }
    }

    fn visit_value(&mut self, value: &Value<V, V>) {
        if let Value::Var(v) | Value::Label(v) = value {
            self.0.insert(v.clone());
        }
    }

    fn post_visit_expr(&mut self, expr: &Expr<V, V>) {
        match expr {
            Expr::Record(_, var, _) | Expr::Select(_, _, var, _) | Expr::Offset(_, _, var, _) => {
                self.0.remove(var);
            }
            Expr::PrimOp(_, _, vars, _) => {
                for v in vars.iter() {
                    self.0.remove(v);
                }
            }
            _ => {}
        }
    }
}

impl<V: Clone + Eq + Hash> Expr<V> {
    pub fn free_vars(&self) -> FreeVars<V> {
        let mut fvs = FreeVars::empty();
        self.compute(&mut fvs);
        fvs
    }

    pub fn fix_function_free_vars(&self) -> FreeVars<V> {
        match self {
            Expr::Fix(defs, _) => FreeVars::empty()
                .merge(defs.iter().map(|(_, p, b)| Self::function_free_vars(p, b)))
                .without_these(defs.iter().map(|(f, _, _)| f)),
            _ => panic!("Expected fix"),
        }
    }

    pub fn function_free_vars(params: &Ref<[V]>, body: &Expr<V>) -> FreeVars<V> {
        body.free_vars().without_these(params.iter())
    }
}

impl<V: Clone + PartialEq + Eq + Hash> Value<V> {
    pub fn free_vars(&self) -> FreeVars<V> {
        let mut fvs = FreeVars::empty();
        self.compute(&mut fvs);
        fvs
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

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
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

    pub fn iter(&self) -> impl Iterator<Item = &V> {
        self.0.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = V> {
        self.0.into_iter()
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

impl<V: Eq + Hash> From<FreeVars<V>> for Set<V> {
    fn from(value: FreeVars<V>) -> Self {
        let tmp: HashSet<_> = value.into();
        tmp.into()
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

    #[test]
    fn label_in_halt() {
        assert_eq!(cps_expr!(halt (@ f)).free_vars(), hash_set!["f"].into());
    }
}
