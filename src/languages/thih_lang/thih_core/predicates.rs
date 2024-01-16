use super::substitutions::{Subst, Types};
use super::types::{Type, Tyvar};
use super::unification::{matches, mgu};
use super::{Id, Result};

/// A predicate imposes constraints on types
#[derive(Clone, Debug, PartialEq)]
pub enum Pred {
    /// Assert that the type (2nd field) is a member of class (1st field)  
    IsIn(Id, Type),
}

impl Types for Pred {
    fn apply_subst(&self, s: &Subst) -> Self {
        match self {
            Pred::IsIn(i, t) => Pred::IsIn(i.clone(), s.apply(t)),
        }
    }

    fn tv(&self) -> Vec<Tyvar> {
        match self {
            Pred::IsIn(_, t) => t.tv(),
        }
    }
}

impl Pred {
    /// test if a predicate is in head-normal form
    pub fn in_hnf(&self) -> bool {
        fn hnf(t: &Type) -> bool {
            match t {
                Type::TVar(_) => true,
                Type::TCon(_) => false,
                Type::TApp(app) => hnf(&app.0),
                Type::TGen(_) => panic!("don't know what to do!"),
            }
        }

        match self {
            Pred::IsIn(_, t) => hnf(t),
        }
    }
}

pub fn mgu_pred(a: &Pred, b: &Pred) -> Result<Subst> {
    lift(mgu, a, b)
}

pub fn match_pred(a: &Pred, b: &Pred) -> Result<Subst> {
    lift(matches, a, b)
}

fn lift(m: impl Fn(&Type, &Type) -> Result<Subst>, a: &Pred, b: &Pred) -> Result<Subst> {
    match (a, b) {
        (Pred::IsIn(i1, t1), Pred::IsIn(i2, t2)) if i1 == i2 => m(t1, t2),
        _ => Err("classes differ")?,
    }
}
