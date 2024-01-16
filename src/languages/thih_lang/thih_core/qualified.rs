use super::predicates::Pred;
use super::substitutions::{Subst, Types};
use super::types::Tyvar;
use crate::core::lists::eq_union;
use std::fmt::{Debug, Formatter};

/// A qualified type is restricted by a list of predicates.
#[derive(Clone, PartialEq)]
pub struct Qual<T>(pub Vec<Pred>, pub T);

impl<T: Debug> Debug for Qual<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} :=> {:?}", self.0, self.1)
    }
}

impl<T: Types> Types for Qual<T> {
    fn apply_subst(&self, s: &Subst) -> Self {
        Qual(s.apply(&self.0), s.apply(&self.1))
    }

    fn tv(&self) -> Vec<Tyvar> {
        eq_union(self.0.tv(), self.1.tv())
    }
}
