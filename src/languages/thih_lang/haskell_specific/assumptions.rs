use super::super::thih_core::scheme::Scheme;
use super::super::thih_core::substitutions::{Subst, Types};
use super::super::thih_core::types::Tyvar;
use super::super::{Id, Result};
use crate::core::persistent::PersistentMap;

/// Represent assumptions about the type of a variables by pairing
/// a variable name with a type scheme.
#[derive(Clone)]
pub struct Assumptions(PersistentMap<Id, Scheme>);

impl Assumptions {
    pub fn empty() -> Self {
        Assumptions(PersistentMap::new())
    }

    pub fn single(i: impl Into<Id>, sc: impl Into<Scheme>) -> Self {
        Self::empty().insert(i, sc)
    }

    pub fn insert(&self, i: impl Into<Id>, sc: impl Into<Scheme>) -> Self {
        Assumptions(self.0.insert(i.into(), sc.into()))
    }

    pub fn extend(&self, more: &Self) -> Self {
        Assumptions(self.0.merge(&more.0))
    }

    pub fn extend_from(&self, it: impl Iterator<Item = (Id, Scheme)>) -> Self {
        let mut map = self.0.clone();
        for (i, sc) in it {
            map = map.insert(i, sc);
        }
        Assumptions(map)
    }
}

impl Types for Assumptions {
    fn apply_subst(&self, s: &Subst) -> Self {
        Assumptions(self.0.map(&|i, sc| s.apply(sc)))
    }

    fn tv(&self) -> Vec<Tyvar> {
        let mut tvs = vec![];
        for sc in self.0.values() {
            for u in sc.tv() {
                if !tvs.contains(&u) {
                    tvs.push(u)
                }
            }
        }
        tvs
    }
}

pub fn find<'a>(i: &Id, ass: &'a Assumptions) -> Result<&'a Scheme> {
    ass.0
        .get(i)
        .ok_or_else(|| format!("unbound identifier: {i}"))
}

impl FromIterator<(Id, Scheme)> for Assumptions {
    fn from_iter<T: IntoIterator<Item = (Id, Scheme)>>(iter: T) -> Self {
        Self::empty().extend_from(iter.into_iter())
    }
}
