use std::borrow::Borrow;
use std::collections::HashSet;
use std::hash::Hash;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Set<T: Eq + Hash>(HashSet<T>);

impl<T: Clone + Eq + Hash> Set<T> {
    pub fn empty() -> Self {
        Set(HashSet::new())
    }

    pub fn singleton(elem: T) -> Self {
        Self::empty().add(elem)
    }

    pub fn contains<Q: Hash + Eq>(&self, elem: &Q) -> bool
        where T: Borrow<Q>
    {
        self.0.contains(elem)
    }

    pub fn add(&self, elem: T) -> Self {
        let mut set = self.0.clone();
        set.insert(elem);
        Set(set)
    }

    pub fn remove<Q: Hash + Eq>(&self, elem: &Q) -> Self
        where T: Borrow<Q>
    {
        let mut set = self.0.clone();
        set.remove(elem);
        Set(set)
    }

    pub fn union(&self, other: &Self) -> Self {
        Set(HashSet::union(&self.0, &other.0).cloned().collect())
    }

    pub fn intersection(&self, other: &Self) -> Self {
        Set(HashSet::intersection(&self.0, &other.0).cloned().collect())
    }

    pub fn difference(&self, other: &Self) -> Self {
        Set(HashSet::difference(&self.0, &other.0).cloned().collect())
    }
}

macro_rules! set {
    ($($x:expr),* $(,)?) => {{
        let mut set = HashSet::new();
        $(set.insert($x);)*
        Set(set)
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sets() {
        assert_eq!(Set::<()>::empty(), Set::empty());
        assert_eq!(Set::singleton(1), Set::singleton(1));
        assert_eq!(set![1, 2, 3], set![2, 3, 1]);

        assert!(set![1, 2].contains(&1));
        assert!(!set![1, 2].contains(&0));

        assert_eq!(set![1, 2].union(&set![2, 3]), set![1, 2, 3]);
        assert_eq!(set![1, 2].intersection(&set![2, 3]), set![2]);
        assert_eq!(set![1, 2].difference(&set![2, 3]), set![1]);
    }
}