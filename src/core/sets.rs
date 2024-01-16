pub use crate::core::persistent::PersistentSet as Set;
use std::borrow::Borrow;
use std::collections::HashSet;
use std::hash::Hash;

impl<T: Clone + Eq + Hash> Set<T> {
    pub fn empty() -> Self {
        Set::new()
    }

    pub fn singleton(elem: T) -> Self {
        Self::empty().add(elem)
    }

    pub fn get_any(&self) -> Option<&T> {
        self.iter().next()
    }

    pub fn add(&self, elem: T) -> Self {
        self.insert(elem)
    }

    pub fn sub<Q: Hash + Eq>(&self, elem: &Q) -> Self
    where
        T: Borrow<Q>,
        T: Clone,
    {
        self.remove(elem).unwrap_or_else(|| self.clone())
    }
}

impl<V: Eq + Hash> From<HashSet<V>> for Set<V> {
    fn from(elems: HashSet<V>) -> Self {
        Self::from_iter(elems.into_iter())
    }
}

impl<V: Eq + Hash> From<Vec<V>> for Set<V> {
    fn from(elems: Vec<V>) -> Self {
        Self::from_iter(elems.into_iter())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::set;

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
