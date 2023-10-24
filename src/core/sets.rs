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
    where
        T: Borrow<Q>,
    {
        self.0.contains(elem)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }

    pub fn pop(self) -> Option<T> {
        self.0.into_iter().next()
    }

    pub fn add(&self, elem: T) -> Self {
        let mut set = self.0.clone();
        set.insert(elem);
        Set(set)
    }

    pub fn remove<Q: Hash + Eq>(&self, elem: &Q) -> Self
    where
        T: Borrow<Q>,
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

impl<V: Eq + Hash> From<HashSet<V>> for Set<V> {
    fn from(elems: HashSet<V>) -> Self {
        Set(elems)
    }
}

impl<V: Eq + Hash> From<Vec<V>> for Set<V> {
    fn from(elems: Vec<V>) -> Self {
        Set(elems.into_iter().collect())
    }
}

impl<V: Eq + Hash> FromIterator<V> for Set<V> {
    fn from_iter<T: IntoIterator<Item = V>>(iter: T) -> Self {
        Set(FromIterator::<V>::from_iter(iter))
    }
}

#[macro_export]
macro_rules! set {
    () => {{
        $crate::core::sets::Set::empty()
    }};

    ($($x:expr),* $(,)?) => {{
        let mut set = std::collections::HashSet::new();
        $(set.insert($x);)*
        $crate::core::sets::Set::from(set)
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
