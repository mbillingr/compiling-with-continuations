use super::persistent_map::{self, PersistentMap};
use std::borrow::Borrow;
use std::fmt::{Debug, Formatter};
use std::hash::Hash;

#[derive(Clone, Default, Eq, PartialEq)]
pub struct PersistentSet<T>(PersistentMap<T, ()>);

impl<T> PersistentSet<T> {
    #[inline]
    pub fn new() -> Self {
        PersistentSet(PersistentMap::new())
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Fast comparison, returns `true` if two sets are the *same*.
    /// This is faster than structural comparison (`eq`, `==`) but less precise. If `ptr_eq` returns `true`,
    /// both sets are guaranteed to be equal. However, if it returns `false`, they may still be equal.
    ///
    /// # Examples
    ///
    /// ```
    /// let a = set!["x", "y"];
    /// let b = set!["x", "y"];
    ///
    /// assert!(a.ptr_eq(&a));
    /// assert!(b.ptr_eq(&b));
    /// assert!(!a.ptr_eq(&b));
    ///
    /// assert!(a.eq(&b));
    /// ```   
    #[inline]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        self.0.ptr_eq(&other.0)
    }

    /// An iterator visiting all key/value pairs in arbitrary order.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.keys()
    }
}

impl<T: Hash + Eq> PersistentSet<T> {
    #[inline]
    pub fn contains<Q: ?Sized>(&self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.0.get_key_value(key).is_some()
    }

    #[inline]
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.0.get_key_value(key).map(|(k, _)| k)
    }

    #[inline]
    pub fn insert(&self, key: T) -> Self {
        PersistentSet(self.0.insert(key, ()))
    }

    #[inline]
    pub fn remove<Q: ?Sized>(&self, key: &Q) -> Option<Self>
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.0.remove(key).map(Self)
    }

    #[inline]
    pub fn union(&self, other: &Self) -> Self {
        PersistentSet(self.0.merge(&other.0))
    }

    #[inline]
    pub fn intersection(&self, other: &Self) -> Self {
        PersistentSet(self.0.intersect(&other.0))
    }

    #[inline]
    pub fn difference(&self, other: &Self) -> Self {
        PersistentSet(self.0.difference(&other.0))
    }

    #[inline]
    pub fn symmetric_difference(&self, other: &Self) -> Self {
        PersistentSet(self.0.symmetric_difference(&other.0))
    }

    /// Create a new subset with elements selected by a predicate
    #[inline]
    pub fn filter(&self, f: &impl Fn(&T) -> bool) -> Self
    where
        T: Clone,
    {
        PersistentSet(self.0.filter(&|k, _| f(k)))
    }
}

impl<T: Debug> Debug for PersistentSet<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<T> From<PersistentMap<T, ()>> for PersistentSet<T> {
    fn from(map: PersistentMap<T, ()>) -> Self {
        PersistentSet(map)
    }
}

impl<T> From<PersistentSet<T>> for PersistentMap<T, ()> {
    fn from(set: PersistentSet<T>) -> Self {
        set.0
    }
}

impl<T: Eq + Hash> FromIterator<T> for PersistentSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        PersistentSet(iter.into_iter().map(|k| (k, ())).collect())
    }
}

impl<'a, T: Eq + Hash> IntoIterator for &'a PersistentSet<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter(self.0.iter())
    }
}

pub struct Iter<'a, T>(persistent_map::Iter<'a, T, ()>);

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k)
    }
}
