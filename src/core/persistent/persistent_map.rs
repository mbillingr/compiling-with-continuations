use super::hamt::{Hamt, LeafIterator};
use crate::core::persistent;
use std::borrow::Borrow;
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::ops::Index;

#[derive(Eq, PartialEq)]
pub struct PersistentMap<K, T>(Hamt<K, T>);

impl<K, T> PersistentMap<K, T> {
    #[inline]
    pub fn new() -> Self {
        PersistentMap(Hamt::new(0, vec![]))
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Fast comparison, returns `true` if two maps are the *same*.
    /// This is faster than structural comparison (`eq`, `==`) but less precise. If `ptr_eq` returns `true`,
    /// both maps are guaranteed to be equal. However, if it returns `false`, they may still be equal.
    ///
    /// # Examples
    ///
    /// ```
    /// let a = map!["x" => 1, "y" => 2];
    /// let b = map!["x" => 1, "y" => 2];
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
    pub fn iter(&self) -> Iter<K, T> {
        Iter(self.0.leaves())
    }

    /// An iterator visiting all keys pairs in arbitrary order.
    #[inline]
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.0.leaves().map(|rc| &rc.0)
    }

    /// An iterator visiting all values pairs in arbitrary order.
    #[inline]
    pub fn values(&self) -> impl Iterator<Item = &T> {
        self.0.leaves().map(|rc| &rc.1)
    }

    /// Create a new map with transformed values
    #[inline]
    pub fn map<U>(&self, f: &impl Fn(&K, &T) -> U) -> PersistentMap<K, U>
    where
        K: Clone,
    {
        PersistentMap(self.0.map(f))
    }

    /// Create a new map with selected entries
    #[inline]
    pub fn filter(&self, f: &impl Fn(&K, &T) -> bool) -> Self {
        PersistentMap(self.0.filter(f))
    }
}

impl<K: Hash + Eq, T> PersistentMap<K, T> {
    #[inline]
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&T>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.get_key_value(key).map(|(_, v)| v)
    }

    #[inline]
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.get_key_value(key).is_some()
    }

    #[inline]
    pub fn get_key_value<Q: ?Sized>(&self, key: &Q) -> Option<(&K, &T)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let k = persistent::hash(&key);
        self.0.get(key, k).map(|rc| (&rc.0, &rc.1))
    }

    #[inline]
    pub fn insert(&self, key: K, val: T) -> Self {
        let k = persistent::hash(&key);
        let hamt = self.0.insert(key, val, k);
        PersistentMap(hamt)
    }

    #[inline]
    pub fn remove<Q: ?Sized>(&self, key: &Q) -> Option<Self>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let k = persistent::hash(&key);
        self.0.remove_from_root(key, k).map(Self)
    }

    #[inline]
    pub fn update<Q: ?Sized>(&self, key: &Q, upd: impl Fn(&T) -> T) -> Option<Self>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
        K: Clone,
    {
        // this could be implemented more efficiently. See comment in upsert, below.
        self.get_key_value(key)
            .map(|(k, v)| self.insert(k.clone(), upd(v)))
    }

    #[inline]
    pub fn upsert(&self, key: K, upd: impl Fn(&T) -> T, default: impl FnOnce() -> T) -> Self
    where
        K: Clone,
    {
        // this could be implemented more efficiently by creating a Hamt.upsert function.
        // to avoid growth in code complexity, insert, update, and maybe remove could be
        // written as special cases of this upsert.
        match self.get(&key) {
            None => self.insert(key, default()),
            Some(v) => self.insert(key, upd(v)),
        }
    }

    /// Merge two maps.
    /// Returns a new map that contains all entries from two maps.
    /// If a key is present in both maps, the value is taken from `other`.
    #[inline]
    pub fn merge(&self, other: &Self) -> Self {
        PersistentMap(self.0.merge(&other.0))
    }

    /// Set intersection on map keys.
    /// That is, returns a new map that contains all keys that are also in another map.
    #[inline]
    pub fn intersect<U>(&self, other: &PersistentMap<K, U>) -> Self {
        PersistentMap(self.0.intersect(&other.0))
    }

    /// Set difference on map keys.
    /// That is, returns a new map that contains all keys that are not contained in another map.
    #[inline]
    pub fn difference<U>(&self, other: &PersistentMap<K, U>) -> Self {
        PersistentMap(self.0.difference(&other.0))
    }

    /// Symmetric set difference on map keys.
    /// That is, returns a new map that contains all keys that are in either map but not in both.
    #[inline]
    pub fn symmetric_difference(&self, other: &Self) -> Self {
        PersistentMap(self.0.symmetric_difference(&other.0))
    }
}

impl<K, T> Clone for PersistentMap<K, T> {
    fn clone(&self) -> Self {
        PersistentMap(self.0.clone())
    }
}

impl<K: Debug, T: Debug> Debug for PersistentMap<K, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, T> Default for PersistentMap<K, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Eq + Hash, T> FromIterator<(K, T)> for PersistentMap<K, T> {
    fn from_iter<I: IntoIterator<Item = (K, T)>>(iter: I) -> Self {
        // could this be done more efficient?
        iter.into_iter()
            .fold(PersistentMap::new(), |map, (k, v)| map.insert(k, v))
    }
}

impl<K: Eq + Hash + Borrow<Q>, Q: Eq + Hash + ?Sized, T> Index<&Q> for PersistentMap<K, T> {
    type Output = T;

    fn index(&self, key: &Q) -> &Self::Output {
        self.get(key).expect("no entry found for key")
    }
}

impl<'a, K: Eq + Hash, T> IntoIterator for &'a PersistentMap<K, T> {
    type Item = (&'a K, &'a T);
    type IntoIter = Iter<'a, K, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter(self.0.leaves())
    }
}

pub struct Iter<'a, K, V>(LeafIterator<'a, K, V>);

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|rc| (&rc.0, &rc.1))
    }
}
