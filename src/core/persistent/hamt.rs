use super::trie::Trie;
use super::RemoveResult::{NoChange, NotFound, Removed, Replaced};
use super::{RemoveResult, NODE_ARRAY_BITS, NODE_ARRAY_MASK};
use crate::core::persistent;
use std::borrow::Borrow;
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::rc::Rc;

/// A Hash array mapped trie node
#[derive(Eq)]
pub struct Hamt<K, T> {
    mapping: u32,
    subtrie: Rc<[Trie<K, T>]>,
}

impl<K: Debug, T: Debug> Debug for Hamt<K, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Hamt({:032b}: {:?}", self.mapping, self.subtrie)
    }
}

impl<K, T> Hamt<K, T> {
    pub fn new(mapping: u32, children: Vec<Trie<K, T>>) -> Self {
        Hamt {
            mapping,
            subtrie: children.into(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.mapping == 0
    }

    pub fn len(&self) -> usize {
        self.subtrie.iter().map(Trie::len).sum()
    }

    pub fn leaves(&self) -> LeafIterator<K, T> {
        LeafIterator::new(&self.subtrie)
    }

    pub fn map<U>(&self, f: &impl Fn(&K, &T) -> U) -> Hamt<K, U>
    where
        K: Clone,
    {
        Hamt {
            mapping: self.mapping,
            subtrie: self
                .subtrie
                .iter()
                .map(|trie| match trie {
                    Trie::Leaf(rc) => Trie::leaf(rc.0.clone(), f(&rc.0, &rc.1)),
                    Trie::Node(hamt) => Trie::Node(hamt.map(f)),
                })
                .collect(),
        }
    }

    #[inline]
    pub fn ptr_eq<U>(&self, other: &Hamt<K, U>) -> bool {
        if Rc::as_ptr(&self.subtrie) as *const u8 == Rc::as_ptr(&other.subtrie) as *const u8 {
            debug_assert_eq!(self.mapping, other.mapping);
            true
        } else {
            false
        }
    }

    pub fn combine<U>(
        &self,
        other: &Hamt<K, U>,
        depth: u32,
        node_from_self: impl Fn(&Trie<K, T>) -> Option<Trie<K, T>>,
        node_from_other: impl Fn(&Trie<K, U>) -> Option<Trie<K, T>>,
        node_from_both: impl Fn(&Trie<K, T>, &Trie<K, U>, u32) -> Option<Trie<K, T>>,
    ) -> Option<Trie<K, T>> {
        let mut mapping = 0;
        let mut subtrie = vec![];

        for ((m, t1), (m2, t2)) in self.slots().zip(other.slots()) {
            debug_assert_eq!(m, m2);
            let res_child = match (t1, t2) {
                (None, None) => None,
                (Some(a), None) => node_from_self(a),
                (None, Some(b)) => node_from_other(b),
                (Some(a), Some(b)) => node_from_both(a, b, depth + NODE_ARRAY_BITS),
            };

            if let Some(node) = res_child {
                mapping |= m;
                subtrie.push(node);
            }
        }

        build_trie(mapping, subtrie)
    }

    pub fn filter(&self, f: &impl Fn(&K, &T) -> bool) -> Self {
        match self._filter(f, true) {
            NoChange => self.clone(),
            Replaced(Trie::Node(root)) => root,
            _ => unreachable!(),
        }
    }

    pub fn _filter(&self, f: &impl Fn(&K, &T) -> bool, is_root: bool) -> RemoveResult<K, T> {
        let mut mapping = 0;
        let mut subtrie: Vec<Trie<_, _>> = vec![];
        let mut any_changes = false;

        for (m, t) in self.slots() {
            match t {
                None => continue,

                Some(node @ Trie::Leaf(rc)) => {
                    if f(&rc.0, &rc.1) {
                        mapping |= m;
                        subtrie.push(node.clone());
                    } else {
                        any_changes = true;
                    }
                }

                Some(node @ Trie::Node(hamt)) => match hamt._filter(f, false) {
                    NotFound => unreachable!(),
                    NoChange => {
                        mapping |= m;
                        subtrie.push(node.clone());
                    }
                    Removed => any_changes = true,
                    Replaced(node) => {
                        mapping |= m;
                        subtrie.push(node.clone());
                        any_changes = true;
                    }
                },
            }
        }

        if any_changes {
            match (is_root, subtrie.len()) {
                (false, 0) => Removed,
                (false, 1) if subtrie[0].is_leaf() => subtrie.pop().map(Replaced).unwrap(),
                _ => Replaced(Trie::Node(Hamt {
                    mapping,
                    subtrie: subtrie.into(),
                })),
            }
        } else {
            NoChange
        }
    }

    fn slots(&self) -> impl Iterator<Item = (u32, Option<&Trie<K, T>>)> {
        let mut children = self.subtrie.iter();
        (0..32).map(|idx| 1 << idx).map(move |bm| {
            (
                bm,
                if self.is_free(bm) {
                    None
                } else {
                    children.next()
                },
            )
        })
    }

    #[inline]
    fn is_free(&self, mask_bit: u32) -> bool {
        self.mapping & mask_bit == 0
    }
}

impl<K: Eq + Hash, T> Hamt<K, T> {
    pub fn get<Q: ?Sized>(&self, key: &Q, k: u64) -> Option<&Rc<(K, T)>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let (mask_bit, idx_) = self.hash_location(k);

        if self.is_free(mask_bit) {
            return None;
        }

        match &self.subtrie[idx_] {
            Trie::Leaf(rc) if rc.0.borrow() == key => Some(rc),
            Trie::Leaf(_) => None,
            Trie::Node(child) => child.get(key, k >> NODE_ARRAY_BITS),
        }
    }

    #[inline]
    pub fn insert(&self, key: K, val: T, k: u64) -> Self {
        self._insert(Rc::new((key, val)), k, NODE_ARRAY_BITS, true)
            .unwrap()
    }

    pub fn _insert(
        &self,
        leaf: Rc<(K, T)>,
        k: u64,
        depth: u32,
        replace_existing: bool,
    ) -> Option<Self> {
        let (mask_bit, idx_) = self.hash_location(k);

        let subtrie = if self.is_free(mask_bit) {
            // free slot
            insert(idx_, Trie::Leaf(leaf), &self.subtrie).into()
        } else {
            // occupied slot
            let new_child = match &self.subtrie[idx_] {
                Trie::Leaf(rc) if rc.0 == leaf.0 => {
                    if replace_existing {
                        Trie::Leaf(leaf)
                    } else {
                        return None;
                    }
                }
                old_leaf @ Trie::Leaf(rc) => persistent::split(
                    Trie::Leaf(leaf),
                    k >> NODE_ARRAY_BITS,
                    old_leaf.clone(),
                    persistent::hash(&rc.0) >> depth,
                ),
                Trie::Node(child) => Trie::Node(child._insert(
                    leaf,
                    k >> NODE_ARRAY_BITS,
                    depth + NODE_ARRAY_BITS,
                    replace_existing,
                )?),
            };
            replace(idx_, new_child, &self.subtrie).into()
        };
        Some(Hamt {
            mapping: self.mapping | mask_bit,
            subtrie,
        })
    }

    pub fn remove_from_root<Q: ?Sized>(&self, key: &Q, k: u64) -> Option<Self>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let (mask_bit, idx_) = self.hash_location(k);

        if self.is_free(mask_bit) {
            return None;
        }

        // we always keep the root array, even if it's empty
        match self.subtrie[idx_].remove(key, k) {
            NotFound => None,
            NoChange => todo!(),
            Removed => Some(self.remove_child(mask_bit, idx_)),
            Replaced(new_child) => Some(self.replace_child(idx_, new_child)),
        }
    }
    pub fn remove_from_node<Q: ?Sized>(&self, key: &Q, k: u64) -> RemoveResult<K, T>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let (mask_bit, idx_) = self.hash_location(k);

        if self.is_free(mask_bit) {
            return NotFound;
        }

        match self.subtrie[idx_].remove(key, k) {
            NotFound => NotFound,

            NoChange => todo!(),

            Removed => match self.subtrie.len() {
                0 => unreachable!(),
                1 => Removed, // this non-root node just became empty, so we can remove it
                2 if self.subtrie[1 - idx_].is_leaf() => {
                    // if the only remaining child is a leaf we can replace this non-root node with it
                    Replaced(self.subtrie[1 - idx_].clone())
                }
                _ => Replaced(Trie::Node(self.remove_child(mask_bit, idx_))),
            },

            Replaced(new_child) => {
                match self.subtrie.len() {
                    0 => unreachable!(),
                    1 if new_child.is_leaf() => {
                        // if the only remaining child is a leaf we can replace this non-root node with it
                        Replaced(new_child)
                    }
                    _ => Replaced(Trie::Node(self.replace_child(idx_, new_child))),
                }
            }
        }
    }

    pub fn merge(&self, other: &Self) -> Self {
        Self::make_root(self._merge(other, 0))
    }

    pub fn _merge(&self, other: &Self, depth: u32) -> Option<Trie<K, T>> {
        if self.ptr_eq(other) {
            return Some(Trie::Node(self.clone()));
        }

        self.combine(
            other,
            depth,
            |a| Some(a.clone()),
            |b| Some(b.clone()),
            Trie::merge,
        )
    }

    pub fn intersect<U>(&self, other: &Hamt<K, U>) -> Self {
        Self::make_root(self._intersect(other, 0))
    }

    pub fn _intersect<U>(&self, other: &Hamt<K, U>, depth: u32) -> Option<Trie<K, T>> {
        if self.ptr_eq(other) {
            return Some(Trie::Node(self.clone()));
        }

        self.combine(other, depth, |_| None, |_| None, Trie::intersect)
    }

    pub fn difference<U>(&self, other: &Hamt<K, U>) -> Self {
        Self::make_root(self._difference(other, 0))
    }

    pub fn _difference<U>(&self, other: &Hamt<K, U>, depth: u32) -> Option<Trie<K, T>> {
        if self.ptr_eq(other) {
            return None;
        }

        self.combine(
            other,
            depth,
            |a| Some(a.clone()),
            |_| None,
            Trie::difference,
        )
    }

    pub fn symmetric_difference(&self, other: &Self) -> Self {
        Self::make_root(self._symmetric_difference(other, 0))
    }

    pub fn _symmetric_difference(&self, other: &Self, depth: u32) -> Option<Trie<K, T>> {
        if self.ptr_eq(other) {
            return None;
        }

        self.combine(
            other,
            depth,
            |a| Some(a.clone()),
            |b| Some(b.clone()),
            Trie::symmetric_difference,
        )
    }

    fn make_root(trie: Option<Trie<K, T>>) -> Hamt<K, T> {
        match trie {
            None => Self::new(0, vec![]),
            Some(Trie::Node(hamt)) => hamt,
            Some(Trie::Leaf(rc)) => {
                let k = persistent::hash(&rc.0);
                Hamt::new(0, vec![])
                    ._insert(rc, k, NODE_ARRAY_BITS, true)
                    .unwrap()
            }
        }
    }

    #[inline]
    fn hash_location(&self, k: u64) -> (u32, usize) {
        let idx = k & NODE_ARRAY_MASK;
        let mask_bit: u32 = 1 << idx;
        let idx_ = u32::count_ones(self.mapping & (mask_bit - 1)) as usize;
        (mask_bit, idx_)
    }

    fn replace_child(&self, idx: usize, child: Trie<K, T>) -> Self {
        Hamt {
            mapping: self.mapping,
            subtrie: replace(idx, child, &self.subtrie).into(),
        }
    }

    fn remove_child(&self, mask_bit: u32, idx: usize) -> Self {
        Hamt {
            mapping: self.mapping & !mask_bit,
            subtrie: remove(idx, &self.subtrie).into(),
        }
    }
}

impl<K, T> Clone for Hamt<K, T> {
    fn clone(&self) -> Self {
        Hamt {
            mapping: self.mapping,
            subtrie: self.subtrie.clone(),
        }
    }
}

impl<K: PartialEq, T: PartialEq> PartialEq for Hamt<K, T> {
    fn eq(&self, other: &Self) -> bool {
        if self.mapping != other.mapping {
            return false;
        }

        self.subtrie
            .iter()
            .zip(other.subtrie.iter())
            .all(|(a, b)| a == b)
    }
}

fn build_trie<K, T>(mapping: u32, mut subtrie: Vec<Trie<K, T>>) -> Option<Trie<K, T>> {
    match subtrie.len() {
        0 => None,
        1 if subtrie[0].is_leaf() => subtrie.pop(),
        _ => Some(Trie::Node(Hamt {
            mapping,
            subtrie: subtrie.into(),
        })),
    }
}

fn insert<T: Clone>(idx: usize, x: T, xs: &[T]) -> Vec<T> {
    let mut res = Vec::with_capacity(xs.len() + 1);
    let mut xs = xs.iter().cloned();
    for _ in 0..idx {
        res.push(xs.next().unwrap());
    }
    res.push(x);
    res.extend(xs);
    res
}

fn replace<T: Clone>(idx: usize, x: T, xs: &[T]) -> Vec<T> {
    let mut res = xs.to_vec();
    res[idx] = x;
    res
}

fn remove<T: Clone>(idx: usize, xs: &[T]) -> Vec<T> {
    let mut res = Vec::with_capacity(xs.len() - 1);
    let mut xs = xs.iter().cloned();
    for _ in 0..idx {
        res.push(xs.next().unwrap());
    }
    xs.next();
    res.extend(xs);
    res
}

pub struct LeafIterator<'a, K, T> {
    stack: Vec<(usize, &'a Rc<[Trie<K, T>]>)>,
}

impl<'a, K, T> LeafIterator<'a, K, T> {
    pub fn new(root: &'a Rc<[Trie<K, T>]>) -> Self {
        LeafIterator {
            stack: vec![(0, root)],
        }
    }
}

impl<'a, K, T> Iterator for LeafIterator<'a, K, T> {
    type Item = &'a Rc<(K, T)>;

    fn next(&mut self) -> Option<Self::Item> {
        let (idx, arr) = self.stack.pop()?;
        if idx >= arr.len() {
            return self.next();
        }
        self.stack.push((idx + 1, arr));
        match &arr[idx] {
            Trie::Node(hamt) => {
                self.stack.push((0, &hamt.subtrie));
                self.next()
            }
            Trie::Leaf(rc) => Some(rc),
        }
    }
}
