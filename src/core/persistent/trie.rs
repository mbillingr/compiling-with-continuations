use super::hamt::Hamt;
use super::RemoveResult::{NoChange, NotFound, Removed, Replaced};
use super::{RemoveResult, NODE_ARRAY_BITS};
use crate::core::persistent;
use std::borrow::Borrow;
use std::hash::Hash;
use std::rc::Rc;

/// A node in an hash array mapped trie
#[derive(Debug, Eq)]
pub enum Trie<K, T> {
    Leaf(Rc<(K, T)>),
    Node(Hamt<K, T>),
}

impl<K, T> Trie<K, T> {
    pub fn leaf(k: K, v: T) -> Self {
        Trie::Leaf(Rc::new((k, v)))
    }

    pub fn len(&self) -> usize {
        match self {
            Trie::Leaf(_) => 1,
            Trie::Node(hamt) => hamt.len(),
        }
    }

    pub fn is_leaf(&self) -> bool {
        match self {
            Trie::Leaf(_) => true,
            Trie::Node(_) => false,
        }
    }
}

impl<K: Eq + Hash, T> Trie<K, T> {
    pub fn remove<Q: ?Sized>(&self, key: &Q, k: u64) -> RemoveResult<K, T>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self {
            Trie::Leaf(rc) if rc.0.borrow() == key => Removed,
            Trie::Leaf(_) => return NotFound,
            Trie::Node(child) => child.remove_from_node(key, k >> NODE_ARRAY_BITS),
        }
    }

    pub fn merge(&self, other: &Self, depth: u32) -> Option<Self> {
        match (self, other) {
            (Trie::Leaf(a), Trie::Leaf(b)) if a.0 == b.0 => Some(other.clone()),
            (Trie::Leaf(a), Trie::Leaf(b)) => Some(persistent::split(
                self.clone(),
                persistent::hash(&a.0) >> depth,
                other.clone(),
                persistent::hash(&b.0) >> depth,
            )),
            (Trie::Leaf(a), Trie::Node(b)) => Some(
                b._insert(
                    a.clone(),
                    persistent::hash(&a.0) >> depth,
                    depth + NODE_ARRAY_BITS,
                    false,
                )
                .map_or_else(|| other.clone(), Trie::Node),
            ),
            (Trie::Node(a), Trie::Leaf(b)) => a
                ._insert(
                    b.clone(),
                    persistent::hash(&b.0) >> depth,
                    depth + NODE_ARRAY_BITS,
                    true,
                )
                .map(Trie::Node),
            (Trie::Node(a), Trie::Node(b)) => a._merge(b, depth),
        }
    }

    pub fn intersect<U>(&self, other: &Trie<K, U>, depth: u32) -> Option<Self> {
        match (self, other) {
            (Trie::Leaf(a), Trie::Leaf(b)) if a.0 == b.0 => Some(self.clone()),
            (Trie::Leaf(_), Trie::Leaf(_)) => None,
            (Trie::Leaf(a), Trie::Node(b)) => b
                .get(&a.0, persistent::hash(&a.0) >> depth)
                .map(|_| self.clone()),
            (Trie::Node(a), Trie::Leaf(b)) => a
                .get(&b.0, persistent::hash(&b.0) >> depth)
                .cloned()
                .map(Trie::Leaf),
            (Trie::Node(a), Trie::Node(b)) => a._intersect(b, depth),
        }
    }

    pub fn difference<U>(&self, other: &Trie<K, U>, depth: u32) -> Option<Self> {
        match (self, other) {
            (Trie::Leaf(a), Trie::Leaf(b)) if a.0 == b.0 => None,
            (Trie::Leaf(_), Trie::Leaf(_)) => Some(self.clone()),
            (Trie::Leaf(a), Trie::Node(b)) => match b.get(&a.0, persistent::hash(&a.0) >> depth) {
                None => Some(self.clone()),
                Some(_) => None,
            },
            (Trie::Node(a), Trie::Leaf(b)) => {
                match a.remove_from_node(&b.0, persistent::hash(&b.0) >> depth) {
                    NotFound => Some(self.clone()),
                    Removed => None,
                    NoChange => todo!(),
                    Replaced(a_) => Some(a_),
                }
            }
            (Trie::Node(a), Trie::Node(b)) => a._difference(b, depth),
        }
    }

    pub fn symmetric_difference(&self, other: &Self, depth: u32) -> Option<Self> {
        match (self, other) {
            (Trie::Leaf(a), Trie::Leaf(b)) if a.0 == b.0 => None,
            (Trie::Leaf(a), Trie::Leaf(b)) => Some(persistent::split(
                self.clone(),
                persistent::hash(&a.0) >> depth,
                other.clone(),
                persistent::hash(&b.0) >> depth,
            )),
            (Trie::Leaf(a), Trie::Node(b)) => {
                let k = persistent::hash(&a.0) >> depth;
                match b.remove_from_node(&a.0, k) {
                    NotFound => b
                        ._insert(a.clone(), k, depth + NODE_ARRAY_BITS, false)
                        .map(Trie::Node),
                    Removed => None,
                    NoChange => todo!(),
                    Replaced(b_) => Some(b_),
                }
            }
            (Trie::Node(a), Trie::Leaf(b)) => {
                let k = persistent::hash(&b.0);
                match a.remove_from_node(&b.0, k >> depth) {
                    NotFound => {
                        let c = a
                            ._insert(b.clone(), k >> depth, depth + NODE_ARRAY_BITS, false)
                            .map(Trie::Node);
                        c
                    }
                    Removed => None,
                    NoChange => todo!(),
                    Replaced(a_) => Some(a_),
                }
            }
            (Trie::Node(a), Trie::Node(b)) => a._symmetric_difference(b, depth),
        }
    }
}

impl<K, T> Clone for Trie<K, T> {
    fn clone(&self) -> Self {
        match self {
            Trie::Leaf(rc) => Trie::Leaf(rc.clone()),
            Trie::Node(hamt) => Trie::Node(hamt.clone()),
        }
    }
}

impl<K: PartialEq, T: PartialEq> PartialEq for Trie<K, T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Trie::Leaf(a), Trie::Leaf(b)) => a == b,
            (Trie::Node(a), Trie::Node(b)) => a == b,
            _ => false,
        }
    }
}
