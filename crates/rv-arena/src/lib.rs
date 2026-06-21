//! Foundation: stable ids, interning, and side-tables.
//!
//! Side-tables are how analysis results stay *outside* the IR core ("decorate,
//! don't embed"): a pass produces a `SideTable<NodeId, T>` rather than mutating nodes.
use std::collections::HashMap;
use std::hash::Hash;

/// Stable identity of an IR node; the key type for [`SideTable`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct NodeId(pub u32);

/// A deduplicating interner: maps values to small integer ids and back.
#[derive(Debug, Default, Clone)]
pub struct Interner<T: Eq + Hash + Clone> {
    forward: HashMap<T, u32>,
    backward: Vec<T>,
}
impl<T: Eq + Hash + Clone> Interner<T> {
    pub fn new() -> Self {
        Self { forward: HashMap::new(), backward: Vec::new() }
    }
    pub fn intern(&mut self, value: T) -> u32 {
        if let Some(&id) = self.forward.get(&value) {
            return id;
        }
        let id = self.backward.len() as u32;
        self.backward.push(value.clone());
        self.forward.insert(value, id);
        id
    }
    pub fn resolve(&self, id: u32) -> Option<&T> {
        self.backward.get(id as usize)
    }
    pub fn len(&self) -> usize {
        self.backward.len()
    }
    pub fn is_empty(&self) -> bool {
        self.backward.is_empty()
    }
}

/// Analysis results attached to nodes, *outside* the IR core.
#[derive(Debug, Clone)]
pub struct SideTable<K: Eq + Hash + Copy, V> {
    map: HashMap<K, V>,
}
impl<K: Eq + Hash + Copy, V> SideTable<K, V> {
    pub fn new() -> Self {
        Self { map: HashMap::new() }
    }
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.map.insert(key, value)
    }
    pub fn get(&self, key: K) -> Option<&V> {
        self.map.get(&key)
    }
    pub fn contains(&self, key: K) -> bool {
        self.map.contains_key(&key)
    }
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.map.iter()
    }
}
impl<K: Eq + Hash + Copy, V> Default for SideTable<K, V> {
    fn default() -> Self {
        Self::new()
    }
}
