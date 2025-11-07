//! Indexed arena allocator for AST nodes

use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

/// Type-safe index into an arena
pub struct Idx<T> {
    raw: u32,
    _phantom: PhantomData<fn() -> T>,
}

impl<T> Copy for Idx<T> {}

impl<T> Clone for Idx<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> PartialEq for Idx<T> {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}

impl<T> Eq for Idx<T> {}

impl<T> std::hash::Hash for Idx<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

impl<T> std::fmt::Debug for Idx<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Idx").field(&self.raw).finish()
    }
}

/// Arena allocator
pub struct Arena<T> {
    data: Vec<T>,
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }

    pub fn alloc(&mut self, value: T) -> Idx<T> {
        let idx = self.data.len() as u32;
        self.data.push(value);
        Idx {
            raw: idx,
            _phantom: PhantomData,
        }
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = (Idx<T>, &T)> {
        self.data.iter().enumerate().map(|(idx, value)| {
            (
                Idx {
                    raw: idx as u32,
                    _phantom: PhantomData,
                },
                value,
            )
        })
    }
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Index<Idx<T>> for Arena<T> {
    type Output = T;

    fn index(&self, idx: Idx<T>) -> &T {
        &self.data[idx.raw as usize]
    }
}

impl<T> IndexMut<Idx<T>> for Arena<T> {
    fn index_mut(&mut self, idx: Idx<T>) -> &mut T {
        &mut self.data[idx.raw as usize]
    }
}
