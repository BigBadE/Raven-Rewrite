//! Type ID foundation
//!
//! This crate provides the type ID type used throughout the compiler.
//! It's a separate crate to avoid circular dependencies between rv-hir and rv-ty.

#![allow(clippy::min_ident_chars, reason = "TyId is a conventional name")]

use serde::{Deserialize, Serialize};

// Re-export for convenience
pub use la_arena::Idx;

/// Opaque type for type IDs
///
/// This is a newtype wrapper to prevent direct construction.
/// Types must be allocated through TyContext.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyIdInner;

/// Type ID - index into the type arena
///
/// This is the single source of truth for types throughout the entire compiler.
/// After type checking, all HIR/MIR/LIR nodes store TyId directly.
pub type TyId = Idx<TyIdInner>;

/// Export for serialization
impl Serialize for TyIdInner {
    fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        unreachable!("TyIdInner should never be serialized directly")
    }
}

impl<'de> Deserialize<'de> for TyIdInner {
    fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        unreachable!("TyIdInner should never be deserialized directly")
    }
}
