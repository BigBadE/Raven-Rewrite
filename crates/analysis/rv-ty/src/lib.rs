//! Type system and type inference
//!
//! This crate handles:
//! - Type representation
//! - Type inference with constraint generation
//! - Unification algorithm
//! - Type checking
//! - Trait bound checking
#![allow(
    clippy::min_ident_chars,
    reason = "Ty and TyId are conventional names in type system implementations"
)]

pub mod bounds;
pub mod context;
pub mod infer;
pub mod ty;
pub mod unify;

pub use bounds::{BoundChecker, BoundError};
pub use context::TyContext;
pub use infer::{InferenceResult, TypeInference};
pub use ty::{StructLayout, Ty, TyId, TyKind, VariantTy};
pub use unify::{UnificationError, Unifier};
