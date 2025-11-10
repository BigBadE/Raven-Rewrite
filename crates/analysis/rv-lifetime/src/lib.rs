//! Lifetime analysis for the Raven compiler.
//!
//! This crate provides lifetime inference and validation to ensure memory safety.
//! It implements a simplified version of Rust's lifetime system, focusing on the
//! core infrastructure needed for basic borrow checking.
//!
//! # Architecture
//!
//! - [`Lifetime`]: Core lifetime representation (named, static, inferred)
//! - [`LifetimeContext`]: Tracks lifetime variables and constraints
//! - [`LifetimeInference`]: Infers lifetimes from function bodies
//! - [`LifetimeError`]: Type-safe error reporting for lifetime violations
//!
//! # Limitations
//!
//! This is a simplified implementation suitable for basic lifetime tracking:
//! - No subtyping variance
//! - Simplified outlives graph (no full Polonius-style analysis)
//! - Limited higher-ranked trait bounds
//!
//! # Examples
//!
//! ```rust
//! use rv_lifetime::{LifetimeContext, LifetimeInference};
//! use rv_hir::Body;
//!
//! // Infer lifetimes for a function body
//! let body = Body::default();
//! let result = LifetimeInference::infer_function(&body);
//! ```

mod context;
mod error;
mod infer;
mod lifetime;

pub use context::LifetimeContext;
pub use error::{LifetimeError, LifetimeResult};
pub use infer::LifetimeInference;
pub use lifetime::{Lifetime, LifetimeId, LifetimeParam, RegionId};
