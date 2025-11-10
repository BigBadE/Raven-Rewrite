//! Name resolution for Raven
//!
//! This crate provides a dedicated name resolution pass that runs after HIR lowering
//! and before type inference. It builds a scope tree, resolves all variable references
//! to their definitions, and catches name resolution errors early.
//!
//! # Architecture
//!
//! The name resolution pass consists of:
//! - **Scope tree**: Tracks all scopes and their parent relationships
//! - **Name resolver**: Walks the HIR, defines names, and resolves references
//! - **Resolution errors**: Undefined names, duplicate definitions, and visibility violations
//!
//! # Usage
//!
//! ```rust,ignore
//! use rv_resolve::NameResolver;
//!
//! let result = NameResolver::resolve(&body, &function, &interner);
//! if !result.errors.is_empty() {
//!     // Handle resolution errors
//! }
//! // Use result.resolutions for type inference
//! ```

pub mod error;
pub mod resolver;
pub mod scope;

pub use error::ResolutionError;
pub use resolver::{NameResolver, ResolutionResult};
pub use scope::{Resolution, Scope, ScopeId, ScopeKind, ScopeTree};
