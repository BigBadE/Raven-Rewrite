//! HIR lowering - converts CST to HIR with name resolution
//!
//! This crate handles:
//! - Scope tree construction
//! - Symbol table management
//! - Name resolution across scopes and modules
//! - CST → HIR lowering

pub mod scope;
pub mod symbol;
pub mod lower;

pub use scope::{Scope, ScopeData, ScopeId, ScopeTree};
pub use symbol::{Symbol, SymbolTable, SymbolId, SymbolKind};
pub use lower::{LoweringContext, lower_source_file};
