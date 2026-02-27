//! HIR lowering - converts CST to HIR with name resolution
//!
//! This crate handles:
//! - Scope tree construction
//! - Symbol table management
//! - Name resolution across scopes and modules
//! - CST → HIR lowering

pub mod lower;
pub mod scope;
pub mod symbol;

pub use lower::{lower_source_file, lower_source_file_with_id_offset, LoweringContext};
pub use scope::{Scope, ScopeData, ScopeId, ScopeTree};
pub use symbol::{Symbol, SymbolId, SymbolKind, SymbolTable};
