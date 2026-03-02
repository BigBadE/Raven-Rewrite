//! HIR lowering - converts CST to HIR with name resolution
//!
//! This crate handles:
//! - Scope tree construction
//! - Symbol table management
//! - Name resolution across scopes and modules
//! - CST → HIR lowering
//! - Core library compilation and prelude injection
//!
//! ## Core Library Support
//!
//! The core library is compiled as a proper crate dependency, not cherry-picked files.
//! The prelude (`core::prelude::v1`) is automatically injected into the root scope,
//! following Rust's behavior.

pub mod core_library;
pub mod lower;
pub mod scope;
pub mod symbol;

pub use core_library::{
    get_core_library_path, CompiledModule, CoreCompilationContext, CoreCrate, CoreLibrary,
    CoreLibraryContext, CrateModule, PreludeItemKind, PreludeReExport, ResolvedItem, UseDecl,
};
pub use lower::{lower_source_file, lower_source_file_with_id_offset, LoweringContext};
pub use scope::{Scope, ScopeData, ScopeId, ScopeTree};
pub use symbol::{Symbol, SymbolId, SymbolKind, SymbolTable};
