//! Indexed arena allocator for AST nodes
//!
//! This is a re-export of `la-arena` which is used by rust-analyzer
//! and provides a robust, well-tested arena implementation.

pub use la_arena::{Arena, ArenaMap, Idx};
