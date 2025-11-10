//! Macro expansion system for Raven
//!
//! This crate provides macro expansion capabilities including:
//! - Declarative macros (macro_rules!)
//! - Builtin macros (println!, vec!, assert!)
//! - Basic hygiene (via scoping)
//!
//! # Architecture
//!
//! The macro system works in several phases:
//!
//! 1. **Parsing**: Macro definitions are parsed from source code
//! 2. **Registration**: Macros are registered in the expansion context
//! 3. **Expansion**: Macro invocations are expanded to token streams
//! 4. **Re-parsing**: Expanded tokens are re-parsed as HIR
//!
//! # Example
//!
//! ```rust,ignore
//! use rv_macro::{MacroExpansionContext, MacroDef, MacroKind, BuiltinMacroKind};
//!
//! let mut ctx = MacroExpansionContext::new(interner);
//!
//! // Register builtin macros
//! ctx.register_macro(MacroDef {
//!     id: MacroId(0),
//!     name: interner.intern("println"),
//!     kind: MacroKind::Builtin {
//!         expander: BuiltinMacroKind::Println,
//!     },
//!     span: FileSpan::default(),
//! });
//!
//! // Expand macro
//! let expanded = ctx.expand_macro(
//!     interner.intern("println"),
//!     arguments,
//!     span,
//! )?;
//! ```

pub mod ast;
pub mod builtins;
pub mod error;
pub mod expand;

// Re-export commonly used types
pub use ast::{
    BuiltinMacroKind, Delimiter, FragmentKind, LiteralKind, MacroDef, MacroExpander, MacroId,
    MacroKind, MacroMatcher, MacroRule, SequenceKind, Token, TokenStream,
};
pub use error::MacroExpansionError;
pub use expand::MacroExpansionContext;
