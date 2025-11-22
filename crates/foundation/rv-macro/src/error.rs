//! Macro expansion error types

use rv_intern::Symbol;
use rv_span::FileSpan;

/// Error type for macro expansion
#[derive(Debug, Clone, thiserror::Error)]
pub enum MacroExpansionError {
    /// Macro not found
    #[error("undefined macro: {name:?}")]
    UndefinedMacro {
        /// Macro name
        name: Symbol,
        /// Source location
        span: FileSpan,
    },
    /// Recursion limit exceeded
    #[error("macro recursion limit exceeded for macro {macro_id:?}")]
    RecursionLimit {
        /// Macro ID that exceeded limit
        macro_id: crate::ast::MacroId,
        /// Source location
        span: FileSpan,
    },
    /// No rule matched the macro arguments
    #[error("no macro rule matched the provided arguments")]
    NoRuleMatched {
        /// Macro name
        name: Symbol,
        /// Number of tokens provided
        num_tokens: usize,
        /// Source location
        span: FileSpan,
    },
    /// Unbound variable in macro expansion
    #[error("unbound variable in macro expansion: {name:?}")]
    UnboundVariable {
        /// Variable name
        name: Symbol,
        /// Source location
        span: FileSpan,
    },
    /// Invalid fragment specifier
    #[error("invalid fragment: expected {expected}, found {found}")]
    InvalidFragment {
        /// Expected fragment kind
        expected: String,
        /// Found fragment kind
        found: String,
        /// Source location
        span: FileSpan,
    },
    /// Invalid macro syntax
    #[error("invalid macro syntax: {message}")]
    InvalidSyntax {
        /// Error message
        message: String,
        /// Source location
        span: FileSpan,
    },
}
