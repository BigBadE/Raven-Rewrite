//! Macro expansion error types

use rv_intern::Symbol;
use rv_span::FileSpan;

/// Error type for macro expansion
#[derive(Debug, Clone, thiserror::Error)]
pub enum MacroExpansionError {
    /// Macro not found
    #[error("undefined macro `{name:?}` at {span:?}. {}", .suggestion.as_deref().unwrap_or("Check the macro name and ensure it is imported"))]
    UndefinedMacro {
        /// Macro name
        name: Symbol,
        /// Source location
        span: FileSpan,
        /// Suggestion for similar macros
        suggestion: Option<String>,
    },
    /// Recursion limit exceeded
    #[error("macro recursion limit exceeded (depth {depth}) for macro {macro_id:?} at {span:?}. Consider reducing nesting or increasing the limit")]
    RecursionLimit {
        /// Macro ID that exceeded limit
        macro_id: crate::ast::MacroId,
        /// Current recursion depth
        depth: usize,
        /// Source location
        span: FileSpan,
    },
    /// No rule matched the macro arguments
    #[error("no macro rule matched the provided arguments for `{name:?}` ({num_tokens} tokens) at {span:?}. {}", format_rule_expectations(.expected_patterns))]
    NoRuleMatched {
        /// Macro name
        name: Symbol,
        /// Number of tokens provided
        num_tokens: usize,
        /// Source location
        span: FileSpan,
        /// Expected patterns (from the macro definition)
        expected_patterns: Vec<String>,
    },
    /// Unbound variable in macro expansion
    #[error("unbound variable `{name:?}` in macro expansion at {span:?}. {}", format_unbound_suggestion(.available_vars))]
    UnboundVariable {
        /// Variable name
        name: Symbol,
        /// Source location
        span: FileSpan,
        /// Available variables in scope
        available_vars: Vec<Symbol>,
    },
    /// Invalid fragment specifier
    #[error("invalid fragment at {span:?}: expected {expected}, found {found}. {help}")]
    InvalidFragment {
        /// Expected fragment kind
        expected: String,
        /// Found fragment kind
        found: String,
        /// Source location
        span: FileSpan,
        /// Help message
        help: String,
    },
    /// Invalid macro syntax
    #[error("invalid macro syntax at {span:?}: {message}")]
    InvalidSyntax {
        /// Error message
        message: String,
        /// Source location
        span: FileSpan,
    },
    /// Ambiguous macro match
    #[error("ambiguous macro invocation at {span:?}: multiple rules could match. Rules: {}", .matching_rules.join(", "))]
    AmbiguousMatch {
        /// Macro name
        name: Symbol,
        /// Source location
        span: FileSpan,
        /// Rules that matched
        matching_rules: Vec<String>,
    },
    /// Missing required argument
    #[error("missing required argument `{arg_name}` for macro `{macro_name:?}` at {span:?}. Expected position: {position}")]
    MissingArgument {
        /// Macro name
        macro_name: Symbol,
        /// Argument name
        arg_name: String,
        /// Expected position
        position: usize,
        /// Source location
        span: FileSpan,
    },
    /// Invalid repetition
    #[error("invalid repetition in macro at {span:?}: {message}. {help}")]
    InvalidRepetition {
        /// Error message
        message: String,
        /// Source location
        span: FileSpan,
        /// Help message
        help: String,
    },
    /// Feature gate required
    #[error("macro feature `{feature}` is unstable at {span:?}. Add #![feature({feature})] to enable")]
    FeatureGateRequired {
        /// Feature name
        feature: String,
        /// Source location
        span: FileSpan,
    },
}

/// Format the expected patterns for a NoRuleMatched error
fn format_rule_expectations(patterns: &[String]) -> String {
    if patterns.is_empty() {
        return "Check the macro definition for valid patterns".to_string();
    }
    if patterns.len() == 1 {
        return format!("Expected pattern: {}", patterns[0]);
    }
    format!(
        "Expected one of {} patterns:\n  {}",
        patterns.len(),
        patterns.join("\n  ")
    )
}

/// Format the suggestion for an unbound variable
fn format_unbound_suggestion(available: &[Symbol]) -> String {
    if available.is_empty() {
        return "No variables are available in the current expansion scope".to_string();
    }
    format!(
        "Available variables: {:?}",
        available
    )
}

impl MacroExpansionError {
    /// Create an UndefinedMacro error without a suggestion
    pub fn undefined_macro(name: Symbol, span: FileSpan) -> Self {
        Self::UndefinedMacro {
            name,
            span,
            suggestion: None,
        }
    }

    /// Create an UndefinedMacro error with a suggestion
    pub fn undefined_macro_with_suggestion(
        name: Symbol,
        span: FileSpan,
        suggestion: String,
    ) -> Self {
        Self::UndefinedMacro {
            name,
            span,
            suggestion: Some(suggestion),
        }
    }

    /// Create a NoRuleMatched error without expected patterns
    pub fn no_rule_matched(name: Symbol, num_tokens: usize, span: FileSpan) -> Self {
        Self::NoRuleMatched {
            name,
            num_tokens,
            span,
            expected_patterns: Vec::new(),
        }
    }

    /// Create a NoRuleMatched error with expected patterns
    pub fn no_rule_matched_with_patterns(
        name: Symbol,
        num_tokens: usize,
        span: FileSpan,
        expected_patterns: Vec<String>,
    ) -> Self {
        Self::NoRuleMatched {
            name,
            num_tokens,
            span,
            expected_patterns,
        }
    }

    /// Create a RecursionLimit error
    pub fn recursion_limit(
        macro_id: crate::ast::MacroId,
        depth: usize,
        span: FileSpan,
    ) -> Self {
        Self::RecursionLimit {
            macro_id,
            depth,
            span,
        }
    }

    /// Create an UnboundVariable error
    pub fn unbound_variable(name: Symbol, span: FileSpan, available_vars: Vec<Symbol>) -> Self {
        Self::UnboundVariable {
            name,
            span,
            available_vars,
        }
    }

    /// Create an InvalidFragment error with a help message
    pub fn invalid_fragment(
        expected: impl Into<String>,
        found: impl Into<String>,
        span: FileSpan,
        help: impl Into<String>,
    ) -> Self {
        Self::InvalidFragment {
            expected: expected.into(),
            found: found.into(),
            span,
            help: help.into(),
        }
    }

    /// Create an InvalidRepetition error
    pub fn invalid_repetition(
        message: impl Into<String>,
        span: FileSpan,
        help: impl Into<String>,
    ) -> Self {
        Self::InvalidRepetition {
            message: message.into(),
            span,
            help: help.into(),
        }
    }

    /// Get the source span for this error
    #[must_use]
    pub const fn span(&self) -> FileSpan {
        match self {
            Self::UndefinedMacro { span, .. }
            | Self::RecursionLimit { span, .. }
            | Self::NoRuleMatched { span, .. }
            | Self::UnboundVariable { span, .. }
            | Self::InvalidFragment { span, .. }
            | Self::InvalidSyntax { span, .. }
            | Self::AmbiguousMatch { span, .. }
            | Self::MissingArgument { span, .. }
            | Self::InvalidRepetition { span, .. }
            | Self::FeatureGateRequired { span, .. } => *span,
        }
    }

    /// Check if this error is recoverable (expansion can continue)
    #[must_use]
    pub const fn is_recoverable(&self) -> bool {
        matches!(
            self,
            Self::InvalidSyntax { .. } | Self::FeatureGateRequired { .. }
        )
    }

    /// Get a short description of the error category
    #[must_use]
    pub const fn category(&self) -> &'static str {
        match self {
            Self::UndefinedMacro { .. } => "undefined macro",
            Self::RecursionLimit { .. } => "recursion limit",
            Self::NoRuleMatched { .. } => "no matching rule",
            Self::UnboundVariable { .. } => "unbound variable",
            Self::InvalidFragment { .. } => "invalid fragment",
            Self::InvalidSyntax { .. } => "syntax error",
            Self::AmbiguousMatch { .. } => "ambiguous match",
            Self::MissingArgument { .. } => "missing argument",
            Self::InvalidRepetition { .. } => "invalid repetition",
            Self::FeatureGateRequired { .. } => "feature gate required",
        }
    }
}
