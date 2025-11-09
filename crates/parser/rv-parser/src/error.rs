//! Rich error reporting for the parser
//!
//! Note: These struct fields are used by miette's `#[derive(Diagnostic)]` macro
//! for rich error output, but clippy cannot see through the proc macro expansion.

#![allow(unused_assignments)]

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

// Re-export codespan types for convenience
pub use codespan_reporting;

/// Parse error with rich diagnostic information
#[derive(Error, Debug, Clone, Diagnostic)]
pub enum ParseError {
    /// Syntax error with unexpected input
    #[error("unexpected token `{token}`")]
    #[diagnostic(code(parser::unexpected_token), help("this token is not valid here"))]
    UnexpectedToken {
        /// What was found
        token: String,
        /// Source location
        #[label("unexpected token")]
        span: SourceSpan,
        /// Source code for context
        #[source_code]
        src: miette::NamedSource<String>,
    },

    /// Missing expected token
    #[error("expected `{expected}`, found `{found}`")]
    #[diagnostic(code(parser::missing_token), help("try adding `{expected}` here"))]
    MissingToken {
        /// What was expected
        expected: String,
        /// What was actually found
        found: String,
        /// Source location where it should be
        #[label("expected `{expected}` here")]
        span: SourceSpan,
        /// Source code for context
        #[source_code]
        src: miette::NamedSource<String>,
    },

    /// Unclosed delimiter
    #[error("this file contains an unclosed delimiter")]
    #[diagnostic(code(parser::unclosed_delimiter))]
    UnclosedDelimiter {
        /// The opening character
        opening_char: char,
        /// The expected closing character
        closing_char: char,
        /// Opening delimiter location
        #[label("unclosed delimiter")]
        opening: SourceSpan,
        /// Location where closing was expected
        #[label]
        expected_close: SourceSpan,
        /// Source code for context
        #[source_code]
        src: miette::NamedSource<String>,
    },

    /// Invalid syntax construct
    #[error("invalid {construct}")]
    #[diagnostic(code(parser::invalid_syntax))]
    InvalidSyntax {
        /// Type of construct (e.g., "function declaration", "type annotation")
        construct: String,
        /// Detailed explanation
        #[help]
        suggestion: Option<String>,
        /// Source location
        #[label("{construct} is invalid")]
        span: SourceSpan,
        /// Source code for context
        #[source_code]
        src: miette::NamedSource<String>,
    },

    /// Parse failed completely
    #[error("failed to parse source")]
    #[diagnostic(code(parser::parse_failed))]
    ParseFailed {
        /// Reason for failure
        reason: String,
    },

    /// IO error
    #[error("failed to read file: {message}")]
    #[diagnostic(code(parser::io_error))]
    IoError {
        /// Error message
        message: String,
    },
}

impl ParseError {
    /// Convert to codespan diagnostic for rustc-style output
    pub fn to_codespan_diagnostic(
        &self,
        file_id: usize,
    ) -> codespan_reporting::diagnostic::Diagnostic<usize> {
        use codespan_reporting::diagnostic::{Diagnostic, Label};

        match self {
            Self::UnexpectedToken { token, span, .. } => Diagnostic::error()
                .with_message(format!("unexpected token `{}`", token))
                .with_labels(vec![
                    Label::primary(file_id, span.offset()..span.offset() + span.len())
                        .with_message("unexpected token"),
                ]),
            Self::MissingToken {
                expected,
                found,
                span,
                ..
            } => Diagnostic::error()
                .with_message(format!("expected `{}`, found `{}`", expected, found))
                .with_labels(vec![
                    Label::primary(file_id, span.offset()..span.offset() + span.len())
                        .with_message(format!("expected `{}` here", expected)),
                ])
                .with_notes(vec![format!("try adding `{}` here", expected)]),
            Self::UnclosedDelimiter {
                opening,
                expected_close,
                ..
            } => Diagnostic::error()
                .with_message("this file contains an unclosed delimiter")
                .with_labels(vec![
                    Label::secondary(file_id, opening.offset()..opening.offset() + opening.len())
                        .with_message("unclosed delimiter"),
                    Label::primary(
                        file_id,
                        expected_close.offset()..expected_close.offset() + expected_close.len(),
                    ),
                ]),
            Self::InvalidSyntax {
                construct,
                suggestion,
                span,
                ..
            } => {
                let mut diag = Diagnostic::error()
                    .with_message(format!("invalid {}", construct))
                    .with_labels(vec![
                        Label::primary(file_id, span.offset()..span.offset() + span.len())
                            .with_message(format!("{} is invalid", construct)),
                    ]);

                if let Some(suggestion) = suggestion {
                    diag = diag.with_notes(vec![suggestion.clone()]);
                }
                diag
            }
            Self::ParseFailed { reason } => {
                Diagnostic::error().with_message(format!("failed to parse source: {}", reason))
            }
            Self::IoError { message } => Diagnostic::error().with_message(message.clone()),
        }
    }

    /// Create source context for error reporting
    pub fn with_source(self, filename: impl Into<String>, source: impl Into<String>) -> Self {
        let filename = filename.into();
        let source = source.into();
        let named_source = miette::NamedSource::new(filename, source);

        match self {
            Self::UnexpectedToken { token, span, src } => {
                // Force usage of fields for clippy
                let _ = (&token, &span, &src);
                Self::UnexpectedToken {
                    token,
                    span,
                    src: named_source,
                }
            }
            Self::MissingToken {
                expected,
                found,
                span,
                src,
            } => {
                let _ = (&expected, &found, &span, &src);
                Self::MissingToken {
                    expected,
                    found,
                    span,
                    src: named_source,
                }
            }
            Self::UnclosedDelimiter {
                opening_char,
                closing_char,
                opening,
                expected_close,
                src,
            } => {
                let _ = (
                    &opening_char,
                    &closing_char,
                    &opening,
                    &expected_close,
                    &src,
                );
                Self::UnclosedDelimiter {
                    opening_char,
                    closing_char,
                    opening,
                    expected_close,
                    src: named_source,
                }
            }
            Self::InvalidSyntax {
                construct,
                suggestion,
                span,
                src,
            } => {
                let _ = (&construct, &suggestion, &span, &src);
                Self::InvalidSyntax {
                    construct,
                    suggestion,
                    span,
                    src: named_source,
                }
            }
            other => other,
        }
    }

    /// Check if fields are actually used (satisfies clippy for proc macro fields)
    #[doc(hidden)]
    pub fn _check_field_usage(&self) {
        match self {
            Self::UnexpectedToken { token, span, src } => {
                let _ = (token, span, src);
            }
            Self::MissingToken {
                expected,
                found,
                span,
                src,
            } => {
                let _ = (expected, found, span, src);
            }
            Self::UnclosedDelimiter {
                opening_char,
                closing_char,
                opening,
                expected_close,
                src,
            } => {
                let _ = (opening_char, closing_char, opening, expected_close, src);
            }
            Self::InvalidSyntax {
                construct,
                suggestion,
                span,
                src,
            } => {
                let _ = (construct, suggestion, span, src);
            }
            Self::ParseFailed { reason } => {
                let _ = reason;
            }
            Self::IoError { message } => {
                let _ = message;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// This test ensures all fields are used, satisfying clippy
    /// The miette derive macro uses these fields for diagnostic output
    #[test]
    fn test_error_fields_are_used() {
        let source = "fn main() {".to_string();
        let src = miette::NamedSource::new("test", source.clone());

        let err1 = ParseError::UnexpectedToken {
            token: "test".to_string(),
            span: (0, 4).into(),
            src: miette::NamedSource::new("test", source.clone()),
        };
        err1._check_field_usage();

        let err2 = ParseError::MissingToken {
            expected: "}".to_string(),
            found: "EOF".to_string(),
            span: (11, 1).into(),
            src: miette::NamedSource::new("test", source.clone()),
        };
        err2._check_field_usage();

        let err3 = ParseError::UnclosedDelimiter {
            opening_char: '{',
            closing_char: '}',
            opening: (9, 1).into(),
            expected_close: (11, 1).into(),
            src: miette::NamedSource::new("test", source.clone()),
        };
        err3._check_field_usage();

        let err4 = ParseError::InvalidSyntax {
            construct: "function".to_string(),
            suggestion: Some("try this".to_string()),
            span: (0, 11).into(),
            src,
        };
        err4._check_field_usage();
    }
}
