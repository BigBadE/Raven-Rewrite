//! Parser infrastructure for Raven
//!
//! This crate provides parsing capabilities using tree-sitter.

pub mod error;

pub use error::ParseError;

use lang_raven::RavenLanguage;
use miette::SourceSpan;
use rv_syntax::{Language, SyntaxNode};

/// Result of parsing a source file
#[derive(Debug, Clone)]
pub struct ParseResult {
    /// Converted syntax tree
    pub syntax: Option<SyntaxNode>,
    /// Parse errors with detailed diagnostics
    pub errors: Vec<ParseError>,
}

/// Parse Raven source code using the language adapter
pub fn parse_source(source: &str) -> ParseResult {
    let language = RavenLanguage::new();

    // Parse using the language adapter
    match language.parse(source) {
        Ok(tree) => {
            let mut errors = Vec::new();

            // Check for parse errors and collect detailed error information
            if tree.root_node().has_error() {
                collect_errors(&tree.root_node(), source, &mut errors);
            }

            // Convert to our syntax tree
            let syntax = language.lower_node(&tree.root_node(), source);

            ParseResult {
                syntax: Some(syntax),
                errors,
            }
        }
        Err(err) => ParseResult {
            syntax: None,
            errors: vec![ParseError::ParseFailed {
                reason: format!("{err}"),
            }],
        },
    }
}

/// Helper to create a missing token error
fn create_missing_token_error(source: &str, pos: usize, expected: &str) -> ParseError {
    // Find what came next
    let found = if pos < source.len() {
        source[pos..]
            .chars()
            .take(10)
            .collect::<String>()
            .split_whitespace()
            .next()
            .unwrap_or("end of file")
            .to_string()
    } else {
        "end of file".to_string()
    };

    let span: SourceSpan = (pos, 1).into();
    let src = miette::NamedSource::new("<input>", source.to_string());
    ParseError::MissingToken {
        expected: expected.to_string(),
        found,
        span,
        src,
    }
}

/// Recursively collect error nodes from the tree
fn collect_errors(node: &tree_sitter::Node, source: &str, errors: &mut Vec<ParseError>) {
    if node.is_error() {
        let start = node.start_byte();
        let end = node.end_byte();
        let span: SourceSpan = (start, end - start).into();

        // Analyze the error context to provide better error messages
        let error = if let Some(parent_node) = node.parent() {
            analyze_error_context(parent_node, node, source, span)
        } else {
            let text = &source[start..end];
            let token = text.lines().next().unwrap_or(text).to_string();
            let src = miette::NamedSource::new("<input>", source.to_string());
            ParseError::UnexpectedToken { token, span, src }
        };

        errors.push(error);
    } else if node.is_missing() {
        let pos = node.start_byte();
        let expected = node.kind().to_string();

        // Check if this is an unclosed delimiter
        let error = if expected == ")" || expected == "}" || expected == "]" {
            // Try to find the matching opening delimiter
            if let Some(parent) = node.parent() {
                if let Some(opening_pos) = find_opening_delimiter(&parent, source) {
                    let (opening_char, closing_char) = match expected.as_str() {
                        ")" => ('(', ')'),
                        "}" => ('{', '}'),
                        "]" => ('[', ']'),
                        other => panic!(
                            "ICE: Unexpected delimiter {:?} in unclosed delimiter handling. \
                             Only ), }}, and ] should reach this match.",
                            other
                        ),
                    };
                    let opening: SourceSpan = (opening_pos, 1).into();
                    let expected_close: SourceSpan = (pos, 1).into();
                    let src = miette::NamedSource::new("<input>", source.to_string());
                    ParseError::UnclosedDelimiter {
                        opening_char,
                        closing_char,
                        opening,
                        expected_close,
                        src,
                    }
                } else {
                    create_missing_token_error(source, pos, &expected)
                }
            } else {
                create_missing_token_error(source, pos, &expected)
            }
        } else {
            create_missing_token_error(source, pos, &expected)
        };

        errors.push(error);
    }

    // Recursively check children
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_errors(&child, source, errors);
    }
}

/// Analyze error context to provide more specific error messages
fn analyze_error_context(
    parent: tree_sitter::Node,
    error_node: &tree_sitter::Node,
    source: &str,
    error_span: SourceSpan,
) -> ParseError {
    let parent_kind = parent.kind();
    let src = miette::NamedSource::new("<input>", source.to_string());

    // Check for common patterns
    match parent_kind {
        "parameters" | "arguments" => {
            // Look for unclosed delimiters
            if let Some(opening_pos) = find_opening_delimiter(&parent, source) {
                let opening_char = '(';
                let closing_char = ')';
                let opening: SourceSpan = (opening_pos, 1).into();
                let expected_close = error_span;
                ParseError::UnclosedDelimiter {
                    opening_char,
                    closing_char,
                    opening,
                    expected_close,
                    src,
                }
            } else {
                let token = &source[error_node.start_byte()..error_node.end_byte()];
                let token = token.to_string();
                let span = error_span;
                ParseError::UnexpectedToken { token, span, src }
            }
        }
        "block" => {
            // Check for unclosed braces
            if let Some(opening_pos) = find_opening_delimiter(&parent, source) {
                let opening_char = '{';
                let closing_char = '}';
                let opening: SourceSpan = (opening_pos, 1).into();
                let expected_close = error_span;
                ParseError::UnclosedDelimiter {
                    opening_char,
                    closing_char,
                    opening,
                    expected_close,
                    src,
                }
            } else {
                let construct = "block".to_string();
                let suggestion = Some("blocks must be enclosed in braces `{}`".to_string());
                let span = error_span;
                ParseError::InvalidSyntax {
                    construct,
                    suggestion,
                    span,
                    src,
                }
            }
        }
        "function_item" => {
            let construct = "function declaration".to_string();
            let suggestion = Some(
                "function declarations have the form: `fn name(params) -> return_type { body }`"
                    .to_string(),
            );
            let span = error_span;
            ParseError::InvalidSyntax {
                construct,
                suggestion,
                span,
                src,
            }
        }
        _ => {
            let token = &source[error_node.start_byte()..error_node.end_byte()];
            let token = token.to_string();
            let span = error_span;
            ParseError::UnexpectedToken { token, span, src }
        }
    }
}

/// Find the position of an opening delimiter in a node
fn find_opening_delimiter(node: &tree_sitter::Node, source: &str) -> Option<usize> {
    let start = node.start_byte();
    let text = &source[start..node.end_byte()];

    // Look for opening delimiters
    for (idx, character) in text.char_indices() {
        if character == '(' || character == '{' || character == '[' {
            return Some(start + idx);
        }
    }

    None
}
