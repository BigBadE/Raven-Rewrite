//! Raven language adapter
//!
//! Provides language-specific support for Raven (currently using Rust syntax)

use anyhow::Result;
use rv_syntax::{Language, SyntaxNode};
use tree_sitter::{Parser, Tree};

/// Raven language implementation
pub struct RavenLanguage;

impl RavenLanguage {
    /// Creates a new Raven language adapter
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

impl Default for RavenLanguage {
    fn default() -> Self {
        Self::new()
    }
}

impl Language for RavenLanguage {
    fn name(&self) -> &'static str {
        "raven"
    }

    fn extensions(&self) -> &[&'static str] {
        &["rs", "rv"]
    }

    fn tree_sitter_language(&self) -> tree_sitter::Language {
        tree_sitter_rust::LANGUAGE.into()
    }

    fn parse(&self, source: &str) -> Result<Tree> {
        let mut parser = Parser::new();
        parser.set_language(&tree_sitter_rust::LANGUAGE.into())?;

        parser
            .parse(source, None)
            .ok_or_else(|| anyhow::anyhow!("tree-sitter parse failed"))
    }

    fn lower_node(&self, node: &tree_sitter::Node, source: &str) -> SyntaxNode {
        use rv_span::Span;
        use rv_syntax::SyntaxKind;

        let kind = match node.kind() {
            "source_file" => SyntaxKind::Root,
            "function_item" => SyntaxKind::Function,
            "struct_item" => SyntaxKind::Struct,
            "trait_item" => SyntaxKind::Trait,
            "impl_item" => SyntaxKind::Impl,
            "use_declaration" => SyntaxKind::Import,
            "identifier" => SyntaxKind::Identifier,
            "integer_literal" | "float_literal" | "string_literal" | "boolean_literal" => {
                SyntaxKind::Literal
            }
            "binary_expression" => SyntaxKind::BinaryOp,
            "call_expression" => SyntaxKind::Call,
            "block" => SyntaxKind::Block,
            "if_expression" => SyntaxKind::If,
            "while_expression" => SyntaxKind::While,
            "for_expression" => SyntaxKind::For,
            "match_expression" => SyntaxKind::Match,
            "return_expression" => SyntaxKind::Return,
            "let_declaration" => SyntaxKind::Let,
            "type_identifier" | "primitive_type" => SyntaxKind::Type,
            "type_parameters" => SyntaxKind::GenericParams,
            "parameters" => SyntaxKind::Parameters,
            "arguments" => SyntaxKind::Arguments,
            _ => SyntaxKind::Unknown(node.kind().to_string()),
        };

        let span = Span::new(node.start_byte() as u32, node.end_byte() as u32);

        // Extract source text for this node
        let text = source[node.start_byte()..node.end_byte()].to_string();

        let mut children = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            children.push(self.lower_node(&child, source));
        }

        SyntaxNode {
            kind,
            span,
            text,
            children,
        }
    }
}
