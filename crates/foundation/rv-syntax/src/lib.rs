//! Generic syntax tree traits for multi-language support
//!
//! This crate provides traits and types for working with syntax trees
//! from different programming languages in a uniform way.

use anyhow::Result;
use rv_arena::{Arena, Idx};
use rv_intern::Symbol;
use rv_span::{FileSpan, Span};
use std::fmt;

/// Generic syntax tree node
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxNode {
    /// The kind of this node
    pub kind: SyntaxKind,
    /// Source location
    pub span: Span,
    /// Source text (for literals, identifiers, operators)
    pub text: String,
    /// Child nodes
    pub children: Vec<SyntaxNode>,
}

/// Language-independent node kinds
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxKind {
    /// Root of the syntax tree
    Root,
    /// Function definition
    Function,
    /// Struct/class definition
    Struct,
    /// Enum definition
    Enum,
    /// Trait/interface definition
    Trait,
    /// Implementation block
    Impl,
    /// Import/use statement
    Import,
    /// Identifier
    Identifier,
    /// Literal value
    Literal,
    /// Binary operation
    BinaryOp,
    /// Function call
    Call,
    /// Block expression
    Block,
    /// If expression
    If,
    /// While loop
    While,
    /// For loop
    For,
    /// Match/switch expression
    Match,
    /// Return statement
    Return,
    /// Let/variable binding
    Let,
    /// Type annotation
    Type,
    /// Generic parameters
    GenericParams,
    /// Parameter list
    Parameters,
    /// Argument list
    Arguments,
    /// Unknown/language-specific node
    Unknown(String),
}

impl fmt::Display for SyntaxKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Root => write!(formatter, "root"),
            Self::Function => write!(formatter, "function"),
            Self::Struct => write!(formatter, "struct"),
            Self::Enum => write!(formatter, "enum"),
            Self::Trait => write!(formatter, "trait"),
            Self::Impl => write!(formatter, "impl"),
            Self::Import => write!(formatter, "import"),
            Self::Identifier => write!(formatter, "identifier"),
            Self::Literal => write!(formatter, "literal"),
            Self::BinaryOp => write!(formatter, "binary_op"),
            Self::Call => write!(formatter, "call"),
            Self::Block => write!(formatter, "block"),
            Self::If => write!(formatter, "if"),
            Self::While => write!(formatter, "while"),
            Self::For => write!(formatter, "for"),
            Self::Match => write!(formatter, "match"),
            Self::Return => write!(formatter, "return"),
            Self::Let => write!(formatter, "let"),
            Self::Type => write!(formatter, "type"),
            Self::GenericParams => write!(formatter, "generic_params"),
            Self::Parameters => write!(formatter, "parameters"),
            Self::Arguments => write!(formatter, "arguments"),
            Self::Unknown(name) => write!(formatter, "unknown({name})"),
        }
    }
}

/// Trait for language-specific parsers
pub trait Language: Send + Sync + 'static {
    /// Name of the language
    fn name(&self) -> &'static str;

    /// File extensions this language handles
    fn extensions(&self) -> &[&'static str];

    /// tree-sitter language instance
    fn tree_sitter_language(&self) -> tree_sitter::Language;

    /// Parse source code to concrete syntax tree
    ///
    /// # Errors
    ///
    /// Returns an error if parsing fails
    fn parse(&self, source: &str) -> Result<tree_sitter::Tree>;

    /// Convert tree-sitter node to generic syntax node
    fn lower_node(&self, node: &tree_sitter::Node, source: &str) -> SyntaxNode;
}

/// High-level AST node (post-parsing, pre-HIR)
pub type AstNodeId = Idx<AstNode>;

/// Abstract syntax tree node with semantic information
#[derive(Debug, Clone)]
pub struct AstNode {
    /// The kind of AST node
    pub kind: AstKind,
    /// Source span
    pub span: FileSpan,
}

/// Semantic AST node kinds
#[derive(Debug, Clone)]
pub enum AstKind {
    /// Function definition
    Function {
        /// Function name
        name: Symbol,
        /// Generic parameters
        generics: Vec<GenericParam>,
        /// Function parameters
        params: Vec<(Symbol, AstNodeId)>,
        /// Return type
        return_type: Option<AstNodeId>,
        /// Function body
        body: AstNodeId,
    },
    /// Struct definition
    Struct {
        /// Struct name
        name: Symbol,
        /// Generic parameters
        generics: Vec<GenericParam>,
        /// Fields
        fields: Vec<(Symbol, AstNodeId)>,
    },
    /// Trait definition
    Trait {
        /// Trait name
        name: Symbol,
        /// Generic parameters
        generics: Vec<GenericParam>,
        /// Associated items
        items: Vec<AstNodeId>,
    },
    /// Implementation block
    Impl {
        /// Type being implemented
        for_type: AstNodeId,
        /// Trait being implemented (None for inherent impl)
        trait_ref: Option<AstNodeId>,
        /// Items
        items: Vec<AstNodeId>,
    },
    /// Type reference
    Type {
        /// Type name
        name: Symbol,
        /// Generic arguments
        generics: Vec<AstNodeId>,
    },
    /// Literal value
    Literal(LiteralKind),
    /// Variable reference
    Variable(Symbol),
    /// Function call
    Call {
        /// Callee expression
        callee: AstNodeId,
        /// Arguments
        args: Vec<AstNodeId>,
    },
    /// Binary operation
    BinaryOp {
        /// Operator
        op: BinaryOpKind,
        /// Left operand
        left: AstNodeId,
        /// Right operand
        right: AstNodeId,
    },
    /// Block expression
    Block {
        /// Statements
        statements: Vec<AstNodeId>,
        /// Trailing expression
        expr: Option<AstNodeId>,
    },
    /// If expression
    If {
        /// Condition
        condition: AstNodeId,
        /// Then branch
        then_branch: AstNodeId,
        /// Else branch
        else_branch: Option<AstNodeId>,
    },
    /// Unknown node (for error recovery)
    Unknown,
}

/// Generic parameter
#[derive(Debug, Clone)]
pub struct GenericParam {
    /// Parameter name
    pub name: Symbol,
    /// Bounds
    pub bounds: Vec<Symbol>,
}

/// Literal kinds
#[derive(Debug, Clone)]
pub enum LiteralKind {
    /// Integer literal
    Integer(i64),
    /// Float literal
    Float(f64),
    /// String literal
    String(String),
    /// Boolean literal
    Bool(bool),
    /// Unit literal
    Unit,
}

/// Binary operator kinds
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOpKind {
    /// Addition
    Add,
    /// Subtraction
    Sub,
    /// Multiplication
    Mul,
    /// Division
    Div,
    /// Modulo
    Mod,
    /// Equality
    Eq,
    /// Inequality
    Ne,
    /// Less than
    Lt,
    /// Less than or equal
    Le,
    /// Greater than
    Gt,
    /// Greater than or equal
    Ge,
    /// Logical AND
    And,
    /// Logical OR
    Or,
}

/// Helper to build AST
pub struct AstBuilder {
    arena: Arena<AstNode>,
}

impl AstBuilder {
    /// Creates a new AST builder
    #[must_use]
    pub fn new() -> Self {
        Self {
            arena: Arena::new(),
        }
    }

    /// Allocates an AST node and returns its ID
    pub fn alloc(&mut self, kind: AstKind, span: FileSpan) -> AstNodeId {
        self.arena.alloc(AstNode { kind, span })
    }

    /// Gets a reference to a node
    #[must_use]
    pub fn get(&self, id: AstNodeId) -> &AstNode {
        &self.arena[id]
    }

    /// Consumes the builder and returns the arena
    #[must_use]
    pub fn finish(self) -> Arena<AstNode> {
        self.arena
    }
}

impl Default for AstBuilder {
    fn default() -> Self {
        Self::new()
    }
}
