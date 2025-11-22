//! Macro AST types

use rv_intern::Symbol;
use rv_span::FileSpan;

/// Unique identifier for a macro definition
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct MacroId(pub u32);

/// Macro definition
#[derive(Debug, Clone)]
pub struct MacroDef {
    /// Unique ID
    pub id: MacroId,
    /// Macro name
    pub name: Symbol,
    /// Macro kind (declarative, builtin, etc.)
    pub kind: MacroKind,
    /// Source location
    pub span: FileSpan,
}

/// Macro kind
#[derive(Debug, Clone)]
pub enum MacroKind {
    /// Declarative macro (macro_rules!)
    Declarative {
        /// Macro rules
        rules: Vec<MacroRule>,
    },
    /// Builtin macro (println!, vec!, etc.)
    Builtin {
        /// Builtin expander
        expander: BuiltinMacroKind,
    },
}

/// Builtin macro kinds
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinMacroKind {
    /// println! macro
    Println,
    /// vec! macro
    Vec,
    /// assert! macro
    Assert,
    /// format! macro
    Format,
}

/// A single macro rule (matcher => expander)
#[derive(Debug, Clone)]
pub struct MacroRule {
    /// Left-hand side pattern
    pub matcher: MacroMatcher,
    /// Right-hand side template
    pub expander: MacroExpander,
}

/// Macro matcher (left-hand side of macro rule)
#[derive(Debug, Clone)]
pub enum MacroMatcher {
    /// Literal token
    Token(Token),
    /// Metavariable ($x:expr)
    MetaVar {
        /// Variable name
        name: Symbol,
        /// Fragment specifier
        kind: FragmentKind,
    },
    /// Sequence ($(...), $(...)+, $(...)?)
    Sequence {
        /// Matchers in the sequence
        matchers: Vec<MacroMatcher>,
        /// Separator token
        separator: Option<Token>,
        /// Sequence kind (*, +, ?)
        kind: SequenceKind,
    },
    /// Group ((...), [...], {...})
    Group {
        /// Delimiter
        delimiter: Delimiter,
        /// Matchers inside
        matchers: Vec<MacroMatcher>,
    },
}

/// Macro expander (right-hand side of macro rule)
#[derive(Debug, Clone)]
pub enum MacroExpander {
    /// Literal token
    Token(Token),
    /// Substitute metavariable ($x)
    Substitute(Symbol),
    /// Sequence ($(...), $(...)+, $(...)?)
    Sequence {
        /// Expanders in the sequence
        expanders: Vec<MacroExpander>,
        /// Separator token
        separator: Option<Token>,
        /// Sequence kind (*, +, ?)
        kind: SequenceKind,
    },
    /// Group ((...), [...], {...})
    Group {
        /// Delimiter
        delimiter: Delimiter,
        /// Expanders inside
        expanders: Vec<MacroExpander>,
    },
}

/// Fragment specifier kind
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FragmentKind {
    /// Expression
    Expr,
    /// Identifier
    Ident,
    /// Type
    Ty,
    /// Pattern
    Pat,
    /// Statement
    Stmt,
    /// Block
    Block,
    /// Item
    Item,
    /// Path
    Path,
    /// Token tree
    Tt,
}

/// Sequence kind
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SequenceKind {
    /// Zero or more (*)
    ZeroOrMore,
    /// One or more (+)
    OneOrMore,
    /// Optional (?)
    Optional,
}

/// Token stream (sequence of tokens)
#[derive(Debug, Clone, PartialEq)]
pub struct TokenStream {
    /// Tokens in the stream
    pub tokens: Vec<Token>,
}

impl TokenStream {
    /// Create a new empty token stream
    #[must_use]
    pub fn new() -> Self {
        Self { tokens: Vec::new() }
    }

    /// Push a token to the stream
    pub fn push(&mut self, token: Token) {
        self.tokens.push(token);
    }

    /// Extend with another token stream
    pub fn extend(&mut self, other: TokenStream) {
        self.tokens.extend(other.tokens);
    }

    /// Get the number of tokens
    #[must_use]
    pub fn len(&self) -> usize {
        self.tokens.len()
    }

    /// Check if the stream is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    /// Iterate over tokens
    pub fn iter(&self) -> impl Iterator<Item = &Token> {
        self.tokens.iter()
    }
}

impl Default for TokenStream {
    fn default() -> Self {
        Self::new()
    }
}

/// Token
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    /// Identifier
    Ident(Symbol),
    /// Literal
    Literal(LiteralKind),
    /// Punctuation character
    Punct(char),
    /// Grouped tokens
    Group {
        /// Delimiter
        delim: Delimiter,
        /// Token stream inside
        stream: TokenStream,
    },
}

/// Literal kind
#[derive(Debug, Clone, PartialEq)]
pub enum LiteralKind {
    /// Integer literal
    Integer(i64),
    /// Float literal
    Float(f64),
    /// String literal
    String(String),
    /// Boolean literal
    Bool(bool),
}

/// Delimiter
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Delimiter {
    /// Parentheses (...)
    Paren,
    /// Brackets [...]
    Bracket,
    /// Braces {...}
    Brace,
}
