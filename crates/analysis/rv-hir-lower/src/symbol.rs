//! Symbol table for name resolution

use la_arena::{Arena, Idx};
use rv_hir::DefId;
use rv_intern::Symbol as InternedString;
use rv_span::Span;

/// Unique identifier for a symbol
pub type SymbolId = Idx<Symbol>;

/// A symbol in the source code
#[derive(Debug, Clone)]
pub struct Symbol {
    /// Symbol name
    pub name: InternedString,
    /// Symbol kind
    pub kind: SymbolKind,
    /// Definition ID in HIR (if applicable)
    pub def_id: Option<DefId>,
    /// Source span
    pub span: Span,
    /// Scope where this symbol is defined
    pub scope: super::ScopeId,
}

/// Kind of symbol
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolKind {
    /// Function definition
    Function,
    /// Struct definition
    Struct,
    /// Enum definition
    Enum,
    /// Trait definition
    Trait,
    /// Type alias
    TypeAlias,
    /// Const definition
    Const,
    /// Static definition
    Static,
    /// Local variable (let binding)
    Local,
    /// Function parameter
    Parameter,
    /// Module
    Module,
}

/// Symbol table mapping names to symbols
#[derive(Debug, Default)]
pub struct SymbolTable {
    symbols: Arena<Symbol>,
}

impl SymbolTable {
    /// Create a new empty symbol table
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a symbol to the table
    pub fn add(
        &mut self,
        name: InternedString,
        kind: SymbolKind,
        span: Span,
        scope: super::ScopeId,
    ) -> SymbolId {
        let symbol = Symbol {
            name,
            kind,
            def_id: None,
            span,
            scope,
        };
        self.symbols.alloc(symbol)
    }

    /// Get a symbol by ID
    pub fn get(&self, id: SymbolId) -> Option<&Symbol> {
        Some(&self.symbols[id])
    }

    /// Get mutable symbol by ID
    pub fn get_mut(&mut self, id: SymbolId) -> Option<&mut Symbol> {
        Some(&mut self.symbols[id])
    }

    /// Set the `DefId` for a symbol
    pub fn set_def_id(&mut self, id: SymbolId, def_id: DefId) {
        self.symbols[id].def_id = Some(def_id);
    }
}
