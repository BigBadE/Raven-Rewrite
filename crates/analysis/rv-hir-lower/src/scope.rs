//! Scope tree for tracking lexical scopes during lowering

use la_arena::{Arena, Idx};
use rv_span::Span;
use std::collections::HashMap;

/// Unique identifier for a scope
pub type ScopeId = Idx<ScopeData>;

/// A scope in the source code
#[derive(Debug, Clone)]
pub struct ScopeData {
    /// Parent scope (None for root/module scope)
    pub parent: Option<ScopeId>,
    /// Symbols defined in this scope
    pub symbols: HashMap<String, super::SymbolId>,
    /// Source span of this scope
    pub span: Span,
}

/// Tree of all scopes in a file
#[derive(Debug, Default)]
pub struct ScopeTree {
    scopes: Arena<ScopeData>,
    /// Root scope for the module
    root: Option<ScopeId>,
}

impl ScopeTree {
    /// Create a new empty scope tree
    pub fn new() -> Self {
        Self::default()
    }

    /// Create the root module scope
    pub fn create_root(&mut self, span: Span) -> ScopeId {
        let scope = ScopeData {
            parent: None,
            symbols: HashMap::new(),
            span,
        };
        let id = self.scopes.alloc(scope);
        self.root = Some(id);
        id
    }

    /// Create a new child scope
    pub fn create_child(&mut self, parent: ScopeId, span: Span) -> ScopeId {
        let scope = ScopeData {
            parent: Some(parent),
            symbols: HashMap::new(),
            span,
        };
        self.scopes.alloc(scope)
    }

    /// Get scope data
    pub fn get(&self, id: ScopeId) -> Option<&ScopeData> {
        Some(&self.scopes[id])
    }

    /// Get mutable scope data
    pub fn get_mut(&mut self, id: ScopeId) -> Option<&mut ScopeData> {
        Some(&mut self.scopes[id])
    }

    /// Get the root scope
    pub fn root(&self) -> Option<ScopeId> {
        self.root
    }

    /// Resolve a name in a scope, walking up parent scopes
    pub fn resolve(&self, scope: ScopeId, name: &str) -> Option<super::SymbolId> {
        let mut current = Some(scope);
        while let Some(scope_id) = current {
            let scope_data = &self.scopes[scope_id];
            if let Some(symbol) = scope_data.symbols.get(name) {
                return Some(*symbol);
            }
            current = scope_data.parent;
        }
        None
    }

    /// Add a symbol to a scope
    pub fn add_symbol(&mut self, scope: ScopeId, name: String, symbol: super::SymbolId) {
        self.scopes[scope].symbols.insert(name, symbol);
    }
}

/// Scope builder for constructing scopes during lowering
pub struct Scope<'tree> {
    tree: &'tree mut ScopeTree,
    current: ScopeId,
}

impl<'tree> Scope<'tree> {
    /// Create a new scope builder starting at root
    pub fn new(tree: &'tree mut ScopeTree, root: ScopeId) -> Self {
        Self {
            tree,
            current: root,
        }
    }

    /// Enter a new child scope
    pub fn enter(&mut self, span: Span) -> ScopeId {
        let new_scope = self.tree.create_child(self.current, span);
        self.current = new_scope;
        new_scope
    }

    /// Exit to parent scope
    pub fn exit(&mut self) {
        let scope_data = &self.tree.scopes[self.current];
        if let Some(parent) = scope_data.parent {
            self.current = parent;
        }
    }

    /// Get current scope ID
    pub fn current(&self) -> ScopeId {
        self.current
    }

    /// Add a symbol to the current scope
    pub fn add_symbol(&mut self, name: String, symbol: super::SymbolId) {
        self.tree.add_symbol(self.current, name, symbol);
    }

    /// Resolve a name in the current scope
    pub fn resolve(&self, name: &str) -> Option<super::SymbolId> {
        self.tree.resolve(self.current, name)
    }
}
