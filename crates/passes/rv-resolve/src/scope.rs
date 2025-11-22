//! Scope tree for name resolution

use crate::error::ResolutionError;
use rv_hir::{DefId, Visibility};
use rv_intern::Symbol;
use rv_span::FileSpan;
use rustc_hash::FxHashMap;

/// Unique identifier for a scope
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
pub struct ScopeId(pub u32);

/// Kind of scope
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    /// Module-level scope (top-level)
    Module,
    /// Function scope
    Function,
    /// Block scope (inside { })
    Block,
    /// Match arm scope
    MatchArm,
    /// Closure scope
    Closure,
}

/// Information about a resolved name
#[derive(Debug, Clone)]
pub struct Resolution {
    /// What the name refers to
    pub def: DefId,
    /// Visibility of the definition
    pub visibility: Visibility,
    /// Where it was defined
    pub span: FileSpan,
    /// Whether it's mutable
    pub mutable: bool,
}

/// A single scope in the scope tree
#[derive(Debug, Clone)]
pub struct Scope {
    /// Parent scope (None for module scope)
    pub parent: Option<ScopeId>,
    /// Kind of scope
    pub kind: ScopeKind,
    /// Definitions in this scope
    pub defs: FxHashMap<Symbol, Resolution>,
}

impl Scope {
    /// Create a new scope
    fn new(parent: Option<ScopeId>, kind: ScopeKind) -> Self {
        Self {
            parent,
            kind,
            defs: FxHashMap::default(),
        }
    }
}

/// Scope tree for name resolution
#[derive(Debug, Clone)]
pub struct ScopeTree {
    /// All scopes in the tree
    scopes: Vec<Scope>,
    /// Module-level (root) scope
    pub module_scope: ScopeId,
}

impl ScopeTree {
    /// Create a new scope tree with a module scope
    #[must_use]
    pub fn new() -> Self {
        let mut scopes = Vec::new();
        let module_scope = ScopeId(0);
        scopes.push(Scope::new(None, ScopeKind::Module));

        Self {
            scopes,
            module_scope,
        }
    }

    /// Create a child scope
    pub fn create_child(&mut self, parent: ScopeId, kind: ScopeKind) -> ScopeId {
        let scope_id = ScopeId(self.scopes.len() as u32);
        self.scopes.push(Scope::new(Some(parent), kind));
        scope_id
    }

    /// Define a name in a scope
    ///
    /// # Errors
    ///
    /// Returns `ResolutionError::DuplicateDefinition` if the name is already defined
    /// in this scope.
    pub fn define(
        &mut self,
        scope: ScopeId,
        name: Symbol,
        def: DefId,
        visibility: Visibility,
        mutable: bool,
        span: FileSpan,
    ) -> Result<(), ResolutionError> {
        let scope_data = &mut self.scopes[scope.0 as usize];

        // Check for duplicate definitions in the same scope
        if let Some(existing) = scope_data.defs.get(&name) {
            return Err(ResolutionError::DuplicateDefinition {
                name,
                first: existing.span,
                second: span,
            });
        }

        scope_data.defs.insert(
            name,
            Resolution {
                def,
                visibility,
                span,
                mutable,
            },
        );

        Ok(())
    }

    /// Resolve a name in a scope, walking up the scope chain
    ///
    /// # Errors
    ///
    /// Returns `ResolutionError::Undefined` if the name is not found in any
    /// visible scope, or `ResolutionError::PrivateItem` if the name is found
    /// but not visible from the use site.
    pub fn resolve(
        &self,
        scope: ScopeId,
        name: Symbol,
        use_site: FileSpan,
        interner: &rv_intern::Interner,
    ) -> Result<Resolution, ResolutionError> {
        let mut current_scope = scope;

        loop {
            let scope_data = &self.scopes[current_scope.0 as usize];

            // Check if name is defined in current scope
            if let Some(resolution) = scope_data.defs.get(&name) {
                // Check visibility
                if self.is_visible(resolution.visibility, scope, current_scope) {
                    return Ok(resolution.clone());
                }
                return Err(ResolutionError::PrivateItem {
                    name,
                    def_site: resolution.span,
                    use_site,
                });
            }

            // Walk up to parent scope
            if let Some(parent) = scope_data.parent {
                current_scope = parent;
            } else {
                // No more parent scopes, name is undefined
                let suggestions = self.compute_suggestions(name, scope, interner);
                return Err(ResolutionError::Undefined {
                    name,
                    use_site,
                    suggestions,
                });
            }
        }
    }

    /// Check if a definition is visible from a use site
    fn is_visible(
        &self,
        visibility: Visibility,
        use_scope: ScopeId,
        def_scope: ScopeId,
    ) -> bool {
        match visibility {
            Visibility::Public => true,
            Visibility::Private => {
                // Private items are only visible within the same scope or child scopes
                self.is_ancestor_of(def_scope, use_scope)
            }
        }
    }

    /// Check if `ancestor` is an ancestor of `descendant` (or the same scope)
    fn is_ancestor_of(&self, ancestor: ScopeId, descendant: ScopeId) -> bool {
        let mut current = descendant;
        loop {
            if current == ancestor {
                return true;
            }
            let scope_data = &self.scopes[current.0 as usize];
            if let Some(parent) = scope_data.parent {
                current = parent;
            } else {
                return false;
            }
        }
    }

    /// Compute suggestions for an undefined name using Levenshtein distance
    fn compute_suggestions(
        &self,
        name: Symbol,
        scope: ScopeId,
        interner: &rv_intern::Interner,
    ) -> Vec<Symbol> {
        let mut available_names = Vec::new();

        // Collect all names visible from this scope
        let mut current_scope = scope;
        loop {
            let scope_data = &self.scopes[current_scope.0 as usize];
            available_names.extend(scope_data.defs.keys().copied());

            if let Some(parent) = scope_data.parent {
                current_scope = parent;
            } else {
                break;
            }
        }

        ResolutionError::compute_suggestions(name, interner, &available_names)
    }

    /// Get a scope by ID
    #[must_use]
    pub fn get_scope(&self, scope: ScopeId) -> &Scope {
        &self.scopes[scope.0 as usize]
    }
}

impl Default for ScopeTree {
    fn default() -> Self {
        Self::new()
    }
}
