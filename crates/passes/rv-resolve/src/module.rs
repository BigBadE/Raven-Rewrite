//! Module resolution for cross-file name resolution
//!
//! This module provides infrastructure for resolving module-qualified paths
//! and handling `use` declarations across module boundaries.

use crate::error::ResolutionError;
use rv_hir::{DefId, FunctionId, ModuleDef, ModuleId, TraitId, TypeDefId, UseItem, Visibility};
use rv_intern::Symbol;
use rv_span::FileSpan;
use rustc_hash::FxHashMap;

/// Represents what a module exports
#[derive(Debug, Clone)]
pub struct ModuleExports {
    /// Functions exported by this module
    pub functions: FxHashMap<Symbol, (FunctionId, Visibility)>,
    /// Structs exported by this module
    pub structs: FxHashMap<Symbol, (TypeDefId, Visibility)>,
    /// Enums exported by this module
    pub enums: FxHashMap<Symbol, (TypeDefId, Visibility)>,
    /// Traits exported by this module
    pub traits: FxHashMap<Symbol, (TraitId, Visibility)>,
    /// Submodules exported by this module
    pub modules: FxHashMap<Symbol, (ModuleId, Visibility)>,
    /// Re-exports from `pub use` declarations
    pub reexports: FxHashMap<Symbol, ResolvedImport>,
}

impl ModuleExports {
    /// Create empty module exports
    #[must_use]
    pub fn new() -> Self {
        Self {
            functions: FxHashMap::default(),
            structs: FxHashMap::default(),
            enums: FxHashMap::default(),
            traits: FxHashMap::default(),
            modules: FxHashMap::default(),
            reexports: FxHashMap::default(),
        }
    }

    /// Look up an item by name
    #[must_use]
    pub fn lookup(&self, name: Symbol) -> Option<ResolvedImport> {
        // Check functions
        if let Some((id, vis)) = self.functions.get(&name) {
            return Some(ResolvedImport {
                def: DefId::Function(*id),
                visibility: *vis,
                kind: ImportKind::Function,
            });
        }
        // Check structs
        if let Some((id, vis)) = self.structs.get(&name) {
            return Some(ResolvedImport {
                def: DefId::Type(*id),
                visibility: *vis,
                kind: ImportKind::Struct,
            });
        }
        // Check enums
        if let Some((id, vis)) = self.enums.get(&name) {
            return Some(ResolvedImport {
                def: DefId::Type(*id),
                visibility: *vis,
                kind: ImportKind::Enum,
            });
        }
        // Check traits
        if let Some((id, vis)) = self.traits.get(&name) {
            return Some(ResolvedImport {
                def: DefId::Trait(*id),
                visibility: *vis,
                kind: ImportKind::Trait,
            });
        }
        // Check submodules
        if let Some((id, vis)) = self.modules.get(&name) {
            return Some(ResolvedImport {
                def: DefId::Module(*id),
                visibility: *vis,
                kind: ImportKind::Module,
            });
        }
        // Check re-exports
        if let Some(reexport) = self.reexports.get(&name) {
            return Some(reexport.clone());
        }
        None
    }

    /// Get all public items (for glob imports)
    #[must_use]
    pub fn public_items(&self) -> Vec<(Symbol, ResolvedImport)> {
        let mut items = Vec::new();

        for (name, (id, vis)) in &self.functions {
            if *vis == Visibility::Public {
                items.push((
                    *name,
                    ResolvedImport {
                        def: DefId::Function(*id),
                        visibility: *vis,
                        kind: ImportKind::Function,
                    },
                ));
            }
        }
        for (name, (id, vis)) in &self.structs {
            if *vis == Visibility::Public {
                items.push((
                    *name,
                    ResolvedImport {
                        def: DefId::Type(*id),
                        visibility: *vis,
                        kind: ImportKind::Struct,
                    },
                ));
            }
        }
        for (name, (id, vis)) in &self.enums {
            if *vis == Visibility::Public {
                items.push((
                    *name,
                    ResolvedImport {
                        def: DefId::Type(*id),
                        visibility: *vis,
                        kind: ImportKind::Enum,
                    },
                ));
            }
        }
        for (name, (id, vis)) in &self.traits {
            if *vis == Visibility::Public {
                items.push((
                    *name,
                    ResolvedImport {
                        def: DefId::Trait(*id),
                        visibility: *vis,
                        kind: ImportKind::Trait,
                    },
                ));
            }
        }
        for (name, (id, vis)) in &self.modules {
            if *vis == Visibility::Public {
                items.push((
                    *name,
                    ResolvedImport {
                        def: DefId::Module(*id),
                        visibility: *vis,
                        kind: ImportKind::Module,
                    },
                ));
            }
        }
        for (name, import) in &self.reexports {
            if import.visibility == Visibility::Public {
                items.push((*name, import.clone()));
            }
        }

        items
    }
}

impl Default for ModuleExports {
    fn default() -> Self {
        Self::new()
    }
}

/// A resolved import
#[derive(Debug, Clone)]
pub struct ResolvedImport {
    /// The definition this import refers to
    pub def: DefId,
    /// Visibility of the imported item
    pub visibility: Visibility,
    /// Kind of import
    pub kind: ImportKind,
}

/// Kind of imported item
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImportKind {
    /// Function import
    Function,
    /// Struct import
    Struct,
    /// Enum import
    Enum,
    /// Trait import
    Trait,
    /// Module import
    Module,
}

/// Module resolver for cross-file name resolution
#[derive(Debug)]
pub struct ModuleResolver {
    /// Exports for each module
    module_exports: FxHashMap<ModuleId, ModuleExports>,
    /// Root module ID (used for resolving absolute paths starting with `crate::`)
    root_module: ModuleId,
    /// Module parent relationships
    module_parents: FxHashMap<ModuleId, ModuleId>,
    /// Module names
    module_names: FxHashMap<ModuleId, Symbol>,
    /// Resolved imports for each module (items brought into scope via `use`)
    module_imports: FxHashMap<ModuleId, FxHashMap<Symbol, ResolvedImport>>,
    /// Traits that are in scope for each module (for method resolution)
    /// A trait is in scope if it's defined in or imported into the module
    in_scope_traits: FxHashMap<ModuleId, Vec<TraitId>>,
}

impl ModuleResolver {
    /// Create a new module resolver
    #[must_use]
    pub fn new(root_module: ModuleId) -> Self {
        Self {
            module_exports: FxHashMap::default(),
            root_module,
            module_parents: FxHashMap::default(),
            module_names: FxHashMap::default(),
            module_imports: FxHashMap::default(),
            in_scope_traits: FxHashMap::default(),
        }
    }

    /// Get the root module ID
    #[must_use]
    pub fn root_module(&self) -> ModuleId {
        self.root_module
    }

    /// Register a module's basic structure (parent, name, empty exports)
    ///
    /// This should be called first for all modules in the crate.
    /// After all modules are registered, use the `register_*` methods
    /// to populate each module's exports with named items.
    pub fn register_module(&mut self, module: &ModuleDef, parent: Option<ModuleId>) {
        let exports = ModuleExports::new();

        // Register parent relationship
        if let Some(parent_id) = parent {
            self.module_parents.insert(module.id, parent_id);
        }
        self.module_names.insert(module.id, module.name);

        // Initialize empty exports - will be populated via register_* methods
        self.module_exports.insert(module.id, exports);

        // Initialize empty imports for this module
        self.module_imports.insert(module.id, FxHashMap::default());

        // Initialize empty in-scope traits for this module
        self.in_scope_traits.insert(module.id, Vec::new());
    }

    /// Register a function in a module
    pub fn register_function(
        &mut self,
        module_id: ModuleId,
        name: Symbol,
        function_id: FunctionId,
        visibility: Visibility,
    ) {
        if let Some(exports) = self.module_exports.get_mut(&module_id) {
            exports.functions.insert(name, (function_id, visibility));
        }
    }

    /// Register a struct in a module
    pub fn register_struct(
        &mut self,
        module_id: ModuleId,
        name: Symbol,
        type_id: TypeDefId,
        visibility: Visibility,
    ) {
        if let Some(exports) = self.module_exports.get_mut(&module_id) {
            exports.structs.insert(name, (type_id, visibility));
        }
    }

    /// Register an enum in a module
    pub fn register_enum(
        &mut self,
        module_id: ModuleId,
        name: Symbol,
        type_id: TypeDefId,
        visibility: Visibility,
    ) {
        if let Some(exports) = self.module_exports.get_mut(&module_id) {
            exports.enums.insert(name, (type_id, visibility));
        }
    }

    /// Register a trait in a module
    ///
    /// This also adds the trait to the module's in-scope traits for method resolution.
    pub fn register_trait(
        &mut self,
        module_id: ModuleId,
        name: Symbol,
        trait_id: TraitId,
        visibility: Visibility,
    ) {
        if let Some(exports) = self.module_exports.get_mut(&module_id) {
            exports.traits.insert(name, (trait_id, visibility));
        }
        // Traits defined in a module are automatically in scope
        if let Some(in_scope) = self.in_scope_traits.get_mut(&module_id) {
            if !in_scope.contains(&trait_id) {
                in_scope.push(trait_id);
            }
        }
    }

    /// Register a submodule in a module
    pub fn register_submodule(
        &mut self,
        parent_id: ModuleId,
        name: Symbol,
        child_id: ModuleId,
        visibility: Visibility,
    ) {
        if let Some(exports) = self.module_exports.get_mut(&parent_id) {
            exports.modules.insert(name, (child_id, visibility));
        }
    }

    /// Resolve a module-qualified path like `mod1::mod2::item`
    ///
    /// # Arguments
    /// * `from_module` - The module we're resolving from
    /// * `path` - The path segments to resolve
    /// * `use_site` - Source location for error reporting
    ///
    /// # Errors
    /// Returns an error if the path cannot be resolved or visibility is violated
    pub fn resolve_path(
        &self,
        from_module: ModuleId,
        path: &[Symbol],
        use_site: FileSpan,
    ) -> Result<ResolvedImport, ResolutionError> {
        if path.is_empty() {
            return Err(ResolutionError::EmptyPath { use_site });
        }

        // Start resolution from the current module or root
        let mut current_module = from_module;
        let mut segments = path.iter().peekable();

        // Check if the first segment is a module name in the current module's scope
        let first = *segments.next().unwrap();

        // Look up the first segment in the current module's exports
        let exports = self.module_exports.get(&current_module).ok_or_else(|| {
            ResolutionError::ModuleNotFound {
                module_id: current_module,
                use_site,
            }
        })?;

        // If there's only one segment, it's a direct lookup
        if segments.peek().is_none() {
            return exports.lookup(first).ok_or_else(|| ResolutionError::Undefined {
                name: first,
                use_site,
                suggestions: vec![],
            });
        }

        // Multiple segments: first must be a module
        let first_import = exports.lookup(first).ok_or_else(|| ResolutionError::Undefined {
            name: first,
            use_site,
            suggestions: vec![],
        })?;

        if first_import.kind != ImportKind::Module {
            return Err(ResolutionError::NotAModule {
                name: first,
                use_site,
            });
        }

        // Extract the module ID
        current_module = match first_import.def {
            DefId::Module(id) => id,
            _ => {
                return Err(ResolutionError::NotAModule {
                    name: first,
                    use_site,
                })
            }
        };

        // Walk the remaining segments
        while let Some(&segment) = segments.next() {
            let exports = self.module_exports.get(&current_module).ok_or_else(|| {
                ResolutionError::ModuleNotFound {
                    module_id: current_module,
                    use_site,
                }
            })?;

            let import = exports.lookup(segment).ok_or_else(|| ResolutionError::Undefined {
                name: segment,
                use_site,
                suggestions: vec![],
            })?;

            // Check visibility
            if import.visibility != Visibility::Public && !self.is_visible(from_module, current_module)
            {
                return Err(ResolutionError::PrivateItem {
                    name: segment,
                    def_site: use_site, // We don't have the def site here
                    use_site,
                });
            }

            // If there are more segments, this must be a module
            if segments.peek().is_some() {
                if import.kind != ImportKind::Module {
                    return Err(ResolutionError::NotAModule {
                        name: segment,
                        use_site,
                    });
                }
                current_module = match import.def {
                    DefId::Module(id) => id,
                    _ => {
                        return Err(ResolutionError::NotAModule {
                            name: segment,
                            use_site,
                        })
                    }
                };
            } else {
                // This is the final segment, return it
                return Ok(import);
            }
        }

        // Should not reach here
        Err(ResolutionError::EmptyPath { use_site })
    }

    /// Process use declarations and resolve imports
    ///
    /// Returns a list of errors for any imports that failed to resolve.
    /// Successful imports are added to the module's import scope.
    pub fn process_use_declarations(
        &mut self,
        module_id: ModuleId,
        use_items: &[UseItem],
    ) -> Vec<ResolutionError> {
        let mut errors = Vec::new();
        let mut resolved_imports = Vec::new();

        // First pass: resolve all imports
        for use_item in use_items {
            match self.resolve_use(module_id, use_item) {
                Ok(resolved) => {
                    // Determine the name to import under
                    let import_name = use_item
                        .alias
                        .unwrap_or_else(|| *use_item.path.last().expect("use path cannot be empty"));

                    // Check if this is a pub use (re-export)
                    let is_reexport = use_item.visibility == Visibility::Public;

                    resolved_imports.push((import_name, resolved, is_reexport));
                }
                Err(e) => errors.push(e),
            }
        }

        // Second pass: add resolved imports to module scope
        for (import_name, resolved, is_reexport) in resolved_imports {
            // Add to module's imports (visible within this module)
            if let Some(imports) = self.module_imports.get_mut(&module_id) {
                imports.insert(import_name, resolved.clone());
            }

            // If this is a trait import, add to in-scope traits for method resolution
            if resolved.kind == ImportKind::Trait {
                if let DefId::Trait(trait_id) = resolved.def {
                    if let Some(in_scope) = self.in_scope_traits.get_mut(&module_id) {
                        if !in_scope.contains(&trait_id) {
                            in_scope.push(trait_id);
                        }
                    }
                }
            }

            // If pub use, also add to module's exports (visible to other modules)
            if is_reexport {
                if let Some(exports) = self.module_exports.get_mut(&module_id) {
                    exports.reexports.insert(import_name, resolved);
                }
            }
        }

        errors
    }

    /// Resolve a use declaration
    fn resolve_use(
        &self,
        from_module: ModuleId,
        use_item: &UseItem,
    ) -> Result<ResolvedImport, ResolutionError> {
        self.resolve_path(from_module, &use_item.path, use_item.span)
    }

    /// Check if `from_module` can access private items in `target_module`
    fn is_visible(&self, from_module: ModuleId, target_module: ModuleId) -> bool {
        // Same module or child module can access
        if from_module == target_module {
            return true;
        }

        // Check if from_module is a descendant of target_module
        let mut current = from_module;
        while let Some(&parent) = self.module_parents.get(&current) {
            if parent == target_module {
                return true;
            }
            current = parent;
        }

        false
    }

    /// Get exports for a module
    #[must_use]
    pub fn get_exports(&self, module_id: ModuleId) -> Option<&ModuleExports> {
        self.module_exports.get(&module_id)
    }

    /// Get all public items from a module (for glob imports)
    #[must_use]
    pub fn get_public_items(&self, module_id: ModuleId) -> Vec<(Symbol, ResolvedImport)> {
        self.module_exports
            .get(&module_id)
            .map(|e| e.public_items())
            .unwrap_or_default()
    }

    /// Look up an item in a module's scope (includes both exports and imports)
    ///
    /// This is used during name resolution within a module to find items
    /// that are either defined in or imported into the module.
    #[must_use]
    pub fn lookup_in_scope(&self, module_id: ModuleId, name: Symbol) -> Option<ResolvedImport> {
        // First check exports (items defined in this module)
        if let Some(exports) = self.module_exports.get(&module_id) {
            if let Some(import) = exports.lookup(name) {
                return Some(import);
            }
        }

        // Then check imports (items brought in via `use`)
        if let Some(imports) = self.module_imports.get(&module_id) {
            if let Some(import) = imports.get(&name) {
                return Some(import.clone());
            }
        }

        None
    }

    /// Get the imports for a module
    #[must_use]
    pub fn get_imports(&self, module_id: ModuleId) -> Option<&FxHashMap<Symbol, ResolvedImport>> {
        self.module_imports.get(&module_id)
    }

    /// Process a glob import (`use module::*`)
    ///
    /// Imports all public items from the target module into the current module.
    /// This includes adding any imported traits to the in-scope traits for method resolution.
    pub fn process_glob_import(
        &mut self,
        from_module: ModuleId,
        target_module: ModuleId,
        use_site: FileSpan,
    ) -> Result<(), ResolutionError> {
        // Get all public items from target module
        let public_items = self.get_public_items(target_module);

        if public_items.is_empty() {
            return Err(ResolutionError::GlobImportFailed {
                module_id: target_module,
                use_site,
            });
        }

        // Collect traits to add to in-scope
        let traits_to_add: Vec<TraitId> = public_items
            .iter()
            .filter_map(|(_, resolved)| {
                if resolved.kind == ImportKind::Trait {
                    if let DefId::Trait(trait_id) = resolved.def {
                        return Some(trait_id);
                    }
                }
                None
            })
            .collect();

        // Add all public items to the importing module's scope
        if let Some(imports) = self.module_imports.get_mut(&from_module) {
            for (name, resolved) in public_items {
                imports.insert(name, resolved);
            }
        }

        // Add traits to in-scope traits
        if let Some(in_scope) = self.in_scope_traits.get_mut(&from_module) {
            for trait_id in traits_to_add {
                if !in_scope.contains(&trait_id) {
                    in_scope.push(trait_id);
                }
            }
        }

        Ok(())
    }

    /// Get the parent module of a given module
    #[must_use]
    pub fn get_parent(&self, module_id: ModuleId) -> Option<ModuleId> {
        self.module_parents.get(&module_id).copied()
    }

    /// Get the name of a module
    #[must_use]
    pub fn get_module_name(&self, module_id: ModuleId) -> Option<Symbol> {
        self.module_names.get(&module_id).copied()
    }

    /// Get the traits that are in scope for a module
    ///
    /// A trait is in scope if:
    /// - It's defined in the module
    /// - It's imported via `use`
    /// - It's imported via glob import (`use module::*`)
    ///
    /// This is used for trait method resolution - only methods from
    /// in-scope traits can be called without fully qualified paths.
    #[must_use]
    pub fn get_in_scope_traits(&self, module_id: ModuleId) -> &[TraitId] {
        self.in_scope_traits
            .get(&module_id)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Check if a trait is in scope for a given module
    #[must_use]
    pub fn is_trait_in_scope(&self, module_id: ModuleId, trait_id: TraitId) -> bool {
        self.in_scope_traits
            .get(&module_id)
            .map(|traits| traits.contains(&trait_id))
            .unwrap_or(false)
    }
}
