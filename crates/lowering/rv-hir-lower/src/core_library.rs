//! Core library compilation and prelude injection
//!
//! This module provides full crate dependency support for the Rust core library.
//! The core library is compiled as a proper crate, following Rust's module system:
//!
//! 1. Parse `core/src/lib.rs` as the crate root
//! 2. Recursively follow all `mod` declarations to build the module tree
//! 3. Parse `core/src/prelude/v1.rs` for prelude exports
//! 4. Resolve `pub use` statements to inject items into user scope
//!
//! ## Prelude Contents (from `core::prelude::v1`)
//!
//! The prelude re-exports:
//! - Marker traits: `Copy`, `Send`, `Sized`, `Sync`, `Unpin`
//! - Function traits: `Drop`, `Fn`, `FnMut`, `FnOnce`
//! - Core traits: `Clone`, `Eq`, `Ord`, `PartialEq`, `PartialOrd`, `From`, `Into`, `Default`
//! - Iterator traits: `Iterator`, `IntoIterator`, `DoubleEndedIterator`, `ExactSizeIterator`, `Extend`
//! - Conversion traits: `AsMut`, `AsRef`
//! - Types: `Option::{self, None, Some}`, `Result::{self, Err, Ok}`
//! - Functions: `drop`, `size_of`, `size_of_val`, `align_of`, `align_of_val`

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::{LoweringContext, ScopeId, SymbolKind};
use rv_hir::{FunctionId, TraitId, TypeDefId};
use rv_syntax::{SyntaxKind, SyntaxNode};

/// Get the path to the Rust core library source
pub fn get_core_library_path() -> Option<PathBuf> {
    // Try to get sysroot from rustc
    let output = Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .ok()?;

    let sysroot = String::from_utf8(output.stdout).ok()?;
    let sysroot = sysroot.trim();

    let path = Path::new(sysroot).join("lib/rustlib/src/rust/library/core/src");

    if path.exists() {
        Some(path)
    } else {
        None
    }
}

/// A module in the crate's module tree
#[derive(Debug, Clone)]
pub struct CrateModule {
    /// Module name (e.g., "option", "result", "prelude")
    pub name: String,
    /// Full path from crate root (e.g., ["core", "option"])
    pub path: Vec<String>,
    /// Types defined in this module
    pub types: HashMap<String, TypeDefId>,
    /// Traits defined in this module
    pub traits: HashMap<String, TraitId>,
    /// Functions defined in this module
    pub functions: HashMap<String, FunctionId>,
    /// Child modules
    pub children: HashMap<String, CrateModule>,
    /// Re-exports from `pub use` statements
    pub reexports: Vec<UseDecl>,
}

impl CrateModule {
    /// Create a new empty module
    pub fn new(name: String, path: Vec<String>) -> Self {
        Self {
            name,
            path,
            types: HashMap::new(),
            traits: HashMap::new(),
            functions: HashMap::new(),
            children: HashMap::new(),
            reexports: Vec::new(),
        }
    }

    /// Get a child module by path segments
    pub fn get_module(&self, path: &[&str]) -> Option<&CrateModule> {
        if path.is_empty() {
            return Some(self);
        }
        let child = self.children.get(path[0])?;
        child.get_module(&path[1..])
    }

    /// Get a mutable child module by path segments
    pub fn get_module_mut(&mut self, path: &[&str]) -> Option<&mut CrateModule> {
        if path.is_empty() {
            return Some(self);
        }
        let child = self.children.get_mut(path[0])?;
        child.get_module_mut(&path[1..])
    }

    /// Resolve an item by path within this module tree
    pub fn resolve_item(&self, path: &[&str]) -> Option<ResolvedItem> {
        if path.is_empty() {
            return None;
        }

        // Single segment - look in current module
        if path.len() == 1 {
            let name = path[0];
            if let Some(&type_id) = self.types.get(name) {
                return Some(ResolvedItem::Type(type_id));
            }
            if let Some(&trait_id) = self.traits.get(name) {
                return Some(ResolvedItem::Trait(trait_id));
            }
            if let Some(&fn_id) = self.functions.get(name) {
                return Some(ResolvedItem::Function(fn_id));
            }
            return None;
        }

        // Multiple segments - descend into child module
        if let Some(child) = self.children.get(path[0]) {
            return child.resolve_item(&path[1..]);
        }

        None
    }
}

/// A resolved item from path resolution
#[derive(Debug, Clone, Copy)]
pub enum ResolvedItem {
    /// Type definition (struct or enum)
    Type(TypeDefId),
    /// Trait definition
    Trait(TraitId),
    /// Function definition
    Function(FunctionId),
}

/// A `use` declaration parsed from source
#[derive(Debug, Clone)]
pub struct UseDecl {
    /// The path being imported (e.g., ["crate", "option", "Option"])
    pub path: Vec<String>,
    /// Specific items to import (e.g., ["self", "Some", "None"])
    /// Empty means import all (`*`)
    pub items: Vec<String>,
    /// Whether this is a glob import (`use foo::*`)
    pub is_glob: bool,
}

/// The compiled core crate
#[derive(Debug)]
pub struct CoreCrate {
    /// Path to core library source
    pub source_path: PathBuf,
    /// The root module (represents `core::`)
    pub root: CrateModule,
}

impl CoreCrate {
    /// Compile the core crate from source
    ///
    /// This parses lib.rs and recursively builds the full module tree.
    pub fn compile(ctx: &mut LoweringContext) -> Option<Self> {
        let source_path = get_core_library_path()?;
        let lib_rs = source_path.join("lib.rs");

        if !lib_rs.exists() {
            return None;
        }

        // Create root module for "core"
        let mut root = CrateModule::new("core".to_string(), vec!["core".to_string()]);

        // Parse lib.rs to find all module declarations
        let lib_source = std::fs::read_to_string(&lib_rs).ok()?;
        let parse_result = rv_parser::parse_source(&lib_source);
        let syntax = parse_result.syntax?;

        // First pass: collect all `mod` declarations
        let mod_decls = Self::collect_mod_declarations(&syntax);

        // Compile ALL modules from the core library - no filtering
        // This ensures full core library support without any workarounds
        for mod_name in &mod_decls {
            Self::compile_module(ctx, &source_path, &mut root, mod_name, vec!["core".to_string()]);
        }

        Some(Self { source_path, root })
    }

    /// Collect all `mod` declarations from a syntax tree
    fn collect_mod_declarations(syntax: &SyntaxNode) -> Vec<String> {
        let mut mods = Vec::new();

        for child in &syntax.children {
            // Look for mod declarations (tree-sitter uses "mod_item")
            if matches!(&child.kind, SyntaxKind::Unknown(s) if s == "mod_item") {
                // Find the module name
                if let Some(name_node) = child.children.iter().find(|c| {
                    c.kind == SyntaxKind::Identifier
                        || matches!(&c.kind, SyntaxKind::Unknown(s) if s == "identifier")
                }) {
                    mods.push(name_node.text.clone());
                }
            }
        }

        mods
    }

    /// Compile a single module and add it to the parent
    fn compile_module(
        ctx: &mut LoweringContext,
        crate_path: &Path,
        parent: &mut CrateModule,
        mod_name: &str,
        parent_path: Vec<String>,
    ) {
        // Try mod_name.rs first, then mod_name/mod.rs
        let mod_file = crate_path.join(format!("{}.rs", mod_name));
        let mod_dir_file = crate_path.join(mod_name).join("mod.rs");

        let (source, mod_path) = if mod_file.exists() {
            match std::fs::read_to_string(&mod_file) {
                Ok(s) => (s, mod_file),
                Err(_) => return,
            }
        } else if mod_dir_file.exists() {
            match std::fs::read_to_string(&mod_dir_file) {
                Ok(s) => (s, mod_dir_file),
                Err(_) => return,
            }
        } else {
            return;
        };

        // Parse the module
        let parse_result = rv_parser::parse_source(&source);
        let Some(syntax) = parse_result.syntax else {
            return;
        };

        // Create module path
        let mut full_path = parent_path;
        full_path.push(mod_name.to_string());

        // Create the module
        let mut module = CrateModule::new(mod_name.to_string(), full_path.clone());

        // Create a scope for this module
        let module_scope = ctx.scope_tree.create_root(syntax.span);

        // Process all items in the module
        for child in &syntax.children {
            Self::process_module_item(ctx, module_scope, &mut module, child);
        }

        // Recursively compile submodules
        let submod_decls = Self::collect_mod_declarations(&syntax);
        let submod_path = mod_path.parent().unwrap_or(crate_path);

        for submod_name in &submod_decls {
            Self::compile_module(ctx, submod_path, &mut module, submod_name, full_path.clone());
        }

        parent.children.insert(mod_name.to_string(), module);
    }

    /// Process a single item in a module
    fn process_module_item(
        ctx: &mut LoweringContext,
        scope: ScopeId,
        module: &mut CrateModule,
        node: &SyntaxNode,
    ) {
        match &node.kind {
            SyntaxKind::Enum => {
                // Get enum name
                let name_node = node.children.iter().find(|c| {
                    c.kind == SyntaxKind::Identifier
                        || c.kind == SyntaxKind::Type
                        || matches!(&c.kind, SyntaxKind::Unknown(s) if s == "type_identifier")
                });

                if let Some(name_node) = name_node {
                    let name = name_node.text.clone();

                    // Lower this enum
                    crate::lower::lower_enum(ctx, scope, node, vec![]);

                    // Find the TypeDefId that was created
                    if let Some(sym_id) = ctx.scope_tree.resolve_in_scope(scope, &name) {
                        if let Some(rv_hir::DefId::Type(type_def_id)) = ctx.symbol_defs.get(&sym_id)
                        {
                            module.types.insert(name, *type_def_id);
                        }
                    }
                }
            }
            SyntaxKind::Struct => {
                // Get struct name
                let name_node = node.children.iter().find(|c| {
                    c.kind == SyntaxKind::Identifier
                        || c.kind == SyntaxKind::Type
                        || matches!(&c.kind, SyntaxKind::Unknown(s) if s == "type_identifier")
                });

                if let Some(name_node) = name_node {
                    let name = name_node.text.clone();

                    // Lower this struct
                    crate::lower::lower_struct(ctx, scope, node, vec![]);

                    // Find the TypeDefId that was created
                    if let Some(sym_id) = ctx.scope_tree.resolve_in_scope(scope, &name) {
                        if let Some(rv_hir::DefId::Type(type_def_id)) = ctx.symbol_defs.get(&sym_id)
                        {
                            module.types.insert(name, *type_def_id);
                        }
                    }
                }
            }
            SyntaxKind::Trait => {
                // Get trait name
                let name_node = node.children.iter().find(|c| {
                    c.kind == SyntaxKind::Identifier
                        || c.kind == SyntaxKind::Type
                        || matches!(&c.kind, SyntaxKind::Unknown(s) if s == "type_identifier")
                });

                if let Some(name_node) = name_node {
                    let name = name_node.text.clone();

                    // Lower this trait
                    crate::lower::lower_trait(ctx, scope, node, vec![]);

                    // Find the TraitId that was created
                    if let Some(sym_id) = ctx.scope_tree.resolve_in_scope(scope, &name) {
                        if let Some(rv_hir::DefId::Trait(trait_id)) = ctx.symbol_defs.get(&sym_id) {
                            module.traits.insert(name, *trait_id);

                            // Mark all default method bodies as core library
                            if let Some(trait_def) = ctx.traits.get(trait_id) {
                                for method in &trait_def.methods {
                                    if let Some(fn_id) = method.default_body {
                                        if let Some(func) = ctx.functions.get_mut(&fn_id) {
                                            func.is_core_library = true;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            SyntaxKind::Function => {
                // Get function name
                let name_node = node.children.iter().find(|c| {
                    c.kind == SyntaxKind::Identifier
                        || matches!(&c.kind, SyntaxKind::Unknown(s) if s == "identifier")
                });

                if let Some(name_node) = name_node {
                    let name = name_node.text.clone();

                    // Lower this function
                    crate::lower::lower_function(ctx, scope, node, vec![]);

                    // Find the FunctionId that was created and mark it as core library
                    if let Some(sym_id) = ctx.scope_tree.resolve_in_scope(scope, &name) {
                        if let Some(rv_hir::DefId::Function(fn_id)) = ctx.symbol_defs.get(&sym_id) {
                            // Mark function as core library so it won't be lowered to MIR
                            if let Some(func) = ctx.functions.get_mut(fn_id) {
                                func.is_core_library = true;
                            }
                            module.functions.insert(name, *fn_id);
                        }
                    }
                }
            }
            SyntaxKind::Unknown(s) if s == "use_declaration" => {
                // Parse use declaration for re-exports
                if let Some(use_decl) = Self::parse_use_declaration(node) {
                    module.reexports.push(use_decl);
                }
            }
            _ => {}
        }
    }

    /// Parse a use declaration into a UseDecl
    fn parse_use_declaration(node: &SyntaxNode) -> Option<UseDecl> {
        // Find the use_tree or scoped_identifier
        let use_tree = node.children.iter().find(|c| {
            matches!(&c.kind, SyntaxKind::Unknown(s) if s == "use_tree" || s == "scoped_identifier" || s == "use_as_clause" || s == "use_list" || s == "use_wildcard")
        })?;

        let (path, items, is_glob) = Self::parse_use_tree(use_tree)?;

        Some(UseDecl {
            path,
            items,
            is_glob,
        })
    }

    /// Parse a use_tree node recursively
    fn parse_use_tree(node: &SyntaxNode) -> Option<(Vec<String>, Vec<String>, bool)> {
        let mut path = Vec::new();
        let mut items = Vec::new();
        let mut is_glob = false;

        for child in &node.children {
            match &child.kind {
                SyntaxKind::Identifier => {
                    path.push(child.text.clone());
                }
                SyntaxKind::Unknown(s) if s == "identifier" || s == "crate" || s == "self" => {
                    path.push(child.text.clone());
                }
                SyntaxKind::Unknown(s) if s == "scoped_identifier" => {
                    // Recursively parse scoped identifier for the path
                    Self::collect_scoped_path(child, &mut path);
                }
                SyntaxKind::Unknown(s) if s == "use_list" => {
                    // Parse list of items: {Item1, Item2, ...}
                    for item_child in &child.children {
                        if let Some(name) = Self::extract_use_item_name(item_child) {
                            items.push(name);
                        }
                    }
                }
                SyntaxKind::Unknown(s) if s == "use_wildcard" || s == "*" => {
                    is_glob = true;
                }
                SyntaxKind::Unknown(s) if s == "::" => {
                    // Path separator, continue
                }
                _ => {}
            }
        }

        if path.is_empty() && items.is_empty() && !is_glob {
            return None;
        }

        Some((path, items, is_glob))
    }

    /// Collect path segments from a scoped_identifier
    fn collect_scoped_path(node: &SyntaxNode, path: &mut Vec<String>) {
        for child in &node.children {
            match &child.kind {
                SyntaxKind::Identifier => {
                    path.push(child.text.clone());
                }
                SyntaxKind::Unknown(s) if s == "identifier" || s == "crate" || s == "self" => {
                    path.push(child.text.clone());
                }
                SyntaxKind::Unknown(s) if s == "scoped_identifier" => {
                    Self::collect_scoped_path(child, path);
                }
                SyntaxKind::Type => {
                    path.push(child.text.clone());
                }
                SyntaxKind::Unknown(s) if s == "type_identifier" => {
                    path.push(child.text.clone());
                }
                _ => {}
            }
        }
    }

    /// Extract the name from a use item
    fn extract_use_item_name(node: &SyntaxNode) -> Option<String> {
        // Could be identifier, self, or use_as_clause
        if node.kind == SyntaxKind::Identifier
            || matches!(&node.kind, SyntaxKind::Unknown(s) if s == "identifier" || s == "self")
        {
            return Some(node.text.clone());
        }

        // For use_as_clause, get the original name
        if matches!(&node.kind, SyntaxKind::Unknown(s) if s == "use_as_clause") {
            if let Some(first) = node.children.first() {
                return Some(first.text.clone());
            }
        }

        // Check children
        for child in &node.children {
            if child.kind == SyntaxKind::Identifier
                || matches!(&child.kind, SyntaxKind::Unknown(s) if s == "identifier" || s == "self")
            {
                return Some(child.text.clone());
            }
            if child.kind == SyntaxKind::Type
                || matches!(&child.kind, SyntaxKind::Unknown(s) if s == "type_identifier")
            {
                return Some(child.text.clone());
            }
        }

        None
    }

    /// Get the prelude module
    pub fn prelude(&self) -> Option<&CrateModule> {
        self.root.get_module(&["prelude", "v1"])
    }
}

/// Context for compiling and injecting the core library
#[derive(Debug, Default)]
pub struct CoreCompilationContext {
    /// The compiled core crate
    pub core: Option<CoreCrate>,
    /// Whether compilation has been attempted
    pub attempted: bool,
}

impl CoreCompilationContext {
    /// Create a new compilation context
    pub fn new() -> Self {
        Self {
            core: None,
            attempted: false,
        }
    }

    /// Compile the core library if not already done
    pub fn ensure_compiled(&mut self, ctx: &mut LoweringContext) -> Option<&CoreCrate> {
        if !self.attempted {
            self.attempted = true;
            self.core = CoreCrate::compile(ctx);
        }
        self.core.as_ref()
    }

    /// Inject the core prelude into a scope
    ///
    /// This resolves all prelude re-exports and adds them to the scope.
    pub fn inject_prelude(&mut self, ctx: &mut LoweringContext, scope: ScopeId) {
        // Compile core if needed
        if !self.attempted {
            self.attempted = true;
            self.core = CoreCrate::compile(ctx);
        }

        let Some(core) = &self.core else {
            return;
        };

        // Get the prelude module's re-exports and inject them
        if let Some(prelude) = core.root.get_module(&["prelude"]) {
            // First check for v1 submodule
            if let Some(v1) = prelude.children.get("v1") {
                Self::inject_module_exports(ctx, scope, &core.root, v1);
            }
        }

        // Also inject types directly from key modules for simplicity
        // This ensures Option, Result etc. are available even if use parsing fails
        Self::inject_essential_types(ctx, scope, core);
    }

    /// Inject exports from a module's re-exports
    fn inject_module_exports(
        ctx: &mut LoweringContext,
        scope: ScopeId,
        root: &CrateModule,
        module: &CrateModule,
    ) {
        for reexport in &module.reexports {
            Self::inject_reexport(ctx, scope, root, reexport);
        }
    }

    /// Inject a single re-export
    fn inject_reexport(
        ctx: &mut LoweringContext,
        scope: ScopeId,
        root: &CrateModule,
        reexport: &UseDecl,
    ) {
        // Convert "crate::" to module lookup
        let path: Vec<&str> = reexport
            .path
            .iter()
            .filter(|s| *s != "crate")
            .map(|s| s.as_str())
            .collect();

        if path.is_empty() {
            return;
        }

        // Try to resolve the path to a module or item
        if let Some(module) = root.get_module(&path) {
            // Importing from a module
            if reexport.is_glob {
                // Import all public items from the module
                Self::inject_module_contents(ctx, scope, module);
            } else if reexport.items.is_empty() {
                // Import the module itself (not supported yet)
            } else {
                // Import specific items
                for item_name in &reexport.items {
                    if item_name == "self" {
                        // Import the last path segment as a type
                        if let Some(last) = path.last() {
                            if let Some(item) = module.resolve_item(&[last]) {
                                Self::inject_item(ctx, scope, *last, item);
                            }
                        }
                    } else {
                        if let Some(item) = module.resolve_item(&[item_name.as_str()]) {
                            Self::inject_item(ctx, scope, item_name, item);
                        }
                    }
                }
            }
        } else {
            // Try resolving as a direct item path
            let (module_path, item_name) = if path.len() > 1 {
                (&path[..path.len() - 1], path.last().copied())
            } else {
                (&path[..], None)
            };

            if let Some(parent_module) = root.get_module(module_path) {
                if let Some(name) = item_name {
                    // Check if it's a type with variant imports (like Option::{self, Some, None})
                    if let Some(ResolvedItem::Type(type_id)) = parent_module.resolve_item(&[name]) {
                        // Inject the type
                        Self::inject_item(ctx, scope, name, ResolvedItem::Type(type_id));

                        // Inject variants if specified
                        for item_name in &reexport.items {
                            if item_name != "self" {
                                // Register variant as accessible directly
                                Self::inject_enum_variant(ctx, scope, type_id, item_name);
                            }
                        }
                    }
                }
            }
        }
    }

    /// Inject all public contents of a module into scope
    fn inject_module_contents(ctx: &mut LoweringContext, scope: ScopeId, module: &CrateModule) {
        for (name, &type_id) in &module.types {
            Self::inject_item(ctx, scope, name, ResolvedItem::Type(type_id));
        }
        for (name, &trait_id) in &module.traits {
            Self::inject_item(ctx, scope, name, ResolvedItem::Trait(trait_id));
        }
        for (name, &fn_id) in &module.functions {
            Self::inject_item(ctx, scope, name, ResolvedItem::Function(fn_id));
        }
    }

    /// Inject a single item into scope
    fn inject_item(ctx: &mut LoweringContext, scope: ScopeId, name: &str, item: ResolvedItem) {
        let name_interned = ctx.intern(name);
        let kind = match item {
            ResolvedItem::Type(_) => SymbolKind::Type,
            ResolvedItem::Trait(_) => SymbolKind::Trait,
            ResolvedItem::Function(_) => SymbolKind::Function,
        };

        let sym_id = ctx.symbols.add(
            name_interned,
            kind,
            rv_span::Span::new(0, 0),
            scope,
        );
        ctx.scope_tree.add_symbol(scope, name.to_string(), sym_id);

        let def_id = match item {
            ResolvedItem::Type(id) => rv_hir::DefId::Type(id),
            ResolvedItem::Trait(id) => rv_hir::DefId::Trait(id),
            ResolvedItem::Function(id) => rv_hir::DefId::Function(id),
        };
        ctx.symbol_defs.insert(sym_id, def_id);
    }

    /// Inject an enum variant into scope
    fn inject_enum_variant(
        ctx: &mut LoweringContext,
        scope: ScopeId,
        type_id: TypeDefId,
        variant_name: &str,
    ) {
        // Check if this enum exists and has this variant
        if let Some(enum_def) = ctx.enums.get(&type_id) {
            let has_variant = enum_def.variants.iter().any(|v| {
                ctx.interner.resolve(&v.name) == variant_name
            });

            if has_variant {
                let name_interned = ctx.intern(variant_name);
                let sym_id = ctx.symbols.add(
                    name_interned,
                    SymbolKind::EnumVariant,
                    rv_span::Span::new(0, 0),
                    scope,
                );
                ctx.scope_tree.add_symbol(scope, variant_name.to_string(), sym_id);
                ctx.symbol_defs.insert(sym_id, rv_hir::DefId::Type(type_id));
            }
        }
    }

    /// Inject essential types directly (fallback for when use parsing fails)
    ///
    /// This injects items from the Rust core prelude:
    /// - Types: Option, Result (with variants)
    /// - Enums: Ordering (from cmp)
    /// - Marker traits: Copy, Send, Sized, Sync, Unpin
    /// - Function traits: Drop, Fn, FnMut, FnOnce
    /// - Core traits: Clone, Eq, Ord, PartialEq, PartialOrd, From, Into, Default
    fn inject_essential_types(ctx: &mut LoweringContext, scope: ScopeId, core: &CoreCrate) {
        // ===== Types with Variants =====

        // Inject Option and its variants
        if let Some(option_module) = core.root.get_module(&["option"]) {
            if let Some(&type_id) = option_module.types.get("Option") {
                Self::inject_item(ctx, scope, "Option", ResolvedItem::Type(type_id));
                Self::inject_enum_variant(ctx, scope, type_id, "Some");
                Self::inject_enum_variant(ctx, scope, type_id, "None");
            }
        }

        // Inject Result and its variants
        if let Some(result_module) = core.root.get_module(&["result"]) {
            if let Some(&type_id) = result_module.types.get("Result") {
                Self::inject_item(ctx, scope, "Result", ResolvedItem::Type(type_id));
                Self::inject_enum_variant(ctx, scope, type_id, "Ok");
                Self::inject_enum_variant(ctx, scope, type_id, "Err");
            }
        }

        // Inject Ordering enum and its variants (from cmp module)
        if let Some(cmp_module) = core.root.get_module(&["cmp"]) {
            if let Some(&type_id) = cmp_module.types.get("Ordering") {
                Self::inject_item(ctx, scope, "Ordering", ResolvedItem::Type(type_id));
                Self::inject_enum_variant(ctx, scope, type_id, "Less");
                Self::inject_enum_variant(ctx, scope, type_id, "Equal");
                Self::inject_enum_variant(ctx, scope, type_id, "Greater");
            }

            // Inject comparison traits
            for trait_name in &["Eq", "Ord", "PartialEq", "PartialOrd"] {
                if let Some(&trait_id) = cmp_module.traits.get(*trait_name) {
                    Self::inject_item(ctx, scope, trait_name, ResolvedItem::Trait(trait_id));
                }
            }
        }

        // ===== Marker Traits (from marker module) =====
        if let Some(marker_module) = core.root.get_module(&["marker"]) {
            for trait_name in &["Copy", "Send", "Sized", "Sync", "Unpin"] {
                if let Some(&trait_id) = marker_module.traits.get(*trait_name) {
                    Self::inject_item(ctx, scope, trait_name, ResolvedItem::Trait(trait_id));
                }
            }
        }

        // ===== Function Traits (from ops module) =====
        if let Some(ops_module) = core.root.get_module(&["ops"]) {
            for trait_name in &["Drop", "Fn", "FnMut", "FnOnce"] {
                if let Some(&trait_id) = ops_module.traits.get(*trait_name) {
                    Self::inject_item(ctx, scope, trait_name, ResolvedItem::Trait(trait_id));
                }
            }
        }

        // ===== Clone Trait (from clone module) =====
        if let Some(clone_module) = core.root.get_module(&["clone"]) {
            if let Some(&trait_id) = clone_module.traits.get("Clone") {
                Self::inject_item(ctx, scope, "Clone", ResolvedItem::Trait(trait_id));
            }
        }

        // ===== Conversion Traits (from convert module) =====
        if let Some(convert_module) = core.root.get_module(&["convert"]) {
            for trait_name in &["AsMut", "AsRef", "From", "Into"] {
                if let Some(&trait_id) = convert_module.traits.get(*trait_name) {
                    Self::inject_item(ctx, scope, trait_name, ResolvedItem::Trait(trait_id));
                }
            }
        }

        // ===== Default Trait (from default module) =====
        if let Some(default_module) = core.root.get_module(&["default"]) {
            if let Some(&trait_id) = default_module.traits.get("Default") {
                Self::inject_item(ctx, scope, "Default", ResolvedItem::Trait(trait_id));
            }
        }

        // ===== Iterator Traits (from iter module) =====
        if let Some(iter_module) = core.root.get_module(&["iter"]) {
            for trait_name in &[
                "Iterator",
                "IntoIterator",
                "DoubleEndedIterator",
                "ExactSizeIterator",
                "Extend",
            ] {
                if let Some(&trait_id) = iter_module.traits.get(*trait_name) {
                    Self::inject_item(ctx, scope, trait_name, ResolvedItem::Trait(trait_id));
                }
            }
        }

        // ===== Memory Functions (from mem module) =====
        if let Some(mem_module) = core.root.get_module(&["mem"]) {
            for fn_name in &["drop", "size_of", "size_of_val", "align_of", "align_of_val"] {
                if let Some(&fn_id) = mem_module.functions.get(*fn_name) {
                    Self::inject_item(ctx, scope, fn_name, ResolvedItem::Function(fn_id));
                }
            }
        }
    }
}

// Re-exports for backwards compatibility
pub use CrateModule as CompiledModule;
pub use CoreCrate as CoreLibrary;
/// Type alias for backwards compatibility with older code
pub type CoreLibraryContext = CoreCompilationContext;

/// Kind of prelude item (for backwards compatibility)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PreludeItemKind {
    /// Enum type with variants that should be injected (e.g., Option with Some/None)
    EnumWithVariants,
    /// Trait definition
    Trait,
    /// Function definition
    Function,
}

/// A re-export from the prelude (for backwards compatibility)
#[derive(Debug, Clone)]
pub struct PreludeReExport {
    /// Source path of the re-export (e.g., `["crate", "option", "Option"]`)
    pub source_path: Vec<String>,
    /// Specific items to import (e.g., `["self", "Some", "None"]`)
    pub items: Vec<String>,
    /// Kind of item being re-exported
    pub kind: PreludeItemKind,
}
