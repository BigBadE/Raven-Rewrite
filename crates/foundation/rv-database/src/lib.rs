//! Salsa database setup for incremental compilation
//!
//! This crate provides the core database infrastructure for the Raven compiler.
//! It uses Salsa for incremental computation and memoization.

use anyhow::Result;
use rv_hir::{ConstId, FunctionId, ImplId, StaticId, TraitId, TypeDefId};
use rv_intern::Interner;
use rv_syntax::{SyntaxKind, SyntaxNode};
use rv_vfs::VirtualFileSystem;
use salsa::Setter;
use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Input: Source file registered in the system
#[salsa::input]
pub struct SourceFile {
    /// The path to the file
    pub path: PathBuf,
    /// The contents of the file (input)
    pub text: String,
}

// Tracked functions (queries)
#[salsa::tracked]
pub fn parse_file(db: &dyn RavenDb, file: SourceFile) -> ParseResult {
    let text = file.text(db);
    let result = rv_parser::parse_source(&text);

    ParseResult {
        syntax: result.syntax,
        errors: result.errors,
    }
}

#[salsa::tracked]
pub fn lower_to_hir(db: &dyn RavenDb, file: SourceFile) -> Arc<HirFileData> {
    let parse_result = parse_file(db, file);

    if let Some(syntax) = &parse_result.syntax {
        let ctx = rv_hir_lower::lower_source_file(syntax);

        Arc::new(HirFileData {
            functions: ctx.functions,
            structs: ctx.structs,
            enums: ctx.enums,
            traits: ctx.traits,
            impl_blocks: ctx.impl_blocks,
            type_aliases: ctx.type_aliases,
            const_items: ctx.const_items,
            static_items: ctx.static_items,
            types: ctx.types,
            interner: ctx.interner,
            lang_items: ctx.lang_items,
            default_method_bodies: ctx.default_method_bodies,
            features: ctx.features,
        })
    } else {
        // Return empty HIR if parsing failed
        Arc::new(HirFileData {
            functions: std::collections::HashMap::new(),
            structs: std::collections::HashMap::new(),
            enums: std::collections::HashMap::new(),
            traits: std::collections::HashMap::new(),
            impl_blocks: std::collections::HashMap::new(),
            type_aliases: std::collections::HashMap::new(),
            const_items: std::collections::HashMap::new(),
            static_items: std::collections::HashMap::new(),
            types: la_arena::Arena::new(),
            interner: rv_intern::Interner::new(),
            lang_items: rv_hir::LangItemRegistry::default(),
            default_method_bodies: std::collections::HashSet::new(),
            features: rv_hir::FeatureSet::new(),
        })
    }
}

#[salsa::tracked]
pub fn file_functions(db: &dyn RavenDb, file: SourceFile) -> Arc<Vec<FunctionId>> {
    let hir = lower_to_hir(db, file);
    let functions = hir.functions.keys().copied().collect();
    Arc::new(functions)
}

#[salsa::tracked]
pub fn function_hir(
    db: &dyn RavenDb,
    file: SourceFile,
    function: FunctionId,
) -> Arc<rv_hir::Function> {
    let hir = lower_to_hir(db, file);
    let func = hir.functions.get(&function).unwrap_or_else(|| {
        panic!(
            "ICE: Function {:?} not found in HIR. \
             This indicates a broken function ID reference.",
            function
        )
    });
    Arc::new(func.clone())
}

#[salsa::tracked]
pub fn file_type_defs(db: &dyn RavenDb, file: SourceFile) -> Arc<Vec<TypeDefId>> {
    let hir = lower_to_hir(db, file);
    let mut type_defs = Vec::new();
    type_defs.extend(hir.structs.keys().copied());
    type_defs.extend(hir.enums.keys().copied());
    Arc::new(type_defs)
}

#[salsa::tracked]
pub fn file_traits(db: &dyn RavenDb, file: SourceFile) -> Arc<Vec<TraitId>> {
    let hir = lower_to_hir(db, file);
    let traits = hir.traits.keys().copied().collect();
    Arc::new(traits)
}

#[salsa::tracked]
pub fn file_impls(db: &dyn RavenDb, file: SourceFile) -> Arc<Vec<ImplId>> {
    let hir = lower_to_hir(db, file);
    let impls = hir.impl_blocks.keys().copied().collect();
    Arc::new(impls)
}

#[salsa::tracked]
pub fn infer_function_types(
    db: &dyn RavenDb,
    file: SourceFile,
    function: FunctionId,
) -> Arc<InferenceResult> {
    let func_hir = function_hir(db, file, function);
    let hir_data = lower_to_hir(db, file);

    // Create type inference with HIR context
    let mut type_inference = rv_ty::TypeInference::with_hir_context(
        &hir_data.impl_blocks,
        &hir_data.functions,
        &hir_data.types,
        &hir_data.structs,
        &hir_data.enums,
        &hir_data.interner,
    );

    type_inference.set_const_static_items(&hir_data.const_items, &hir_data.static_items);

    // Run type inference on the REQUESTED function only
    // Each function gets its own TypeInference instance (via Salsa caching) to avoid ExprId conflicts
    // Generic functions will be type-inferred during monomorphization with concrete types
    if func_hir.generics.is_empty() {
        type_inference.infer_function(&func_hir);
    }

    // Extract results from type inference
    let result = type_inference.finish();

    Arc::new(InferenceResult {
        context: result.ctx,
        errors: result.errors,
        lifetime_constraints: result.lifetime_constraints,
    })
}

#[salsa::tracked]
pub fn function_signature(
    db: &dyn RavenDb,
    file: SourceFile,
    function: FunctionId,
) -> Arc<FunctionSignature> {
    let func_hir = function_hir(db, file, function);

    Arc::new(FunctionSignature {
        params: func_hir.parameters.iter().map(|param| param.ty).collect(),
        return_type: func_hir.return_type,
        generic_params: func_hir.generics.clone(),
    })
}

// ARCHITECTURE: Method resolution removed from rv-database
// Method resolution now lives in rv-mir-lower where it belongs during HIR → MIR lowering.
// This removes duplication and keeps database focused on incremental queries.

#[salsa::tracked]
pub fn lower_function_to_mir(
    db: &dyn RavenDb,
    file: SourceFile,
    function: FunctionId,
) -> Arc<rv_mir::MirFunction> {
    let func_hir = function_hir(db, file, function);
    let inference = infer_function_types(db, file, function);
    let hir_data = lower_to_hir(db, file);

    // Clone context to get a mutable version for normalization
    let mut ty_ctx = inference.context.clone();

    // Evaluate const and static items
    let const_values =
        rv_const_eval::evaluate_const_items(&hir_data.const_items, &hir_data.interner);
    let static_values = rv_const_eval::evaluate_static_items(
        &hir_data.static_items,
        &hir_data.const_items,
        &const_values,
        &hir_data.interner,
    );

    // Lower to MIR
    let mir_result = rv_mir_lower::LoweringContext::lower_function(
        &func_hir,
        &mut ty_ctx,
        &hir_data.structs,
        &hir_data.enums,
        &hir_data.impl_blocks,
        &hir_data.functions,
        &hir_data.types,
        &hir_data.traits,
        &hir_data.interner,
        &hir_data.lang_items,
        &const_values,
        &static_values,
    );

    Arc::new(mir_result.function)
}

// ===== Multi-File Module Discovery =====

/// Discovered module file with its module path relative to the crate root.
#[derive(Debug, Clone)]
pub struct ModuleFile {
    /// Absolute path to the source file
    pub path: PathBuf,
    /// Module path segments (e.g., ["utils"] for mod utils; or ["math", "arithmetic"])
    pub module_path: Vec<String>,
}

/// Discover all source files in a project by following `mod` declarations.
///
/// Starting from `root_path` (typically `src/main.rs`), parses each file's CST
/// to find `mod foo;` declarations (external modules without a body), then resolves
/// them to either `foo.rs` or `foo/mod.rs` relative to the declaring file.
///
/// Returns a list of all discovered files including the root.
pub fn discover_module_files(root_path: &Path) -> Result<Vec<ModuleFile>> {
    let mut discovered = Vec::new();
    let mut visited = HashSet::new();

    discover_recursive(root_path, &[], &mut discovered, &mut visited)?;

    Ok(discovered)
}

fn discover_recursive(
    file_path: &Path,
    module_path: &[String],
    discovered: &mut Vec<ModuleFile>,
    visited: &mut HashSet<PathBuf>,
) -> Result<()> {
    let canonical = file_path
        .canonicalize()
        .unwrap_or_else(|_| file_path.to_path_buf());
    if !visited.insert(canonical.clone()) {
        return Ok(()); // Already visited
    }

    discovered.push(ModuleFile {
        path: file_path.to_path_buf(),
        module_path: module_path.to_vec(),
    });

    // Read and parse the file to find mod declarations
    let source = std::fs::read_to_string(file_path)?;
    let parse_result = rv_parser::parse_source(&source);

    let syntax = match parse_result.syntax {
        Some(s) => s,
        None => {
            anyhow::bail!(
                "Failed to parse {} during module discovery: {} parse error(s)",
                file_path.display(),
                parse_result.errors.len()
            );
        }
    };

    // Find mod declarations without bodies (external module references)
    let parent_dir = file_path.parent().unwrap_or(Path::new("."));
    let file_stem = file_path.file_stem().and_then(|s| s.to_str()).unwrap_or("");

    // If this file is mod.rs, modules are resolved relative to its directory.
    // If this file is foo.rs, modules are resolved relative to a sibling foo/ directory.
    let module_dir = if file_stem == "mod" || file_stem == "main" || file_stem == "lib" {
        parent_dir.to_path_buf()
    } else {
        parent_dir.join(file_stem)
    };

    for child in &syntax.children {
        if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "mod_item" {
                // Check if this is an external module (no body)
                let has_body = child.children.iter().any(|c| {
                    matches!(c.kind, SyntaxKind::Block)
                        || matches!(&c.kind, SyntaxKind::Unknown(s) if s == "declaration_list")
                });

                if has_body {
                    continue; // Inline module, no file to discover
                }

                // Extract module name
                let mod_name = child
                    .children
                    .iter()
                    .find(|c| c.kind == SyntaxKind::Identifier)
                    .map(|c| c.text.clone());

                // Check for #[path = "..."] attribute
                let custom_path = extract_path_attribute(child);

                if let Some(name) = mod_name {
                    let mut child_path = module_path.to_vec();
                    child_path.push(name.clone());

                    // If #[path = "..."] is specified, use that path relative to current file
                    if let Some(custom) = custom_path {
                        let resolved = parent_dir.join(&custom);
                        if resolved.exists() {
                            discover_recursive(&resolved, &child_path, discovered, visited)?;
                        }
                    } else {
                        // Try to resolve: module_dir/name.rs or module_dir/name/mod.rs
                        let file_rs = module_dir.join(format!("{name}.rs"));
                        let mod_rs = module_dir.join(&name).join("mod.rs");

                        if file_rs.exists() {
                            discover_recursive(&file_rs, &child_path, discovered, visited)?;
                        } else if mod_rs.exists() {
                            discover_recursive(&mod_rs, &child_path, discovered, visited)?;
                        }
                        // If neither exists, silently skip — the compiler will report
                        // an error later during name resolution.
                    }
                }
            }
        }
    }

    Ok(())
}

/// Extract the path from a `#[path = "..."]` attribute on a mod item.
///
/// Looks for attribute nodes that contain `path` and a string literal value.
fn extract_path_attribute(mod_item: &SyntaxNode) -> Option<String> {
    for child in &mod_item.children {
        // Look for attribute_item nodes
        if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "attribute_item" || s == "attribute" {
                // Look for the attribute content
                let mut is_path_attr = false;
                let mut path_value = None;

                for attr_child in &child.children {
                    // Check for "path" identifier
                    if attr_child.kind == SyntaxKind::Identifier && attr_child.text == "path" {
                        is_path_attr = true;
                    }
                    // Look for string literal value
                    if let SyntaxKind::Unknown(ref s2) = attr_child.kind {
                        if s2 == "string_literal" || s2 == "string_content" {
                            // Remove quotes from the string
                            let text = attr_child.text.trim_matches('"');
                            path_value = Some(text.to_string());
                        }
                        // Also check nested children for the value
                        if s2 == "meta_item" || s2 == "attribute" {
                            for meta_child in &attr_child.children {
                                if meta_child.kind == SyntaxKind::Identifier
                                    && meta_child.text == "path"
                                {
                                    is_path_attr = true;
                                }
                                if let SyntaxKind::Unknown(ref s3) = meta_child.kind {
                                    if s3 == "string_literal" {
                                        let text = meta_child.text.trim_matches('"');
                                        path_value = Some(text.to_string());
                                    }
                                }
                            }
                        }
                    }
                }

                if is_path_attr {
                    return path_value;
                }
            }
        }
    }
    None
}

// ===== Project-Level Compilation =====

/// A module's HIR data paired with its module path.
#[derive(Debug, Clone)]
pub struct ModuleHirData {
    /// The module path (empty for root)
    pub module_path: Vec<String>,
    /// This module's HIR data (functions, structs, etc.)
    pub hir: Arc<HirFileData>,
}

/// Project-level HIR data: each file is lowered separately, and a module index
/// provides cross-module name resolution.
#[derive(Debug, Clone)]
pub struct ProjectHirData {
    /// Per-module HIR data, indexed by module path
    pub modules: std::collections::HashMap<Vec<String>, ModuleHirData>,
    /// Module item index: maps module path to name→FunctionId
    pub module_functions: std::collections::HashMap<
        Vec<String>,
        std::collections::HashMap<String, (FunctionId, Vec<String>)>,
    >,
    /// Quick lookup: all files in the project
    pub module_files: Vec<ModuleFile>,
}

impl ProjectHirData {
    /// Get the root module's HIR data (main.rs / lib.rs).
    pub fn root_hir(&self) -> Option<&Arc<HirFileData>> {
        self.modules.get(&Vec::<String>::new()).map(|m| &m.hir)
    }

    /// Find a function by name in a specific module.
    pub fn find_function_in_module(
        &self,
        module_path: &[String],
        function_name: &str,
    ) -> Option<(FunctionId, &Arc<HirFileData>)> {
        let module = self.modules.get(module_path)?;
        let hir = &module.hir;
        for (id, func) in &hir.functions {
            if hir.interner.resolve(&func.name) == function_name {
                return Some((*id, hir));
            }
        }
        None
    }

    /// Resolve a scoped call like `utils::get_value()`.
    ///
    /// Given a path like `["utils"]` and a function name `"get_value"`,
    /// finds the function in the corresponding module.
    pub fn resolve_cross_module_call(
        &self,
        module_path: &[String],
        function_name: &str,
    ) -> Option<(FunctionId, &Arc<HirFileData>)> {
        self.find_function_in_module(module_path, function_name)
    }
}

/// Lower an entire project starting from the root file.
///
/// Discovers all module files, lowers each independently, and builds
/// a module index for cross-module resolution.
pub fn lower_project(root_path: &Path) -> Result<ProjectHirData> {
    let module_files = discover_module_files(root_path)?;

    let mut project = ProjectHirData {
        modules: std::collections::HashMap::new(),
        module_functions: std::collections::HashMap::new(),
        module_files: module_files.clone(),
    };

    // Track the next available FunctionId across all modules so each
    // module gets globally unique IDs that don't collide during compilation.
    let mut next_func_id_offset: u32 = 0;

    for module_file in &module_files {
        let source = std::fs::read_to_string(&module_file.path)?;
        let parse_result = rv_parser::parse_source(&source);

        let syntax = match parse_result.syntax {
            Some(s) => s,
            None => continue,
        };

        let ctx = rv_hir_lower::lower_source_file_with_id_offset(&syntax, next_func_id_offset);
        next_func_id_offset = ctx.next_function_id();

        // Build function name index for this module
        let mut func_index = std::collections::HashMap::new();
        for (id, func) in &ctx.functions {
            let name = ctx.interner.resolve(&func.name).to_string();
            func_index.insert(name, (*id, module_file.module_path.clone()));
        }

        let hir = Arc::new(HirFileData {
            functions: ctx.functions,
            structs: ctx.structs,
            enums: ctx.enums,
            traits: ctx.traits,
            impl_blocks: ctx.impl_blocks,
            type_aliases: ctx.type_aliases,
            const_items: ctx.const_items,
            static_items: ctx.static_items,
            types: ctx.types,
            interner: ctx.interner,
            lang_items: ctx.lang_items,
            default_method_bodies: ctx.default_method_bodies,
            features: ctx.features,
        });

        project.modules.insert(
            module_file.module_path.clone(),
            ModuleHirData {
                module_path: module_file.module_path.clone(),
                hir,
            },
        );

        project
            .module_functions
            .insert(module_file.module_path.clone(), func_index);
    }

    Ok(project)
}

/// Main database trait for the Raven compiler
#[salsa::db]
pub trait RavenDb: salsa::Database {
    /// Get the virtual file system
    fn vfs(&self) -> &VirtualFileSystem;

    /// Get the string interner
    fn interner(&self) -> &Interner;
}

/// Parse result from parsing a file
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseResult {
    /// Converted syntax tree
    pub syntax: Option<rv_syntax::SyntaxNode>,
    /// Parse errors with detailed diagnostics
    pub errors: Vec<rv_parser::ParseError>,
}

/// HIR file data containing all top-level items
#[derive(Debug, Clone, PartialEq)]
pub struct HirFileData {
    /// Functions defined in this file
    pub functions: std::collections::HashMap<FunctionId, rv_hir::Function>,
    /// Type definitions
    pub structs: std::collections::HashMap<TypeDefId, rv_hir::StructDef>,
    /// Enum definitions
    pub enums: std::collections::HashMap<TypeDefId, rv_hir::EnumDef>,
    /// Trait definitions
    pub traits: std::collections::HashMap<TraitId, rv_hir::TraitDef>,
    /// Implementation blocks
    pub impl_blocks: std::collections::HashMap<ImplId, rv_hir::ImplBlock>,
    /// Type alias definitions
    pub type_aliases: std::collections::HashMap<rv_hir::TypeAliasId, rv_hir::TypeAlias>,
    /// Const item definitions
    pub const_items: std::collections::HashMap<ConstId, rv_hir::ConstItem>,
    /// Static item definitions
    pub static_items: std::collections::HashMap<StaticId, rv_hir::StaticItem>,
    /// HIR types arena
    pub types: la_arena::Arena<rv_hir::Type>,
    /// String interner
    pub interner: rv_intern::Interner,
    /// Lang item registry
    pub lang_items: rv_hir::LangItemRegistry,
    /// FunctionIds of default trait method bodies (must not be compiled standalone)
    pub default_method_bodies: std::collections::HashSet<FunctionId>,
    /// Enabled unstable features from `#![feature(...)]` attributes
    pub features: rv_hir::FeatureSet,
}

/// Type inference result
#[derive(Debug, Clone, PartialEq)]
pub struct InferenceResult {
    /// Type context with inferred types
    pub context: rv_ty::TyContext,
    /// Any type errors encountered
    pub errors: Vec<rv_ty::TypeError>,
    /// Lifetime outlives constraints: (sub, sup, source_expr)
    pub lifetime_constraints: Vec<(
        rv_span::LifetimeId,
        rv_span::LifetimeId,
        Option<rv_hir::ExprId>,
    )>,
}

/// Function signature for type checking
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionSignature {
    /// Parameter types
    pub params: Vec<rv_hir::TypeId>,
    /// Return type
    pub return_type: Option<rv_hir::TypeId>,
    /// Generic parameters
    pub generic_params: Vec<rv_hir::GenericParam>,
}

/// Root database implementation
#[salsa::db]
#[derive(Clone)]
pub struct RootDatabase {
    storage: salsa::Storage<Self>,
    vfs: VirtualFileSystem,
    interner: Interner,
}

impl RootDatabase {
    /// Creates a new root database
    #[must_use]
    pub fn new() -> Self {
        Self {
            storage: salsa::Storage::default(),
            vfs: VirtualFileSystem::new(),
            interner: Interner::new(),
        }
    }

    /// Registers a file and creates a `SourceFile` input
    ///
    /// # Errors
    ///
    /// Returns an error if file registration fails
    pub fn register_file(&mut self, path: impl Into<PathBuf>) -> Result<SourceFile> {
        let path = path.into();
        let contents = std::fs::read_to_string(&path)?;
        let _file_id = self.vfs.register_file(&path)?;
        Ok(SourceFile::new(self, path, contents))
    }

    /// Registers a virtual file with the given contents (for testing)
    ///
    /// This does not require the file to exist on disk.
    #[must_use]
    pub fn register_virtual_file(&mut self, path: impl Into<PathBuf>, contents: String) -> SourceFile {
        let path = path.into();
        // VFS registration is optional for virtual files - they live purely in Salsa
        let _ = self.vfs.register_file(&path);
        SourceFile::new(self, path, contents)
    }

    /// Sets file contents directly (useful for testing and incremental updates)
    pub fn set_file_contents(&mut self, source_file: SourceFile, contents: String) {
        source_file.set_text(self).to(contents);
    }

    /// Gets file contents
    #[must_use]
    pub fn get_file_contents(&self, source_file: SourceFile) -> String {
        source_file.text(self)
    }
}

impl Default for RootDatabase {
    fn default() -> Self {
        Self::new()
    }
}

#[salsa::db]
impl salsa::Database for RootDatabase {}

#[salsa::db]
impl RavenDb for RootDatabase {
    fn vfs(&self) -> &VirtualFileSystem {
        &self.vfs
    }

    fn interner(&self) -> &Interner {
        &self.interner
    }
}
