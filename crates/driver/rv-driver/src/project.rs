//! Multi-file project compilation
//!
//! This module provides infrastructure for compiling multi-file Rust projects.
//! It handles module discovery, cross-file name resolution, and unified compilation.

use anyhow::Result;
use rv_database::{discover_module_files, ModuleFile};
use rv_hir::{
    EnumDef, Function, FunctionId, ImplBlock, ImplId, LangItemRegistry, ModuleId, StructDef,
    TraitDef, TraitId, Type, TypeDefId, UseItem, Visibility,
};
use rv_intern::Interner;
use rv_mir::MirFunction;
use rv_resolve::ModuleResolver;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use thiserror::Error;

/// Errors that can occur during project compilation
#[derive(Debug, Error)]
pub enum ProjectCompilationError {
    /// Failed to discover module files
    #[error("Failed to discover module files: {0}")]
    ModuleDiscovery(#[from] anyhow::Error),

    /// Failed to parse a source file
    #[error("Failed to parse {path}: {message}")]
    ParseError {
        /// Path to the file that failed to parse
        path: PathBuf,
        /// Error message
        message: String,
    },

    /// Failed to resolve a module path
    #[error("Failed to resolve module path: {0:?}")]
    ModuleResolution(Vec<String>),

    /// Cross-module call resolution failed
    #[error("Cannot resolve function '{function}' in module '{module}'")]
    FunctionNotFound {
        /// Module path
        module: String,
        /// Function name
        function: String,
    },
}

/// A compiled module's HIR data
#[derive(Debug, Clone)]
pub struct CompiledModule {
    /// Module path (empty for root)
    pub module_path: Vec<String>,
    /// Source file path
    pub source_path: PathBuf,
    /// Functions defined in this module
    pub functions: HashMap<FunctionId, Function>,
    /// Structs defined in this module
    pub structs: HashMap<TypeDefId, StructDef>,
    /// Enums defined in this module
    pub enums: HashMap<TypeDefId, EnumDef>,
    /// Traits defined in this module
    pub traits: HashMap<TraitId, TraitDef>,
    /// Impl blocks in this module
    pub impl_blocks: HashMap<ImplId, ImplBlock>,
    /// Type arena for this module
    pub types: la_arena::Arena<Type>,
    /// Lang items discovered in this module
    pub lang_items: LangItemRegistry,
    /// Use declarations in this module
    pub use_items: Vec<UseItem>,
}

/// Result of compiling a multi-file project
#[derive(Debug)]
pub struct ProjectCompilation {
    /// All compiled modules, keyed by module path
    pub modules: HashMap<Vec<String>, CompiledModule>,
    /// Module resolver for cross-module lookups
    pub resolver: ModuleResolver,
    /// Unified interner shared across all modules
    pub interner: Interner,
    /// Cross-module function index: module_path -> (name -> FunctionId)
    pub function_index: HashMap<Vec<String>, HashMap<String, FunctionId>>,
    /// All source files in the project
    pub source_files: Vec<ModuleFile>,
    /// Root module ID
    pub root_module_id: ModuleId,
}

impl ProjectCompilation {
    /// Get the root module
    #[must_use]
    pub fn root_module(&self) -> Option<&CompiledModule> {
        self.modules.get(&Vec::new())
    }

    /// Find a function by module path and name
    #[must_use]
    pub fn find_function(&self, module_path: &[String], name: &str) -> Option<&Function> {
        let module = self.modules.get(module_path)?;
        let func_id = self.function_index.get(module_path)?.get(name)?;
        module.functions.get(func_id)
    }

    /// Resolve a cross-module function call (e.g., `utils::get_value`)
    ///
    /// Returns the function and the module it's defined in.
    #[must_use]
    pub fn resolve_cross_module_call(
        &self,
        module_path: &[String],
        function_name: &str,
    ) -> Option<(&Function, &CompiledModule)> {
        let module = self.modules.get(module_path)?;
        let func_id = self.function_index.get(module_path)?.get(function_name)?;
        let function = module.functions.get(func_id)?;
        Some((function, module))
    }

    /// Get all functions across all modules
    #[must_use]
    pub fn all_functions(&self) -> Vec<(&Function, &CompiledModule)> {
        let mut result = Vec::new();
        for module in self.modules.values() {
            for function in module.functions.values() {
                result.push((function, module));
            }
        }
        result
    }

    /// Get all non-generic functions that can be compiled directly
    #[must_use]
    pub fn compilable_functions(&self) -> Vec<(&Function, &CompiledModule)> {
        self.all_functions()
            .into_iter()
            .filter(|(f, _)| f.generics.is_empty())
            .collect()
    }
}

/// Compile a multi-file project starting from the root file.
///
/// This function:
/// 1. Discovers all module files by following `mod` declarations
/// 2. Parses and lowers each file to HIR
/// 3. Builds a unified symbol table across all modules
/// 4. Sets up cross-module name resolution
///
/// # Arguments
/// * `root_path` - Path to the root file (main.rs or lib.rs)
///
/// # Returns
/// A `ProjectCompilation` containing all compiled modules and resolution infrastructure.
pub fn compile_project(root_path: impl AsRef<Path>) -> Result<ProjectCompilation, ProjectCompilationError> {
    let root_path = root_path.as_ref();

    // Step 1: Discover all module files
    let module_files = discover_module_files(root_path)?;

    // Step 2: Create shared interner
    let mut interner = Interner::new();

    // Step 3: Lower each module file to HIR with globally unique IDs
    let mut modules = HashMap::new();
    let mut function_index: HashMap<Vec<String>, HashMap<String, FunctionId>> = HashMap::new();
    let mut next_func_id: u32 = 0;
    let mut next_struct_id: u32 = 0;
    let mut next_enum_id: u32 = 0;
    let mut next_trait_id: u32 = 0;
    let mut next_impl_id: u32 = 0;

    for module_file in &module_files {
        let source = std::fs::read_to_string(&module_file.path).map_err(|e| {
            ProjectCompilationError::ParseError {
                path: module_file.path.clone(),
                message: e.to_string(),
            }
        })?;

        let parse_result = rv_parser::parse_source(&source);
        let syntax = parse_result.syntax.ok_or_else(|| {
            ProjectCompilationError::ParseError {
                path: module_file.path.clone(),
                message: format!("{} parse errors", parse_result.errors.len()),
            }
        })?;

        // Lower with ID offset to ensure globally unique IDs
        let ctx = rv_hir_lower::lower_source_file_with_id_offset(&syntax, next_func_id);

        // Update ID counters for next module
        let max_func_id = ctx.functions.keys().map(|id| id.0).max().unwrap_or(0);
        next_func_id = max_func_id + 1;

        let max_struct_id = ctx.structs.keys().map(|id| id.0).max().unwrap_or(next_struct_id);
        next_struct_id = max_struct_id + 1;

        let max_enum_id = ctx.enums.keys().map(|id| id.0).max().unwrap_or(next_enum_id);
        next_enum_id = max_enum_id + 1;

        let max_trait_id = ctx.traits.keys().map(|id| id.0).max().unwrap_or(next_trait_id);
        next_trait_id = max_trait_id + 1;

        let max_impl_id = ctx.impl_blocks.keys().map(|id| id.0).max().unwrap_or(next_impl_id);
        next_impl_id = max_impl_id + 1;

        // Build function index for this module
        let mut func_idx = HashMap::new();
        for (id, func) in &ctx.functions {
            let name = ctx.interner.resolve(&func.name).to_string();
            func_idx.insert(name, *id);
        }
        function_index.insert(module_file.module_path.clone(), func_idx);

        // Merge interner symbols
        // Note: In a real implementation, we'd share the interner across all modules
        // For now, we copy the interner from the first module
        if modules.is_empty() {
            interner = ctx.interner.clone();
        }

        let compiled = CompiledModule {
            module_path: module_file.module_path.clone(),
            source_path: module_file.path.clone(),
            functions: ctx.functions,
            structs: ctx.structs,
            enums: ctx.enums,
            traits: ctx.traits,
            impl_blocks: ctx.impl_blocks,
            types: ctx.types,
            lang_items: ctx.lang_items,
            use_items: ctx.use_items,
        };

        modules.insert(module_file.module_path.clone(), compiled);
    }

    // Step 4: Build module resolver
    let root_module_id = ModuleId(0);
    let mut resolver = ModuleResolver::new(root_module_id);

    // Register all modules with the resolver
    let mut module_id_counter: u32 = 0;
    let mut module_path_to_id: HashMap<Vec<String>, ModuleId> = HashMap::new();

    for module_file in &module_files {
        let module_id = ModuleId(module_id_counter);
        module_id_counter += 1;
        module_path_to_id.insert(module_file.module_path.clone(), module_id);
    }

    // Register modules and their exports
    for module_file in &module_files {
        let module_id = module_path_to_id[&module_file.module_path];
        let parent_id = if module_file.module_path.is_empty() {
            None
        } else {
            let parent_path: Vec<String> = module_file.module_path[..module_file.module_path.len() - 1].to_vec();
            module_path_to_id.get(&parent_path).copied()
        };

        // Create a minimal ModuleDef for registration
        let module_name = if module_file.module_path.is_empty() {
            interner.intern("crate")
        } else {
            interner.intern(module_file.module_path.last().unwrap())
        };

        let module_def = rv_hir::ModuleDef {
            id: module_id,
            name: module_name,
            items: Vec::new(),
            submodules: Vec::new(),
            visibility: Visibility::Public,
            span: rv_span::FileSpan::synthetic(),
        };

        resolver.register_module(&module_def, parent_id);

        // Register this module's exports
        if let Some(compiled) = modules.get(&module_file.module_path) {
            // Register functions with their actual visibility
            for (func_id, func) in &compiled.functions {
                resolver.register_function(module_id, func.name, *func_id, func.visibility);
            }

            // Register structs with their actual visibility
            for (type_id, struct_def) in &compiled.structs {
                resolver.register_struct(module_id, struct_def.name, *type_id, struct_def.visibility);
            }

            // Register enums with their actual visibility
            for (type_id, enum_def) in &compiled.enums {
                resolver.register_enum(module_id, enum_def.name, *type_id, enum_def.visibility);
            }

            // Register traits with their actual visibility
            for (trait_id, trait_def) in &compiled.traits {
                resolver.register_trait(module_id, trait_def.name, *trait_id, trait_def.visibility);
            }
        }

        // Register submodules
        if let Some(parent_id) = parent_id {
            resolver.register_submodule(
                parent_id,
                module_name,
                module_id,
                Visibility::Public, // Modules declared with `mod` are visible to parent
            );
        }
    }

    // Step 5: Process use declarations for each module
    // This must happen after all modules and items are registered so paths can be resolved.
    for module_file in &module_files {
        let module_id = module_path_to_id[&module_file.module_path];
        if let Some(compiled) = modules.get(&module_file.module_path) {
            // Process regular use declarations
            let use_errors = resolver.process_use_declarations(module_id, &compiled.use_items);

            // Log resolution errors (in production, these would be reported to the user)
            for err in use_errors {
                eprintln!(
                    "Warning: Failed to resolve use in {:?}: {:?}",
                    module_file.module_path, err
                );
            }

            // Process glob imports (use foo::*)
            // Glob imports are identified by having a path ending with "*"
            for use_item in &compiled.use_items {
                if !use_item.path.is_empty() {
                    let last_segment = interner.resolve(use_item.path.last().unwrap());
                    if last_segment == "*" {
                        // This is a glob import - resolve the module path (without the "*")
                        let module_path: Vec<_> = use_item.path[..use_item.path.len() - 1].to_vec();
                        if !module_path.is_empty() {
                            // Resolve the target module
                            if let Ok(resolved) =
                                resolver.resolve_path(module_id, &module_path, use_item.span)
                            {
                                if let rv_hir::DefId::Module(target_module_id) = resolved.def {
                                    if let Err(e) = resolver.process_glob_import(
                                        module_id,
                                        target_module_id,
                                        use_item.span,
                                    ) {
                                        eprintln!(
                                            "Warning: Failed glob import in {:?}: {:?}",
                                            module_file.module_path, e
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    Ok(ProjectCompilation {
        modules,
        resolver,
        interner,
        function_index,
        source_files: module_files,
        root_module_id,
    })
}

/// Remap TypeIds in a function to use the merged type arena indices.
///
/// When merging modules, each module's type arena is appended to the combined arena.
/// TypeIds need to be adjusted to point to the correct indices in the merged arena.
fn remap_function_types(
    func: &mut Function,
    module_path: &[String],
    type_map: &HashMap<(Vec<String>, u32), rv_hir::TypeId>,
    type_offset: usize,
) {
    // Remap return type
    if let Some(ret_ty) = func.return_type {
        func.return_type = Some(remap_type_id(ret_ty, module_path, type_map, type_offset));
    }

    // Remap parameter types
    for param in &mut func.parameters {
        param.ty = remap_type_id(param.ty, module_path, type_map, type_offset);
    }

    // Note: Body expression types are inferred during type checking, not stored in HIR
}

/// Remap TypeIds in a struct definition
fn remap_struct_types(
    struct_def: &mut StructDef,
    module_path: &[String],
    type_map: &HashMap<(Vec<String>, u32), rv_hir::TypeId>,
    type_offset: usize,
) {
    for field in &mut struct_def.fields {
        field.ty = remap_type_id(field.ty, module_path, type_map, type_offset);
    }
}

/// Remap TypeIds in an enum definition
fn remap_enum_types(
    enum_def: &mut EnumDef,
    module_path: &[String],
    type_map: &HashMap<(Vec<String>, u32), rv_hir::TypeId>,
    type_offset: usize,
) {
    for variant in &mut enum_def.variants {
        match &mut variant.fields {
            rv_hir::VariantFields::Unit => {}
            rv_hir::VariantFields::Tuple(types) => {
                for ty in types.iter_mut() {
                    *ty = remap_type_id(*ty, module_path, type_map, type_offset);
                }
            }
            rv_hir::VariantFields::Struct(fields) => {
                for field in fields.iter_mut() {
                    field.ty = remap_type_id(field.ty, module_path, type_map, type_offset);
                }
            }
        }
    }
}

/// Remap TypeIds in an impl block
fn remap_impl_types(
    impl_block: &mut ImplBlock,
    module_path: &[String],
    type_map: &HashMap<(Vec<String>, u32), rv_hir::TypeId>,
    type_offset: usize,
) {
    impl_block.self_ty = remap_type_id(impl_block.self_ty, module_path, type_map, type_offset);
}

/// Remap a single TypeId
fn remap_type_id(
    type_id: rv_hir::TypeId,
    module_path: &[String],
    type_map: &HashMap<(Vec<String>, u32), rv_hir::TypeId>,
    type_offset: usize,
) -> rv_hir::TypeId {
    // Try to find the exact mapping
    let key = (module_path.to_vec(), type_id.into_raw().into_u32());
    if let Some(&new_id) = type_map.get(&key) {
        return new_id;
    }

    // Fallback: apply simple offset-based remapping
    let raw = type_id.into_raw().into_u32() as usize;
    let new_raw = raw + type_offset;
    rv_hir::TypeId::from_raw(la_arena::RawIdx::from_u32(new_raw as u32))
}


/// Compile a project and lower all functions to MIR.
///
/// This is a convenience function that combines `compile_project` with MIR lowering.
pub fn compile_project_to_mir(
    root_path: impl AsRef<Path>,
) -> Result<(ProjectCompilation, HashMap<FunctionId, MirFunction>), ProjectCompilationError> {
    let project = compile_project(root_path)?;

    let mut mir_functions = HashMap::new();

    // Collect all const/static values across modules
    let all_const_values = HashMap::new();
    let all_static_values = HashMap::new();

    // Merge all module data for cross-module compilation
    let mut all_functions: HashMap<FunctionId, Function> = HashMap::new();
    let mut all_structs: HashMap<TypeDefId, StructDef> = HashMap::new();
    let mut all_enums: HashMap<TypeDefId, EnumDef> = HashMap::new();
    let mut all_traits: HashMap<TraitId, TraitDef> = HashMap::new();
    let mut all_impl_blocks: HashMap<ImplId, ImplBlock> = HashMap::new();
    let mut all_types: la_arena::Arena<Type> = la_arena::Arena::new();
    let merged_lang_items = LangItemRegistry::default();

    // Track type ID remapping for each module
    // Maps (module_path, old_type_id_raw) -> new_type_id
    let mut type_id_remap: HashMap<(Vec<String>, u32), rv_hir::TypeId> = HashMap::new();

    // Process modules in a deterministic order (root first)
    let mut ordered_modules: Vec<_> = project.modules.iter().collect();
    ordered_modules.sort_by_key(|(path, _)| path.len()); // Root first (empty path)

    for (module_path, module) in &ordered_modules {
        // Record the offset before adding this module's types
        let type_offset = all_types.len();

        // Merge types from this module into the combined arena
        for (old_type_id, ty) in module.types.iter() {
            let new_type_id = all_types.alloc(ty.clone());
            // Store the mapping using raw index
            type_id_remap.insert(((*module_path).clone(), old_type_id.into_raw().into_u32()), new_type_id);
        }

        // Merge functions with remapped TypeIds
        for (id, f) in &module.functions {
            let mut remapped = f.clone();
            remap_function_types(&mut remapped, module_path, &type_id_remap, type_offset);
            all_functions.insert(*id, remapped);
        }

        // Merge structs with remapped TypeIds
        for (id, s) in &module.structs {
            let mut remapped = s.clone();
            remap_struct_types(&mut remapped, module_path, &type_id_remap, type_offset);
            all_structs.insert(*id, remapped);
        }

        // Merge enums (enum variants may have associated types)
        for (id, e) in &module.enums {
            let mut remapped = e.clone();
            remap_enum_types(&mut remapped, module_path, &type_id_remap, type_offset);
            all_enums.insert(*id, remapped);
        }

        for (id, t) in &module.traits {
            all_traits.insert(*id, t.clone());
        }

        // Merge impl blocks with remapped TypeIds
        for (id, i) in &module.impl_blocks {
            let mut remapped = i.clone();
            remap_impl_types(&mut remapped, module_path, &type_id_remap, type_offset);
            all_impl_blocks.insert(*id, remapped);
        }
    }

    // Compile each non-generic function
    for (func_id, function) in &all_functions {
        if !function.generics.is_empty() {
            continue;
        }

        // Type inference with merged context
        let mut ty_ctx = rv_ty::TypeInference::with_hir_context(
            &all_impl_blocks,
            &all_functions,
            &all_types,
            &all_structs,
            &all_enums,
            &project.interner,
        );
        ty_ctx.infer_function(function);
        let mut ty_result = ty_ctx.finish();

        // Lower to MIR
        let mir_result = rv_mir_lower::LoweringContext::lower_function(
            function,
            &mut ty_result.ctx,
            &all_structs,
            &all_enums,
            &all_impl_blocks,
            &all_functions,
            &all_types,
            &all_traits,
            &project.interner,
            &merged_lang_items,
            &all_const_values,
            &all_static_values,
        );

        mir_functions.insert(*func_id, mir_result.function);
    }

    Ok((project, mir_functions))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    fn create_test_project(files: &[(&str, &str)]) -> TempDir {
        let dir = TempDir::new().unwrap();
        let src_dir = dir.path().join("src");
        fs::create_dir_all(&src_dir).unwrap();

        for (path, content) in files {
            let full_path = src_dir.join(path);
            if let Some(parent) = full_path.parent() {
                fs::create_dir_all(parent).unwrap();
            }
            fs::write(&full_path, content).unwrap();
        }

        dir
    }

    #[test]
    fn test_single_file_project() {
        let dir = create_test_project(&[(
            "main.rs",
            r#"
            fn main() -> i64 {
                42
            }
            "#,
        )]);

        let result = compile_project(dir.path().join("src/main.rs"));
        assert!(result.is_ok(), "Compilation should succeed");

        let project = result.unwrap();
        assert_eq!(project.modules.len(), 1);
        assert!(project.root_module().is_some());
    }

    #[test]
    fn test_two_file_project() {
        let dir = create_test_project(&[
            (
                "main.rs",
                r#"
                mod utils;

                fn main() -> i64 {
                    utils::get_value()
                }
                "#,
            ),
            (
                "utils.rs",
                r#"
                pub fn get_value() -> i64 {
                    42
                }
                "#,
            ),
        ]);

        let result = compile_project(dir.path().join("src/main.rs"));
        assert!(result.is_ok(), "Compilation should succeed: {:?}", result.err());

        let project = result.unwrap();
        assert_eq!(project.modules.len(), 2);

        // Check root module exists
        assert!(project.root_module().is_some());

        // Check utils module exists
        assert!(project.modules.contains_key(&vec!["utils".to_string()]));

        // Check we can find the function
        let utils_module = project.modules.get(&vec!["utils".to_string()]).unwrap();
        assert!(!utils_module.functions.is_empty());
    }

    #[test]
    fn test_nested_modules() {
        let dir = create_test_project(&[
            (
                "main.rs",
                r#"
                mod math;

                fn main() -> i64 {
                    math::arithmetic::add(1, 2)
                }
                "#,
            ),
            (
                "math/mod.rs",
                r#"
                pub mod arithmetic;
                "#,
            ),
            (
                "math/arithmetic.rs",
                r#"
                pub fn add(a: i64, b: i64) -> i64 {
                    a + b
                }
                "#,
            ),
        ]);

        let result = compile_project(dir.path().join("src/main.rs"));
        assert!(result.is_ok(), "Compilation should succeed: {:?}", result.err());

        let project = result.unwrap();
        assert_eq!(project.modules.len(), 3);

        // Check nested module exists
        assert!(project.modules.contains_key(&vec!["math".to_string(), "arithmetic".to_string()]));
    }
}
