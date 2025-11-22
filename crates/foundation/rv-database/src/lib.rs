//! Salsa database setup for incremental compilation
//!
//! This crate provides the core database infrastructure for the Raven compiler.
//! It uses Salsa for incremental computation and memoization.

use anyhow::Result;
use rv_hir::{FunctionId, ImplId, TraitId, TypeDefId};
use rv_intern::Interner;
use rv_vfs::VirtualFileSystem;
use salsa::Setter;
use std::path::PathBuf;
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
            types: ctx.types,
            interner: ctx.interner,
        })
    } else {
        // Return empty HIR if parsing failed
        Arc::new(HirFileData {
            functions: std::collections::HashMap::new(),
            structs: std::collections::HashMap::new(),
            enums: std::collections::HashMap::new(),
            traits: std::collections::HashMap::new(),
            impl_blocks: std::collections::HashMap::new(),
            types: la_arena::Arena::new(),
            interner: rv_intern::Interner::new(),
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
    if let Some(func) = hir.functions.get(&function) {
        Arc::new(func.clone())
    } else {
        // Return a dummy function if not found
        Arc::new(rv_hir::Function {
            id: function,
            name: rv_intern::Interner::new().intern("__missing__"),
            span: rv_span::FileSpan::new(rv_span::FileId(0), rv_span::Span::new(0, 0)),
            generics: vec![],
            parameters: vec![],
            return_type: None,
            body: rv_hir::Body::new(),
            is_external: false,
        })
    }
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
        &hir_data.traits,
        &hir_data.interner,
    );

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

/// Resolve a method call on a given type
#[salsa::tracked]
pub fn resolve_method(
    db: &dyn RavenDb,
    file: SourceFile,
    receiver_type: TypeDefId,
    method_name: rv_intern::Symbol,
) -> Option<FunctionId> {
    let hir_data = lower_to_hir(db, file);

    // Search impl blocks for this type
    for (_impl_id, impl_block) in &hir_data.impl_blocks {
        // Check if this impl block is for the receiver type
        let impl_self_ty = &hir_data.types[impl_block.self_ty];

        if let rv_hir::Type::Named { def: Some(def_id), .. } = impl_self_ty {
            if *def_id == receiver_type {
                // Search methods in this impl block
                for method_id in &impl_block.methods {
                    if let Some(method_func) = hir_data.functions.get(method_id) {
                        if method_func.name == method_name {
                            return Some(*method_id);
                        }
                    }
                }
            }
        }
    }

    None
}

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

    // Lower to MIR
    let mir = rv_mir_lower::LoweringContext::lower_function(
        &func_hir,
        &mut ty_ctx,
        &hir_data.structs,
        &hir_data.enums,
        &hir_data.impl_blocks,
        &hir_data.functions,
        &hir_data.types,
        &hir_data.traits,
        &hir_data.interner,
    );

    Arc::new(mir)
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
    /// HIR types arena
    pub types: la_arena::Arena<rv_hir::Type>,
    /// String interner
    pub interner: rv_intern::Interner,
}

/// Type inference result
#[derive(Debug, Clone, PartialEq)]
pub struct InferenceResult {
    /// Type context with inferred types
    pub context: rv_ty::TyContext,
    /// Any type errors encountered
    pub errors: Vec<rv_ty::TypeError>,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_incremental_file_contents() {
        let mut database = RootDatabase::new();

        // Create source file with initial contents
        let source_file = SourceFile::new(&mut database, PathBuf::from("test.rs"), "fn main() {}".to_string());
        let contents1 = database.get_file_contents(source_file);
        assert_eq!(contents1, "fn main() {}");

        // Update contents - this should invalidate dependent queries
        database.set_file_contents(source_file, "fn test() {}".to_string());
        let contents2 = database.get_file_contents(source_file);
        assert_eq!(contents2.as_str(), "fn test() {}");
    }
}
