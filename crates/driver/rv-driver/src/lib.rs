//! Compilation driver and high-level APIs
//!
//! This crate provides the high-level driver logic for the Raven compiler.
//! It orchestrates the compilation pipeline using the incremental queries from rv-database.

use anyhow::Result;
use rv_hir::{FunctionId, ImplBlock, ImplId, StructDef, TraitDef, TraitId, TypeDefId};
use rv_intern::Interner;
use rv_mir::MirFunction;
use std::collections::HashMap;
use std::path::Path;

/// High-level compilation context containing all HIR data
pub struct CompilationContext {
    /// Function definitions
    pub functions: HashMap<FunctionId, rv_hir::Function>,
    /// Struct definitions
    pub structs: HashMap<TypeDefId, StructDef>,
    /// Enum definitions
    pub enums: HashMap<TypeDefId, rv_hir::EnumDef>,
    /// Trait definitions
    pub traits: HashMap<TraitId, TraitDef>,
    /// Implementation blocks (both inherent and trait impls)
    pub impl_blocks: HashMap<ImplId, ImplBlock>,
    /// Type arena
    pub types: la_arena::Arena<rv_hir::Type>,
    /// String interner
    pub interner: Interner,
}

/// Compile a single file to MIR
pub fn compile_file_to_mir(path: impl AsRef<Path>) -> Result<HashMap<FunctionId, MirFunction>> {
    let source = std::fs::read_to_string(path)?;

    // Parse source
    let parse_result = rv_parser::parse_source(&source);
    let syntax = parse_result.syntax.ok_or_else(|| anyhow::anyhow!("Parse failed"))?;

    // Lower to HIR
    let hir_ctx = rv_hir_lower::lower_source_file(&syntax);

    // Run type inference and lower to MIR for each function
    let mut mir_functions = HashMap::new();

    for (func_id, function) in &hir_ctx.functions {
        // Skip generic functions (need monomorphization)
        if !function.generics.is_empty() {
            continue;
        }

        // Type inference
        let mut ty_ctx = rv_ty::TypeInference::with_hir_context(
            &hir_ctx.impl_blocks,
            &hir_ctx.functions,
            &hir_ctx.types,
            &hir_ctx.structs,
            &hir_ctx.enums,
            &hir_ctx.traits,
            &hir_ctx.interner,
        );
        ty_ctx.infer_function(function);
        let mut ty_result = ty_ctx.finish();

        // Lower to MIR
        let mir = rv_mir_lower::LoweringContext::lower_function(
            function,
            &mut ty_result.ctx,
            &hir_ctx.structs,
            &hir_ctx.enums,
            &hir_ctx.impl_blocks,
            &hir_ctx.functions,
            &hir_ctx.types,
            &hir_ctx.traits,
            &hir_ctx.interner,
        );

        mir_functions.insert(*func_id, mir);
    }

    Ok(mir_functions)
}

/// Compile a single file and extract HIR context
pub fn compile_file_to_hir(path: impl AsRef<Path>) -> Result<CompilationContext> {
    let source = std::fs::read_to_string(path)?;

    // Parse source
    let parse_result = rv_parser::parse_source(&source);
    let syntax = parse_result.syntax.ok_or_else(|| anyhow::anyhow!("Parse failed"))?;

    // Lower to HIR
    let hir_ctx = rv_hir_lower::lower_source_file(&syntax);

    Ok(CompilationContext {
        functions: hir_ctx.functions,
        structs: hir_ctx.structs,
        enums: hir_ctx.enums,
        traits: hir_ctx.traits,
        impl_blocks: hir_ctx.impl_blocks,
        types: hir_ctx.types,
        interner: hir_ctx.interner,
    })
}
