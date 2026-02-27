//! Compiler pipeline integration

use anyhow::{Context, Result};
use lang_raven::RavenLanguage;
use rv_hir::{ConstId, Function, StaticId};
use rv_hir_lower::LoweringContext;
use rv_mir::MirFunction;
use std::collections::HashMap;
use std::path::Path;

/// Result of compiling a source file
pub struct CompileResult {
    /// Lowering context with HIR
    pub hir_ctx: LoweringContext,
}

/// Compile a source file through the available pipeline stages
pub fn compile_file(path: &Path) -> Result<CompileResult> {
    use rv_syntax::Language;

    // Read source file
    let source =
        std::fs::read_to_string(path).with_context(|| format!("Failed to read file {:?}", path))?;

    // Parse with tree-sitter
    let language = RavenLanguage::new();
    let tree = language.parse(&source)?;

    // Lower to SyntaxNode
    let root = language.lower_node(&tree.root_node(), &source);

    // Lower to HIR
    let hir_ctx = rv_hir_lower::lower_source_file(&root);

    Ok(CompileResult { hir_ctx })
}

/// Find the main function in HIR
pub fn find_main_function(hir_ctx: &LoweringContext) -> Option<&Function> {
    hir_ctx
        .functions
        .values()
        .find(|f| hir_ctx.interner.resolve(&f.name) == "main")
}

/// Evaluate all const items in the HIR context.
///
/// Returns a map from `ConstId` to the evaluated `ConstValue`.
pub fn evaluate_consts(hir_ctx: &LoweringContext) -> HashMap<ConstId, rv_const_eval::ConstValue> {
    rv_const_eval::evaluate_const_items(&hir_ctx.const_items, &hir_ctx.interner)
}

/// Evaluate all static item initializers in the HIR context.
///
/// Returns a map from `StaticId` to the evaluated `ConstValue`.
pub fn evaluate_statics(
    hir_ctx: &LoweringContext,
    const_values: &HashMap<ConstId, rv_const_eval::ConstValue>,
) -> HashMap<StaticId, rv_const_eval::ConstValue> {
    rv_const_eval::evaluate_static_items(
        &hir_ctx.static_items,
        &hir_ctx.const_items,
        const_values,
        &hir_ctx.interner,
    )
}

/// Run coherence checking on the HIR.
///
/// Detects overlapping/conflicting trait implementations and duplicate
/// inherent methods. Should be called after HIR lowering but before MIR
/// lowering.
///
/// # Errors
///
/// Returns an error if any coherence violations are found.
pub fn check_coherence(hir_ctx: &LoweringContext) -> Result<()> {
    if let Err(errors) = rv_ty::check_coherence(
        &hir_ctx.impl_blocks,
        &hir_ctx.traits,
        &hir_ctx.types,
        &hir_ctx.functions,
    ) {
        for error in &errors {
            eprintln!("error[coherence]: {error}");
        }
        anyhow::bail!(
            "Compilation aborted due to {} coherence error(s)",
            errors.len()
        );
    }
    Ok(())
}

/// Lower all non-generic functions to MIR with type inference.
///
/// Returns the type inference result and a Vec of MIR functions.
///
/// # Errors
///
/// Returns an error if any function fails borrow checking.
pub fn lower_to_mir(
    hir_ctx: &LoweringContext,
) -> Result<(rv_ty::InferenceResult, Vec<MirFunction>)> {
    // Evaluate const and static items
    let const_values = evaluate_consts(hir_ctx);
    let static_values = evaluate_statics(hir_ctx, &const_values);

    let mut type_inference = rv_ty::TypeInference::with_hir_context(
        &hir_ctx.impl_blocks,
        &hir_ctx.functions,
        &hir_ctx.types,
        &hir_ctx.structs,
        &hir_ctx.enums,
        &hir_ctx.interner,
    );
    type_inference.set_const_static_items(&hir_ctx.const_items, &hir_ctx.static_items);

    let mut mir_functions = Vec::new();
    let mut borrow_errors = false;

    for (_, func) in hir_ctx
        .functions
        .iter()
        .filter(|(_, func)| func.generics.is_empty())
    {
        type_inference.context_mut().clear_expr_types();
        type_inference.infer_function(func);

        let mir_result = rv_mir_lower::LoweringContext::lower_function(
            func,
            type_inference.context_mut(),
            &hir_ctx.structs,
            &hir_ctx.enums,
            &hir_ctx.impl_blocks,
            &hir_ctx.functions,
            &hir_ctx.types,
            &hir_ctx.traits,
            &hir_ctx.interner,
            &hir_ctx.lang_items,
            &const_values,
            &static_values,
        );
        for diag in &mir_result.diagnostics {
            eprintln!("warning[mir]: {}", diag.message);
        }

        if !run_borrow_check(&mir_result.function, &hir_ctx.interner.resolve(&func.name)) {
            borrow_errors = true;
        }

        mir_functions.push(mir_result.function);
    }

    if borrow_errors {
        anyhow::bail!("Compilation aborted due to borrow check errors");
    }

    let inference_result = type_inference.finish();
    Ok((inference_result, mir_functions))
}

/// Monomorphize generic functions and rewrite calls.
pub fn monomorphize(hir_ctx: &LoweringContext, mir_functions: &mut Vec<MirFunction>) {
    use rv_mono::MonoCollector;

    let mut collector = MonoCollector::new();
    for mir_func in mir_functions.iter() {
        collector.collect_from_mir(mir_func, &hir_ctx.functions, &hir_ctx.types);
    }

    let next_func_id = hir_ctx.functions.len() as u32;
    let bound_checker = rv_ty::BoundChecker::new(
        hir_ctx.traits.clone(),
        &hir_ctx.impl_blocks,
        hir_ctx.types.clone(),
        hir_ctx.structs.clone(),
        hir_ctx.enums.clone(),
    );
    let (mono_functions, instance_map) = rv_mono::monomorphize_functions(
        hir_ctx,
        collector.needed_instances(),
        next_func_id,
        Some(&bound_checker),
    );

    mir_functions.extend(mono_functions);

    rv_mono::rewrite_calls_to_instances(
        mir_functions,
        &instance_map,
        &hir_ctx.functions,
        &hir_ctx.types,
    );
}

/// Run borrow checking on a MIR function.
///
/// Returns `true` if no errors were found, `false` if borrow errors exist.
/// All errors are printed to stderr.
pub fn run_borrow_check(mir_func: &MirFunction, func_name: &str) -> bool {
    match rv_borrow_check::BorrowChecker::check(mir_func) {
        Ok(()) => true,
        Err(errors) => {
            for error in &errors {
                eprintln!("error[borrow-check]: in function '{func_name}': {error}");
            }
            false
        }
    }
}
