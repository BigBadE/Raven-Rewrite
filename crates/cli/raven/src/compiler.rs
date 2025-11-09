//! Compiler pipeline integration

use anyhow::{Context, Result};
use lang_raven::RavenLanguage;
use rv_hir::Function;
use rv_hir_lower::LoweringContext;
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
    let source = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read file {:?}", path))?;

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
