//! Compiler helper for analyzer CLI

use anyhow::{Context, Result};
use lang_raven::RavenLanguage;
use rv_hir_lower::LoweringContext;
use rv_syntax::Language;
use std::path::Path;

/// Compile a source file to HIR
pub fn compile_to_hir(path: &Path) -> Result<LoweringContext> {
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

    Ok(hir_ctx)
}
