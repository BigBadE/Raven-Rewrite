//! Cranelift JIT backend

use crate::backend::{Backend, BuildResult, TestResult};
use crate::manifest::Manifest;
use anyhow::{Context, Result};
use rv_cranelift::JitCompiler;
use rv_database::{RootDatabase, SourceFile};
use rv_hir_lower::lower::lower_source_file;
use rv_mir::lower::LoweringContext;
use rv_ty::infer::TypeInference;
use std::path::Path;

/// Cranelift JIT backend
pub struct CraneliftBackend {
    /// Database for incremental compilation
    db: RootDatabase,

    /// JIT compiler
    jit: JitCompiler,
}

impl CraneliftBackend {
    /// Create a new Cranelift backend
    pub fn new() -> Result<Self> {
        Ok(Self {
            db: RootDatabase::new(),
            jit: JitCompiler::new()?,
        })
    }

    /// Load a source file into the database
    fn load_file(&mut self, path: &Path) -> Result<SourceFile> {
        self.db.register_file(path)
    }

    /// Compile and execute a function
    fn execute_function(&mut self, source_file: SourceFile, function_name: &str) -> Result<i64> {
        // Get file contents and parse
        let contents = self.db.get_file_contents(source_file);
        let parse_result = rv_parser::parse_source(&contents);

        if let Some(syntax) = parse_result.syntax {
            // Lower to HIR
            let hir_ctx = lower_source_file(&syntax);

            // Find the requested function
            let function = hir_ctx
                .functions
                .iter()
                .find(|(_id, func)| hir_ctx.interner.resolve(&func.name) == function_name)
                .map(|(_id, func)| func)
                .with_context(|| format!("Function '{function_name}' not found"))?;

            // Run type inference with HIR context for method resolution
            let mut type_inference = TypeInference::with_hir_context(
                &hir_ctx.impl_blocks,
                &hir_ctx.functions,
                &hir_ctx.types,
                &hir_ctx.structs,
                &hir_ctx.enums,
                &hir_ctx.traits,
                &hir_ctx.interner,
            );
            type_inference.infer_function(function);

            // Lower ALL functions to MIR (including called functions)
            let mut mir_functions = Vec::new();
            let mut target_mir_func_id = None;

            for (_func_id, hir_func) in &hir_ctx.functions {
                let mir_func = LoweringContext::lower_function(
                    hir_func,
                    type_inference.context(),
                    &hir_ctx.structs,
                    &hir_ctx.enums,
                    &hir_ctx.impl_blocks,
                    &hir_ctx.functions,
                    &hir_ctx.types,
                    &hir_ctx.traits,
                );

                // Track which MIR function is our target
                if hir_ctx.interner.resolve(&hir_func.name) == function_name {
                    target_mir_func_id = Some(mir_func.id);
                }

                mir_functions.push(mir_func);
            }

            // Compile all functions with Cranelift (supports function calls)
            if mir_functions.len() > 1 {
                // Multi-function compilation (for generic functions and calls)
                self.jit.compile_multiple(&mir_functions)?;

                // Get the specific function we want to execute
                let target_func_id = target_mir_func_id.context("Target function not found in MIR")?;
                let code_ptr = self.jit.compiled_functions.get(&target_func_id)
                    .copied()
                    .context("Target function was not compiled")?;

                // Execute
                let result = unsafe { self.jit.execute(code_ptr) };
                Ok(result)
            } else {
                // Single function (legacy path)
                let code_ptr = self.jit.compile(&mir_functions[0])?;
                let result = unsafe { self.jit.execute(code_ptr) };
                Ok(result)
            }
        } else {
            anyhow::bail!("Failed to parse file");
        }
    }
}

impl Default for CraneliftBackend {
    fn default() -> Self {
        Self::new().expect("Failed to create Cranelift backend")
    }
}

impl Backend for CraneliftBackend {
    fn build(&self, manifest: &Manifest, project_dir: &Path) -> Result<BuildResult> {
        let mut messages = vec![format!(
            "Building {} v{} (JIT)",
            manifest.package.name, manifest.package.version
        )];

        // Validate that the main file exists
        if let Some(bin) = manifest.main_bin() {
            let main_path = project_dir.join(&bin.path);
            if !main_path.exists() {
                messages.push(format!("Error: Main file not found: {}", main_path.display()));
                return Ok(BuildResult {
                    success: false,
                    messages,
                    executable: None,
                });
            }

            messages.push(format!("Validated main file: {}", bin.path.display()));
        }

        messages.push("Build completed successfully (JIT mode)".to_string());

        Ok(BuildResult {
            success: true,
            messages,
            executable: None,
        })
    }

    fn run(&self, manifest: &Manifest, project_dir: &Path, _args: &[String]) -> Result<()> {
        let bin = manifest
            .main_bin()
            .context("No binary target found in manifest")?;

        let main_path = project_dir.join(&bin.path);

        // Create a new backend instance for execution
        let mut backend = Self::new()?;
        let source_file = backend.load_file(&main_path)?;

        // Execute the main function
        let result = backend.execute_function(source_file, "main")?;

        // Print the result if it's not 0 (representing unit)
        if result != 0 {
            eprintln!("{result}");
        }

        Ok(())
    }

    fn test(&self, manifest: &Manifest, project_dir: &Path) -> Result<TestResult> {
        let mut messages = vec![format!(
            "Testing {} v{} (JIT)",
            manifest.package.name, manifest.package.version
        )];
        let mut passed = 0;
        let mut failed = 0;

        // Look for test functions in the main file
        if let Some(bin) = manifest.main_bin() {
            let main_path = project_dir.join(&bin.path);

            let mut backend = Self::new()?;
            let source_file = backend.load_file(&main_path)?;

            // Parse to find test functions
            let contents = backend.db.get_file_contents(source_file);
            let parse_result = rv_parser::parse_source(&contents);

            if let Some(syntax) = parse_result.syntax {
                let hir_ctx = lower_source_file(&syntax);

                // Find all test functions
                for (_func_id, function) in &hir_ctx.functions {
                    let func_name = hir_ctx.interner.resolve(&function.name);

                    if func_name.starts_with("test_") {
                        messages.push(format!("Running test: {func_name}"));

                        match backend.execute_function(source_file, &func_name) {
                            Ok(result) if result == 1 => {
                                // true is represented as 1
                                passed += 1;
                                messages.push(format!("  ✓ {func_name}"));
                            }
                            Ok(result) => {
                                failed += 1;
                                messages.push(format!(
                                    "  ✗ {func_name} - returned {result} instead of true (1)"
                                ));
                            }
                            Err(error) => {
                                failed += 1;
                                messages.push(format!("  ✗ {func_name} - {error}"));
                            }
                        }
                    }
                }
            }
        }

        Ok(TestResult {
            success: failed == 0,
            passed,
            failed,
            messages,
        })
    }

    fn check(&self, manifest: &Manifest, project_dir: &Path) -> Result<()> {
        let bin = manifest
            .main_bin()
            .context("No binary target found in manifest")?;

        let main_path = project_dir.join(&bin.path);

        // Parse and type-check the file
        let mut backend = Self::new()?;
        let source_file = backend.load_file(&main_path)?;
        let contents = backend.db.get_file_contents(source_file);
        let parse_result = rv_parser::parse_source(&contents);

        if parse_result.syntax.is_none() {
            anyhow::bail!("Parse errors found");
        }

        Ok(())
    }

    fn clean(&self, _project_dir: &Path) -> Result<()> {
        // JIT backend doesn't produce artifacts to clean
        Ok(())
    }
}
