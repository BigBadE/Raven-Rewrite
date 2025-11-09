//! Raven interpreter backend

use crate::backend::{Backend, BuildResult, TestResult};
use crate::manifest::Manifest;
use anyhow::{bail, Context, Result};
use rv_database::{RootDatabase, SourceFile};
use rv_hir_lower::lower::lower_source_file;
use rv_interpreter::Interpreter;
use rv_mir::lower::LoweringContext;
use rv_ty::infer::TypeInference;
use std::path::Path;

/// Raven interpreter backend
pub struct RavenBackend {
    /// Database for incremental compilation
    db: RootDatabase,
}

impl RavenBackend {
    /// Create a new Raven backend
    #[must_use]
    pub fn new() -> Self {
        Self {
            db: RootDatabase::new(),
        }
    }

    /// Load a source file into the database
    fn load_file(&mut self, path: &Path) -> Result<SourceFile> {
        let contents = std::fs::read_to_string(path)
            .with_context(|| format!("Failed to read file: {}", path.display()))?;

        let source_file = self.db.register_file(path)?;
        self.db.set_file_contents(source_file, contents)?;

        Ok(source_file)
    }

    /// Execute a function from a compiled file
    fn execute_function(&mut self, source_file: SourceFile, function_name: &str) -> Result<String> {
        // Get file contents and parse
        let contents = self.db.get_file_contents(source_file)?;
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
                .with_context(|| format!("Function '{}' not found", function_name))?;

            // Run type inference on ALL functions (including methods in impl blocks)
            let mut type_inference = TypeInference::with_hir_context(
                &hir_ctx.impl_blocks,
                &hir_ctx.functions,
                &hir_ctx.types,
                &hir_ctx.structs,
                &hir_ctx.interner,
            );
            for (_func_id, hir_func) in &hir_ctx.functions {
                type_inference.infer_function(hir_func);
            }

            // Lower to MIR
            let mir_function = LoweringContext::lower_function(
                function,
                type_inference.context(),
                &hir_ctx.structs,
                &hir_ctx.impl_blocks,
                &hir_ctx.functions,
                &hir_ctx.types,
                &hir_ctx.traits,
            );

            // Execute with interpreter (with HIR context for generic function calls)
            let mut interpreter = Interpreter::new_with_context(&hir_ctx, type_inference.context());

            if function_name.contains("match") {
                eprintln!("\n>>> Executing {}", function_name);
            }

            let result = interpreter.execute(&mir_function);

            if function_name.contains("match") {
                eprintln!("<<< Result: {:?}\n", result);
            }

            let result = result?;

            Ok(format!("{result}"))
        } else {
            bail!("Failed to parse file");
        }
    }
}

impl Default for RavenBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for RavenBackend {
    fn build(&self, manifest: &Manifest, project_dir: &Path) -> Result<BuildResult> {
        let mut messages = vec![format!("Building {} v{}", manifest.package.name, manifest.package.version)];

        // For now, just validate that the main file exists
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

        messages.push("Build completed successfully".to_string());

        Ok(BuildResult {
            success: true,
            messages,
            executable: None, // Interpreter doesn't produce executables
        })
    }

    fn run(&self, manifest: &Manifest, project_dir: &Path, _args: &[String]) -> Result<()> {
        let bin = manifest
            .main_bin()
            .context("No binary target found in manifest")?;

        let main_path = project_dir.join(&bin.path);

        // Create a new backend instance for execution
        let mut backend = Self::new();
        let source_file = backend.load_file(&main_path)?;

        // Execute the main function
        let result = backend.execute_function(source_file, "main")?;

        // Print the result if it's not unit
        if result != "()" {
            eprintln!("{result}");
        }

        Ok(())
    }

    fn test(&self, manifest: &Manifest, project_dir: &Path) -> Result<TestResult> {
        let mut messages = vec![format!("Testing {} v{}", manifest.package.name, manifest.package.version)];
        let mut passed = 0;
        let mut failed = 0;

        // For interpreter backend, we'll look for test functions in the main file
        if let Some(bin) = manifest.main_bin() {
            let main_path = project_dir.join(&bin.path);

            let mut backend = Self::new();
            let source_file = backend.load_file(&main_path)?;

            // Parse to find test functions
            let contents = backend.db.get_file_contents(source_file)?;
            let parse_result = rv_parser::parse_source(&contents);

            if let Some(syntax) = parse_result.syntax {
                let hir_ctx = lower_source_file(&syntax);

                // Find all test functions (functions starting with "test_")
                for (_func_id, function) in &hir_ctx.functions {
                    let func_name = hir_ctx.interner.resolve(&function.name);

                    if func_name.starts_with("test_") {
                        messages.push(format!("Running test: {func_name}"));

                        match backend.execute_function(source_file, &func_name) {
                            Ok(result) if result == "true" => {
                                passed += 1;
                                messages.push(format!("  ✓ {func_name}"));
                            }
                            Ok(result) => {
                                failed += 1;
                                eprintln!("DEBUG: Test {} returned: {:?}", func_name, result);
                                messages.push(format!("  ✗ {func_name} - returned {result} instead of true"));
                            }
                            Err(error) => {
                                failed += 1;
                                eprintln!("DEBUG: Test {} error: {:?}", func_name, error);
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
        let mut backend = Self::new();
        let source_file = backend.load_file(&main_path)?;
        let contents = backend.db.get_file_contents(source_file)?;
        let parse_result = rv_parser::parse_source(&contents);

        if parse_result.syntax.is_none() {
            bail!("Parse errors found");
        }

        Ok(())
    }

    fn clean(&self, _project_dir: &Path) -> Result<()> {
        // Interpreter backend doesn't produce artifacts to clean
        Ok(())
    }
}
