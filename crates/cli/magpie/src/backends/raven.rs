//! Raven interpreter backend

use crate::backend::{Backend, BuildResult, TestResult};
use crate::manifest::Manifest;
use anyhow::{bail, Context, Result};
use rv_database::{RootDatabase, SourceFile};
use rv_interpreter::Interpreter;
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
        self.db.register_file(path)
    }

    /// Execute a function from a compiled file using database queries
    fn execute_function(&mut self, source_file: SourceFile, function_name: &str) -> Result<String> {
        // Parse and lower to HIR via queries (automatically cached)
        let hir_data = rv_database::lower_to_hir(&self.db, source_file);

        // Find the requested function
        let function_id = hir_data
            .functions
            .iter()
            .find(|(_id, func)| hir_data.interner.resolve(&func.name) == function_name)
            .map(|(id, _func)| *id)
            .with_context(|| format!("Function '{}' not found", function_name))?;

        // Get MIR via query (automatically runs type inference and lowering)
        let mir_function = rv_database::lower_function_to_mir(&self.db, source_file, function_id);

        // Get type inference result for interpreter context
        let inference = rv_database::infer_function_types(&self.db, source_file, function_id);

        // Execute with interpreter (with HIR context for generic function calls)
        let mut interpreter = Interpreter::new_with_context(&hir_data, &inference.context);

        if function_name.contains("match") {
            eprintln!("\n>>> Executing {}", function_name);
        }

        let result = interpreter.execute(&mir_function);

        if function_name.contains("match") {
            eprintln!("<<< Result: {:?}\n", result);
        }

        let result = result?;

        Ok(format!("{result}"))
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

            // Get HIR via query to find test functions
            let hir_data = rv_database::lower_to_hir(&backend.db, source_file);

            // Find all test functions (functions starting with "test_")
            for (_func_id, function) in &hir_data.functions {
                let func_name = hir_data.interner.resolve(&function.name);

                if func_name.starts_with("test_") {
                    messages.push(format!("Running test: {func_name}"));

                    match backend.execute_function(source_file, &func_name) {
                        Ok(result) if result == "true" => {
                            passed += 1;
                            messages.push(format!("  ✓ {func_name}"));
                        }
                        Ok(result) => {
                            failed += 1;
                            messages.push(format!("  ✗ {func_name} - returned {result} instead of true"));
                        }
                        Err(error) => {
                            failed += 1;
                            messages.push(format!("  ✗ {func_name} - {error}"));
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

        // Parse via query and check for errors
        let mut backend = Self::new();
        let source_file = backend.load_file(&main_path)?;
        let parse_result = rv_database::parse_file(&backend.db, source_file);

        if parse_result.syntax.is_none() || !parse_result.errors.is_empty() {
            bail!("Parse errors found");
        }

        Ok(())
    }

    fn clean(&self, _project_dir: &Path) -> Result<()> {
        // Interpreter backend doesn't produce artifacts to clean
        Ok(())
    }
}
