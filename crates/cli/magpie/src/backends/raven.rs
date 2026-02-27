//! Raven interpreter backend

use crate::backend::{Backend, BuildResult, TestResult};
use crate::manifest::Manifest;
use anyhow::{Context, Result, bail};
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
        crate::run_borrow_check(&mir_function, function_name);

        // Get type inference result for interpreter context
        let inference = rv_database::infer_function_types(&self.db, source_file, function_id);

        // Create a temporary LoweringContext for the interpreter
        // The interpreter needs access to functions for generic calls
        use rv_hir_lower::LoweringContext;
        let mut hir_ctx = LoweringContext::new();
        hir_ctx.functions = hir_data.functions.clone();
        hir_ctx.structs = hir_data.structs.clone();
        hir_ctx.enums = hir_data.enums.clone();
        hir_ctx.traits = hir_data.traits.clone();
        hir_ctx.impl_blocks = hir_data.impl_blocks.clone();
        hir_ctx.types = hir_data.types.clone();
        hir_ctx.interner = hir_data.interner.clone();

        // Execute with interpreter (with HIR context for generic function calls)
        let mut interpreter = Interpreter::new_with_context(&hir_ctx, &inference.context);

        let result = interpreter.execute(&mir_function);

        let result = result?;

        Ok(format!("{result}"))
    }

    /// Execute a function from a multi-file project using project-level compilation.
    ///
    /// Discovers all module files starting from `main_path`, lowers each to HIR,
    /// builds a cross-module function map, and executes the requested function.
    fn execute_project_function(
        &mut self,
        main_path: &Path,
        function_name: &str,
    ) -> Result<String> {
        let project = rv_database::lower_project(main_path)?;

        // Find the function in the root module
        let root_hir = project
            .root_hir()
            .context("No root module found in project")?;

        let function_id = root_hir
            .functions
            .iter()
            .find(|(_id, func)| root_hir.interner.resolve(&func.name) == function_name)
            .map(|(id, _)| *id)
            .with_context(|| format!("Function '{}' not found in root module", function_name))?;

        // Build cross-module function map for MIR lowering
        let mut cross_module_functions =
            std::collections::HashMap::<(Vec<String>, String), rv_hir::FunctionId>::new();

        for (mod_path, module_data) in &project.modules {
            if mod_path.is_empty() {
                continue; // Skip root module — its functions are resolved locally
            }
            for (func_id, func) in &module_data.hir.functions {
                let func_name = module_data.hir.interner.resolve(&func.name);
                cross_module_functions.insert((mod_path.clone(), func_name), *func_id);
            }
        }

        // Run type inference on the root module
        let mut type_inference = rv_ty::TypeInference::with_hir_context(
            &root_hir.impl_blocks,
            &root_hir.functions,
            &root_hir.types,
            &root_hir.structs,
            &root_hir.enums,
            &root_hir.interner,
        );
        type_inference.set_const_static_items(&root_hir.const_items, &root_hir.static_items);

        // Evaluate const and static items for MIR lowering
        let const_values =
            rv_const_eval::evaluate_const_items(&root_hir.const_items, &root_hir.interner);
        let static_values = rv_const_eval::evaluate_static_items(
            &root_hir.static_items,
            &root_hir.const_items,
            &const_values,
            &root_hir.interner,
        );

        // Infer and lower each non-generic root function to MIR.
        // Inference and lowering must be interleaved because ExprIds are local
        // to each function body and would collide in the shared TyContext.
        let mut all_mir_functions = std::collections::HashMap::new();
        for (func_id, func) in root_hir
            .functions
            .iter()
            .filter(|(_, func)| func.generics.is_empty())
            .filter(|(func_id, _)| !root_hir.default_method_bodies.contains(func_id))
        {
            type_inference.context_mut().clear_expr_types();
            type_inference.infer_function(func);
            let mir_result = rv_mir_lower::LoweringContext::lower_function_cross_module(
                func,
                type_inference.context_mut(),
                &root_hir.structs,
                &root_hir.enums,
                &root_hir.impl_blocks,
                &root_hir.functions,
                &root_hir.types,
                &root_hir.traits,
                &root_hir.interner,
                &cross_module_functions,
                &root_hir.lang_items,
                &const_values,
                &static_values,
            );
            crate::print_mir_diagnostics(&mir_result.diagnostics);
            let func_name_str = root_hir.interner.resolve(&func.name);
            crate::run_borrow_check(&mir_result.function, &func_name_str);
            all_mir_functions.insert(*func_id, mir_result.function);
        }

        for (mod_path, module_data) in &project.modules {
            if mod_path.is_empty() {
                continue;
            }

            let mod_hir = &module_data.hir;
            let mut mod_type_inference = rv_ty::TypeInference::with_hir_context(
                &mod_hir.impl_blocks,
                &mod_hir.functions,
                &mod_hir.types,
                &mod_hir.structs,
                &mod_hir.enums,
                &mod_hir.interner,
            );
            mod_type_inference.set_const_static_items(&mod_hir.const_items, &mod_hir.static_items);

            // Evaluate const and static items for this module
            let mod_const_values =
                rv_const_eval::evaluate_const_items(&mod_hir.const_items, &mod_hir.interner);
            let mod_static_values = rv_const_eval::evaluate_static_items(
                &mod_hir.static_items,
                &mod_hir.const_items,
                &mod_const_values,
                &mod_hir.interner,
            );

            // Infer and lower each non-generic module function to MIR.
            // Inference and lowering must be interleaved because ExprIds are local
            // to each function body and would collide in the shared TyContext.
            for (func_id, func) in mod_hir
                .functions
                .iter()
                .filter(|(_, func)| func.generics.is_empty())
                .filter(|(func_id, _)| !mod_hir.default_method_bodies.contains(func_id))
            {
                mod_type_inference.context_mut().clear_expr_types();
                mod_type_inference.infer_function(func);
                let mir_result = rv_mir_lower::LoweringContext::lower_function(
                    func,
                    mod_type_inference.context_mut(),
                    &mod_hir.structs,
                    &mod_hir.enums,
                    &mod_hir.impl_blocks,
                    &mod_hir.functions,
                    &mod_hir.types,
                    &mod_hir.traits,
                    &mod_hir.interner,
                    &mod_hir.lang_items,
                    &mod_const_values,
                    &mod_static_values,
                );
                crate::print_mir_diagnostics(&mir_result.diagnostics);
                let func_name = mod_hir.interner.resolve(&func.name);
                crate::run_borrow_check(&mir_result.function, &func_name);
                all_mir_functions.insert(*func_id, mir_result.function);
            }
        }

        // Create interpreter with root HIR context
        use rv_hir_lower::LoweringContext;
        let mut hir_ctx = LoweringContext::new();
        hir_ctx.functions = root_hir.functions.clone();
        hir_ctx.structs = root_hir.structs.clone();
        hir_ctx.enums = root_hir.enums.clone();
        hir_ctx.traits = root_hir.traits.clone();
        hir_ctx.impl_blocks = root_hir.impl_blocks.clone();
        hir_ctx.types = root_hir.types.clone();
        hir_ctx.interner = root_hir.interner.clone();

        let ty_result = type_inference.finish();
        let mut interpreter = Interpreter::new_with_context(&hir_ctx, &ty_result.ctx);

        // Register cross-module MIR functions in the interpreter
        for (func_id, mir_func) in &all_mir_functions {
            if *func_id != function_id {
                interpreter.register_mir_function(*func_id, mir_func.clone());
            }
        }

        let result = interpreter.execute(&all_mir_functions[&function_id])?;
        Ok(format!("{result}"))
    }

    /// Check if a project has multiple files (mod declarations referencing other files).
    fn is_multi_file_project(main_path: &Path) -> Result<bool> {
        let files = rv_database::discover_module_files(main_path)?;
        Ok(files.len() > 1)
    }

    /// Compile and run a single source file (for compiletest)
    pub fn compile_and_run(&self, file: &Path, _args: &[String]) -> Result<()> {
        let mut backend = Self::new();
        let source_file = backend.load_file(file)?;

        // Execute the main function
        let result = backend.execute_function(source_file, "main")?;

        // Print the result if it's not unit
        if result != "()" {
            println!("{result}");
        }

        Ok(())
    }
}

impl Default for RavenBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for RavenBackend {
    fn build(&self, manifest: &Manifest, project_dir: &Path) -> Result<BuildResult> {
        let mut messages = vec![format!(
            "Building {} v{}",
            manifest.package.name, manifest.package.version
        )];

        // For now, just validate that the main file exists
        if let Some(bin) = manifest.main_bin() {
            let main_path = project_dir.join(&bin.path);
            if !main_path.exists() {
                messages.push(format!(
                    "Error: Main file not found: {}",
                    main_path.display()
                ));
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

        let mut backend = Self::new();

        let result = if Self::is_multi_file_project(&main_path)? {
            backend.execute_project_function(&main_path, "main")?
        } else {
            let source_file = backend.load_file(&main_path)?;
            backend.execute_function(source_file, "main")?
        };

        // Print the result if it's not unit
        if result != "()" {
            eprintln!("{result}");
        }

        Ok(())
    }

    fn test(&self, manifest: &Manifest, project_dir: &Path) -> Result<TestResult> {
        let mut messages = vec![format!(
            "Testing {} v{}",
            manifest.package.name, manifest.package.version
        )];
        let mut passed = 0;
        let mut failed = 0;

        if let Some(bin) = manifest.main_bin() {
            let main_path = project_dir.join(&bin.path);

            let is_multi = Self::is_multi_file_project(&main_path)?;
            if is_multi {
                // Multi-file project: use project-level compilation
                let project = rv_database::lower_project(&main_path)?;
                let root_hir = project
                    .root_hir()
                    .context("No root module found in project")?;

                // Find all test functions in the root module
                let test_functions: Vec<String> = root_hir
                    .functions
                    .iter()
                    .filter_map(|(_, func)| {
                        let name = root_hir.interner.resolve(&func.name);
                        if name.starts_with("test_") {
                            Some(name)
                        } else {
                            None
                        }
                    })
                    .collect();

                for func_name in &test_functions {
                    messages.push(format!("Running test: {func_name}"));

                    let mut backend = Self::new();
                    match backend.execute_project_function(&main_path, func_name) {
                        Ok(result) if result == "true" => {
                            passed += 1;
                            messages.push(format!("  \u{2713} {func_name}"));
                        }
                        Ok(result) => {
                            failed += 1;
                            messages.push(format!(
                                "  \u{2717} {func_name} - returned {result} instead of true"
                            ));
                        }
                        Err(error) => {
                            failed += 1;
                            messages.push(format!("  \u{2717} {func_name} - {error}"));
                        }
                    }
                }
            } else {
                // Single-file project: use database queries
                let mut backend = Self::new();
                let source_file = backend.load_file(&main_path)?;

                let hir_data = rv_database::lower_to_hir(&backend.db, source_file);

                for (_func_id, function) in &hir_data.functions {
                    let func_name = hir_data.interner.resolve(&function.name);

                    if func_name.starts_with("test_") {
                        messages.push(format!("Running test: {func_name}"));

                        match backend.execute_function(source_file, &func_name) {
                            Ok(result) if result == "true" => {
                                passed += 1;
                                messages.push(format!("  \u{2713} {func_name}"));
                            }
                            Ok(result) => {
                                failed += 1;
                                messages.push(format!(
                                    "  \u{2717} {func_name} - returned {result} instead of true"
                                ));
                            }
                            Err(error) => {
                                failed += 1;
                                messages.push(format!("  \u{2717} {func_name} - {error}"));
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
