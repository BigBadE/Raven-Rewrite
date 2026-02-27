//! Cranelift JIT backend

use crate::backend::{Backend, BuildResult, TestResult};
use crate::manifest::Manifest;
use anyhow::{Context, Result};
use rv_cranelift::JitCompiler;
use rv_database::{RootDatabase, SourceFile};
use rv_hir_lower::lower::lower_source_file;
use rv_mir_lower::LoweringContext;
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
            let _function = hir_ctx
                .functions
                .iter()
                .find(|(_id, func)| hir_ctx.interner.resolve(&func.name) == function_name)
                .map(|(_id, func)| func)
                .with_context(|| format!("Function '{function_name}' not found"))?;

            // Run coherence checking
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

            // Evaluate const and static items
            let const_values =
                rv_const_eval::evaluate_const_items(&hir_ctx.const_items, &hir_ctx.interner);
            let static_values = rv_const_eval::evaluate_static_items(
                &hir_ctx.static_items,
                &hir_ctx.const_items,
                &const_values,
                &hir_ctx.interner,
            );

            // Run type inference with HIR context for method resolution
            let mut type_inference = TypeInference::with_hir_context(
                &hir_ctx.impl_blocks,
                &hir_ctx.functions,
                &hir_ctx.types,
                &hir_ctx.structs,
                &hir_ctx.enums,
                &hir_ctx.interner,
            );
            type_inference.set_const_static_items(&hir_ctx.const_items, &hir_ctx.static_items);

            // Infer and lower each non-generic function to MIR.
            // Inference and lowering must be interleaved because ExprIds are local
            // to each function body and would collide in the shared TyContext.
            let mut mir_functions = Vec::new();
            let mut target_mir_func_id = None;

            for (_func_id, hir_func) in hir_ctx
                .functions
                .iter()
                .filter(|(_, func)| func.generics.is_empty())
                .filter(|(func_id, _)| !hir_ctx.default_method_bodies.contains(func_id))
            {
                type_inference.context_mut().clear_expr_types();
                type_inference.infer_function(hir_func);

                let mir_result = LoweringContext::lower_function(
                    hir_func,
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
                crate::print_mir_diagnostics(&mir_result.diagnostics);

                let func_name_str = hir_ctx.interner.resolve(&hir_func.name);
                crate::run_borrow_check(&mir_result.function, &func_name_str);

                // Track which MIR function is our target
                if hir_ctx.interner.resolve(&hir_func.name) == function_name {
                    target_mir_func_id = Some(mir_result.function.id);
                }

                mir_functions.push(mir_result.function);
            }

            // Monomorphization: collect generic function instantiations needed from MIR
            use rv_mono::MonoCollector;
            let mut collector = MonoCollector::new();
            for mir_func in &mir_functions {
                collector.collect_from_mir(mir_func, &hir_ctx.functions, &hir_ctx.types);
            }

            // Generate specialized versions of generic functions with proper type substitution
            let next_func_id = hir_ctx.functions.len() as u32;
            let bound_checker = rv_ty::BoundChecker::new(
                hir_ctx.traits.clone(),
                &hir_ctx.impl_blocks,
                hir_ctx.types.clone(),
                hir_ctx.structs.clone(),
                hir_ctx.enums.clone(),
            );
            let (mono_functions, instance_map) = rv_mono::monomorphize_functions(
                &hir_ctx,
                collector.needed_instances(),
                next_func_id,
                Some(&bound_checker),
            );

            // Add monomorphized functions to the compilation set
            mir_functions.extend(mono_functions);

            // Rewrite calls in existing MIR to use monomorphized instance IDs
            rv_mono::rewrite_calls_to_instances(
                &mut mir_functions,
                &instance_map,
                &hir_ctx.functions,
                &hir_ctx.types,
            );

            // Compile all functions with Cranelift (supports function calls)
            self.jit.compile_multiple(&mir_functions)?;

            let target_func_id = target_mir_func_id.context("Target function not found in MIR")?;
            let code_ptr = self
                .jit
                .compiled_functions
                .get(&target_func_id)
                .copied()
                .context("Target function was not compiled")?;

            let result = unsafe { self.jit.execute(code_ptr) };
            Ok(result)
        } else {
            anyhow::bail!("Failed to parse file");
        }
    }

    /// Compile and execute a function from a multi-file project.
    ///
    /// Discovers all module files, lowers each to MIR, compiles all functions
    /// together with Cranelift, and executes the requested function.
    fn execute_project_function(&mut self, main_path: &Path, function_name: &str) -> Result<i64> {
        let project = rv_database::lower_project(main_path)?;

        // Find the target function in the root module
        let root_hir = project
            .root_hir()
            .context("No root module found in project")?;

        let target_func_id = root_hir
            .functions
            .iter()
            .find(|(_, func)| root_hir.interner.resolve(&func.name) == function_name)
            .map(|(id, _)| *id)
            .with_context(|| format!("Function '{function_name}' not found in root module"))?;

        // Build cross-module function map for MIR lowering
        let mut cross_module_functions =
            std::collections::HashMap::<(Vec<String>, String), rv_hir::FunctionId>::new();

        for (mod_path, module_data) in &project.modules {
            if mod_path.is_empty() {
                continue;
            }
            for (func_id, func) in &module_data.hir.functions {
                let func_name = module_data.hir.interner.resolve(&func.name);
                cross_module_functions.insert((mod_path.clone(), func_name), *func_id);
            }
        }

        // Collect all MIR functions from all modules
        let mut all_mir_functions = Vec::new();

        // Evaluate const and static items for root module
        let root_const_values =
            rv_const_eval::evaluate_const_items(&root_hir.const_items, &root_hir.interner);
        let root_static_values = rv_const_eval::evaluate_static_items(
            &root_hir.static_items,
            &root_hir.const_items,
            &root_const_values,
            &root_hir.interner,
        );

        // Lower root module functions with cross-module resolution
        let mut root_type_inference = TypeInference::with_hir_context(
            &root_hir.impl_blocks,
            &root_hir.functions,
            &root_hir.types,
            &root_hir.structs,
            &root_hir.enums,
            &root_hir.interner,
        );
        root_type_inference.set_const_static_items(&root_hir.const_items, &root_hir.static_items);

        // Infer and lower each non-generic root function to MIR.
        // Inference and lowering must be interleaved because ExprIds are local
        // to each function body and would collide in the shared TyContext.
        for (_, func) in root_hir
            .functions
            .iter()
            .filter(|(_, func)| func.generics.is_empty())
            .filter(|(func_id, _)| !root_hir.default_method_bodies.contains(func_id))
        {
            root_type_inference.context_mut().clear_expr_types();
            root_type_inference.infer_function(func);
            let mir_result = LoweringContext::lower_function_cross_module(
                func,
                root_type_inference.context_mut(),
                &root_hir.structs,
                &root_hir.enums,
                &root_hir.impl_blocks,
                &root_hir.functions,
                &root_hir.types,
                &root_hir.traits,
                &root_hir.interner,
                &cross_module_functions,
                &root_hir.lang_items,
                &root_const_values,
                &root_static_values,
            );
            crate::print_mir_diagnostics(&mir_result.diagnostics);
            let func_name_str = root_hir.interner.resolve(&func.name);
            crate::run_borrow_check(&mir_result.function, &func_name_str);
            all_mir_functions.push(mir_result.function);
        }

        // Lower non-root module functions
        for (mod_path, module_data) in &project.modules {
            if mod_path.is_empty() {
                continue;
            }

            let mod_hir = &module_data.hir;

            // Evaluate const and static items for this module
            let mod_const_values =
                rv_const_eval::evaluate_const_items(&mod_hir.const_items, &mod_hir.interner);
            let mod_static_values = rv_const_eval::evaluate_static_items(
                &mod_hir.static_items,
                &mod_hir.const_items,
                &mod_const_values,
                &mod_hir.interner,
            );

            let mut mod_type_inference = TypeInference::with_hir_context(
                &mod_hir.impl_blocks,
                &mod_hir.functions,
                &mod_hir.types,
                &mod_hir.structs,
                &mod_hir.enums,
                &mod_hir.interner,
            );
            mod_type_inference.set_const_static_items(&mod_hir.const_items, &mod_hir.static_items);

            // Infer and lower each non-generic module function to MIR.
            // Inference and lowering must be interleaved because ExprIds are local
            // to each function body and would collide in the shared TyContext.
            for (_, func) in mod_hir
                .functions
                .iter()
                .filter(|(_, func)| func.generics.is_empty())
                .filter(|(func_id, _)| !mod_hir.default_method_bodies.contains(func_id))
            {
                mod_type_inference.context_mut().clear_expr_types();
                mod_type_inference.infer_function(func);
                let mir_result = LoweringContext::lower_function(
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
                let func_name_str = mod_hir.interner.resolve(&func.name);
                crate::run_borrow_check(&mir_result.function, &func_name_str);
                all_mir_functions.push(mir_result.function);
            }
        }

        // Compile all functions together with Cranelift
        if all_mir_functions.is_empty() {
            anyhow::bail!("No functions to compile");
        }

        self.jit.compile_multiple(&all_mir_functions)?;

        let code_ptr = self
            .jit
            .compiled_functions
            .get(&target_func_id)
            .copied()
            .context("Target function was not compiled")?;

        let result = unsafe { self.jit.execute(code_ptr) };
        Ok(result)
    }

    /// Check if a project has multiple files (mod declarations referencing other files).
    fn is_multi_file_project(main_path: &Path) -> Result<bool> {
        let files = rv_database::discover_module_files(main_path)?;
        Ok(files.len() > 1)
    }

    /// Compile and run a single source file (for compiletest)
    pub fn compile_and_run(&self, file: &Path, _args: &[String]) -> Result<()> {
        let mut backend = Self::new()?;
        let source_file = backend.load_file(file)?;

        // Execute the main function
        let result = backend.execute_function(source_file, "main")?;

        // Print the result if it's not 0 (representing unit)
        if result != 0 {
            println!("{result}");
        }

        Ok(())
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

        let mut backend = Self::new()?;

        let result = if Self::is_multi_file_project(&main_path)? {
            backend.execute_project_function(&main_path, "main")?
        } else {
            let source_file = backend.load_file(&main_path)?;
            backend.execute_function(source_file, "main")?
        };

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

        if let Some(bin) = manifest.main_bin() {
            let main_path = project_dir.join(&bin.path);

            if Self::is_multi_file_project(&main_path)? {
                // Multi-file project: use project-level compilation
                let project = rv_database::lower_project(&main_path)?;
                let root_hir = project
                    .root_hir()
                    .context("No root module found in project")?;

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

                    // Each test gets a fresh JIT instance
                    let mut backend = Self::new()?;
                    match backend.execute_project_function(&main_path, func_name) {
                        Ok(result) if result == 1 => {
                            passed += 1;
                            messages.push(format!("  \u{2713} {func_name}"));
                        }
                        Ok(result) => {
                            failed += 1;
                            messages.push(format!(
                                "  \u{2717} {func_name} - returned {result} instead of true (1)"
                            ));
                        }
                        Err(error) => {
                            failed += 1;
                            messages.push(format!("  \u{2717} {func_name} - {error}"));
                        }
                    }
                }
            } else {
                // Single-file project
                let mut backend = Self::new()?;
                let source_file = backend.load_file(&main_path)?;

                let contents = backend.db.get_file_contents(source_file);
                let parse_result = rv_parser::parse_source(&contents);

                if let Some(syntax) = parse_result.syntax {
                    let hir_ctx = lower_source_file(&syntax);

                    for (_func_id, function) in &hir_ctx.functions {
                        let func_name = hir_ctx.interner.resolve(&function.name);

                        if func_name.starts_with("test_") {
                            messages.push(format!("Running test: {func_name}"));

                            match backend.execute_function(source_file, &func_name) {
                                Ok(result) if result == 1 => {
                                    passed += 1;
                                    messages.push(format!("  \u{2713} {func_name}"));
                                }
                                Ok(result) => {
                                    failed += 1;
                                    messages.push(format!(
                                        "  \u{2717} {func_name} - returned {result} instead of true (1)"
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
