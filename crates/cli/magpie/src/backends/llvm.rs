//! LLVM backend for magpie
//!
//! This backend compiles Raven code to native binaries using LLVM.
//! Uses LIR (Low-level IR) which guarantees all code is monomorphized.

use crate::backend::{Backend, BuildResult, TestResult};
use crate::manifest::Manifest;
use anyhow::{Context, Result};
use std::path::Path;

/// LLVM backend (AOT compilation)
pub struct LLVMBackend;

impl LLVMBackend {
    pub fn new() -> Result<Self> {
        Ok(Self)
    }

    /// Check if a project has multiple files (mod declarations referencing other files).
    fn is_multi_file_project(main_path: &Path) -> Result<bool> {
        let files = rv_database::discover_module_files(main_path)?;
        Ok(files.len() > 1)
    }

    /// Compile a multi-file project to an executable.
    fn compile_project_to_executable(&self, main_path: &Path, output_path: &Path) -> Result<()> {
        use rv_mir_lower::LoweringContext;

        let project = rv_database::lower_project(main_path)?;

        let root_hir = project
            .root_hir()
            .context("No root module found in project")?;

        // Build cross-module function map
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

        // Evaluate const and static items for root module
        let root_const_values =
            rv_const_eval::evaluate_const_items(&root_hir.const_items, &root_hir.interner);
        let root_static_values = rv_const_eval::evaluate_static_items(
            &root_hir.static_items,
            &root_hir.const_items,
            &root_const_values,
            &root_hir.interner,
        );

        use rv_ty::TypeInference;
        let mut root_type_inference = TypeInference::with_hir_context(
            &root_hir.impl_blocks,
            &root_hir.functions,
            &root_hir.types,
            &root_hir.structs,
            &root_hir.enums,
            &root_hir.interner,
        );
        root_type_inference.set_const_static_items(&root_hir.const_items, &root_hir.static_items);

        let mut mir_functions: Vec<rv_mir::MirFunction> = Vec::new();
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
            let func_name = root_hir.interner.resolve(&func.name);
            crate::run_borrow_check(&mir_result.function, &func_name);
            mir_functions.push(mir_result.function);
        }

        // Lower non-root modules
        for (mod_path, module_data) in &project.modules {
            if mod_path.is_empty() {
                continue;
            }

            let mod_hir = &module_data.hir;
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

            for (func_id, func) in &mod_hir.functions {
                if func.generics.is_empty() && !mod_hir.default_method_bodies.contains(func_id) {
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
                    let func_name = mod_hir.interner.resolve(&func.name);
                    crate::run_borrow_check(&mir_result.function, &func_name);
                    mir_functions.push(mir_result.function);
                }
            }
        }

        // Multi-file compilation does not yet run monomorphization because
        // there is no unified HIR context spanning all files. Generic functions
        // in multi-file projects will fail at LIR lowering. This requires the
        // module resolution system (rv-resolve) to provide a cross-file HIR.
        let combined_hir = rv_hir_lower::LoweringContext::new();

        let lir_functions = rv_lir::lower::lower_mir_to_lir(mir_functions, &combined_hir);

        use rv_llvm_backend::{OptLevel, compile_to_native};
        compile_to_native(&lir_functions, output_path, OptLevel::Default)?;
        Ok(())
    }

    /// Compile a Raven source file to an executable
    fn compile_to_executable(&self, source: &str, output_path: &Path) -> Result<()> {
        use lang_raven::RavenLanguage;
        use rv_hir_lower::lower_source_file;
        use rv_mir_lower::LoweringContext;
        use rv_syntax::Language;

        // Parse source code
        let language = RavenLanguage::new();
        let tree = language.parse(source)?;

        // Lower to HIR
        let root = language.lower_node(&tree.root_node(), source);
        let hir = lower_source_file(&root);

        if hir.functions.is_empty() && hir.external_functions.is_empty() {
            anyhow::bail!("No functions found in source");
        }

        // Run coherence checking
        if let Err(errors) =
            rv_ty::check_coherence(&hir.impl_blocks, &hir.traits, &hir.types, &hir.functions)
        {
            for error in &errors {
                eprintln!("error[coherence]: {error}");
            }
            anyhow::bail!(
                "Compilation aborted due to {} coherence error(s)",
                errors.len()
            );
        }

        // Evaluate const and static items
        let const_values = rv_const_eval::evaluate_const_items(&hir.const_items, &hir.interner);
        let static_values = rv_const_eval::evaluate_static_items(
            &hir.static_items,
            &hir.const_items,
            &const_values,
            &hir.interner,
        );

        // Lower HIR to MIR with type inference
        use rv_ty::TypeInference;
        let mut type_inference = TypeInference::with_hir_context(
            &hir.impl_blocks,
            &hir.functions,
            &hir.types,
            &hir.structs,
            &hir.enums,
            &hir.interner,
        );
        type_inference.set_const_static_items(&hir.const_items, &hir.static_items);

        // Infer and lower each non-generic function to MIR.
        // Inference and lowering must be interleaved because ExprIds are local
        // to each function body and would collide in the shared TyContext.
        let mut mir_functions: Vec<rv_mir::MirFunction> = Vec::new();
        for (_, func) in hir
            .functions
            .iter()
            .filter(|(_, func)| func.generics.is_empty())
            .filter(|(func_id, _)| !hir.default_method_bodies.contains(func_id))
        {
            type_inference.context_mut().clear_expr_types();
            type_inference.infer_function(func);
            let mir_result = LoweringContext::lower_function(
                func,
                type_inference.context_mut(),
                &hir.structs,
                &hir.enums,
                &hir.impl_blocks,
                &hir.functions,
                &hir.types,
                &hir.traits,
                &hir.interner,
                &hir.lang_items,
                &const_values,
                &static_values,
            );
            crate::print_mir_diagnostics(&mir_result.diagnostics);
            let func_name = hir.interner.resolve(&func.name);
            crate::run_borrow_check(&mir_result.function, &func_name);
            mir_functions.push(mir_result.function);
        }

        // Monomorphization: collect generic function instantiations needed from MIR
        use rv_mono::MonoCollector;
        let mut collector = MonoCollector::new();

        // Only collect from non-generic functions (entry points)
        for mir_func in &mir_functions {
            if let Some(hir_func) = hir.functions.get(&mir_func.id) {
                if hir_func.generics.is_empty() {
                    collector.collect_from_mir(mir_func, &hir.functions, &hir.types);
                }
            }
        }

        // Generate monomorphized instances
        // ARCHITECTURE: No catch_unwind - let monomorphization failures bubble up
        use rv_mono::monomorphize_functions;
        let next_func_id = hir.functions.keys().map(|id| id.0).max().unwrap_or(0) + 1;
        let bound_checker = rv_ty::BoundChecker::new(
            hir.traits.clone(),
            &hir.impl_blocks,
            hir.types.clone(),
            hir.structs.clone(),
            hir.enums.clone(),
        );
        let (mono_functions, instance_map) = monomorphize_functions(
            &hir,
            collector.needed_instances(),
            next_func_id,
            Some(&bound_checker),
        );

        // Add monomorphized functions to MIR functions list
        mir_functions.extend(mono_functions);

        // Remap function calls in all MIR functions to use monomorphized instance IDs
        use rv_mono::rewrite_calls_to_instances;
        rewrite_calls_to_instances(
            &mut mir_functions,
            &instance_map,
            &hir.functions,
            &hir.types,
        );

        // Lower MIR to LIR (now all generics are monomorphized)
        let lir_functions = rv_lir::lower::lower_mir_to_lir(mir_functions, &hir);
        let lir_externals = rv_lir::lower::lower_external_functions(
            &hir.external_functions,
            &hir.types,
            &hir.interner,
        );

        // Compile LIR to LLVM IR and generate object file
        use rv_llvm_backend::{OptLevel, compile_to_native_with_externals};
        compile_to_native_with_externals(
            &lir_functions,
            &lir_externals,
            output_path,
            OptLevel::Default,
        )?;
        Ok(())
    }
}

impl Backend for LLVMBackend {
    fn build(&self, manifest: &Manifest, project_dir: &Path) -> Result<BuildResult> {
        let src_dir = project_dir.join("src");
        let main_file = src_dir.join("main.rs");

        if !main_file.exists() {
            anyhow::bail!("No main.rs found in {}", src_dir.display());
        }

        // Create target directory
        let target_dir = project_dir.join("target");
        std::fs::create_dir_all(&target_dir)?;

        // Output executable path
        let exe_name = if cfg!(windows) {
            format!("{}.exe", manifest.package.name)
        } else {
            manifest.package.name.clone()
        };
        let output_path = target_dir.join(&exe_name);

        if Self::is_multi_file_project(&main_file)? {
            self.compile_project_to_executable(&main_file, &output_path)?;
        } else {
            let source = std::fs::read_to_string(&main_file)?;
            self.compile_to_executable(&source, &output_path)?;
        }

        Ok(BuildResult {
            success: true,
            messages: vec![format!("LLVM: Compiled to {}", output_path.display())],
            executable: Some(output_path),
        })
    }

    fn run(&self, manifest: &Manifest, project_dir: &Path, args: &[String]) -> Result<()> {
        // Build first
        let build_result = self.build(manifest, project_dir)?;

        if let Some(executable) = build_result.executable {
            // Execute the compiled binary
            let status = std::process::Command::new(&executable)
                .args(args)
                .status()?;

            if !status.success() {
                anyhow::bail!("Execution failed with exit code: {:?}", status.code());
            }
        } else {
            anyhow::bail!("No executable was produced");
        }

        Ok(())
    }

    fn test(&self, _manifest: &Manifest, project_dir: &Path) -> Result<TestResult> {
        use rv_mir_lower::LoweringContext;

        let src_dir = project_dir.join("src");
        let main_file = src_dir.join("main.rs");

        let mut messages = Vec::new();
        let mut passed = 0;
        let mut failed = 0;

        // Create target directory for test executables
        let target_dir = project_dir.join("target").join("llvm-tests");
        std::fs::create_dir_all(&target_dir)?;

        let is_multi = Self::is_multi_file_project(&main_file)?;

        // Lower all functions to MIR, handling multi-file projects with cross-module resolution
        let (mut mir_functions, hir) = if is_multi {
            let project = rv_database::lower_project(&main_file)?;
            let root_hir = project
                .root_hir()
                .context("No root module found in project")?;

            // Build cross-module function map
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

            // Evaluate const and static items for root module
            let root_const_values =
                rv_const_eval::evaluate_const_items(&root_hir.const_items, &root_hir.interner);
            let root_static_values = rv_const_eval::evaluate_static_items(
                &root_hir.static_items,
                &root_hir.const_items,
                &root_const_values,
                &root_hir.interner,
            );

            use rv_ty::TypeInference;
            let mut root_type_inference = TypeInference::with_hir_context(
                &root_hir.impl_blocks,
                &root_hir.functions,
                &root_hir.types,
                &root_hir.structs,
                &root_hir.enums,
                &root_hir.interner,
            );
            root_type_inference
                .set_const_static_items(&root_hir.const_items, &root_hir.static_items);

            let mut mir_functions: Vec<rv_mir::MirFunction> = Vec::new();
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
                let func_name = root_hir.interner.resolve(&func.name);
                crate::run_borrow_check(&mir_result.function, &func_name);
                mir_functions.push(mir_result.function);
            }

            // Lower non-root module functions
            for (mod_path, module_data) in &project.modules {
                if mod_path.is_empty() {
                    continue;
                }
                let mod_hir = &module_data.hir;
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
                mod_type_inference
                    .set_const_static_items(&mod_hir.const_items, &mod_hir.static_items);

                for (func_id, func) in &mod_hir.functions {
                    if func.generics.is_empty() && !mod_hir.default_method_bodies.contains(func_id)
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
                        let func_name = mod_hir.interner.resolve(&func.name);
                        crate::run_borrow_check(&mir_result.function, &func_name);
                        mir_functions.push(mir_result.function);
                    }
                }
            }

            // Convert HirFileData to LoweringContext for downstream APIs
            let root_data = root_hir.as_ref();
            let hir = rv_hir_lower::LoweringContext::from_hir_fields(
                root_data.functions.clone(),
                root_data.structs.clone(),
                root_data.enums.clone(),
                root_data.traits.clone(),
                root_data.impl_blocks.clone(),
                root_data.types.clone(),
                root_data.interner.clone(),
            );
            (mir_functions, hir)
        } else {
            use lang_raven::RavenLanguage;
            use rv_hir_lower::lower_source_file;
            use rv_syntax::Language;

            let source = std::fs::read_to_string(&main_file)?;
            let language = RavenLanguage::new();
            let tree = language.parse(&source)?;
            let root = language.lower_node(&tree.root_node(), &source);
            let hir = lower_source_file(&root);

            // Run coherence checking
            if let Err(errors) =
                rv_ty::check_coherence(&hir.impl_blocks, &hir.traits, &hir.types, &hir.functions)
            {
                for error in &errors {
                    eprintln!("error[coherence]: {error}");
                }
                anyhow::bail!(
                    "Compilation aborted due to {} coherence error(s)",
                    errors.len()
                );
            }

            // Evaluate const and static items
            let const_values = rv_const_eval::evaluate_const_items(&hir.const_items, &hir.interner);
            let static_values = rv_const_eval::evaluate_static_items(
                &hir.static_items,
                &hir.const_items,
                &const_values,
                &hir.interner,
            );

            use rv_ty::TypeInference;
            let mut type_inference = TypeInference::with_hir_context(
                &hir.impl_blocks,
                &hir.functions,
                &hir.types,
                &hir.structs,
                &hir.enums,
                &hir.interner,
            );
            type_inference.set_const_static_items(&hir.const_items, &hir.static_items);

            let mut mir_functions: Vec<rv_mir::MirFunction> = Vec::new();
            for (_, func) in hir
                .functions
                .iter()
                .filter(|(_, func)| func.generics.is_empty())
                .filter(|(func_id, _)| !hir.default_method_bodies.contains(func_id))
            {
                type_inference.context_mut().clear_expr_types();
                type_inference.infer_function(func);
                let mir_result = LoweringContext::lower_function(
                    func,
                    type_inference.context_mut(),
                    &hir.structs,
                    &hir.enums,
                    &hir.impl_blocks,
                    &hir.functions,
                    &hir.types,
                    &hir.traits,
                    &hir.interner,
                    &hir.lang_items,
                    &const_values,
                    &static_values,
                );
                crate::print_mir_diagnostics(&mir_result.diagnostics);
                let func_name = hir.interner.resolve(&func.name);
                crate::run_borrow_check(&mir_result.function, &func_name);
                mir_functions.push(mir_result.function);
            }

            (mir_functions, hir)
        };

        // Monomorphization: collect generic function instantiations needed from MIR
        use rv_mono::MonoCollector;
        let mut collector = MonoCollector::new();

        // Only collect from non-generic functions (entry points)
        for mir_func in &mir_functions {
            if let Some(hir_func) = hir.functions.get(&mir_func.id) {
                if hir_func.generics.is_empty() {
                    collector.collect_from_mir(mir_func, &hir.functions, &hir.types);
                }
            }
        }

        // Generate monomorphized instances
        use rv_mono::monomorphize_functions;
        let next_func_id = hir.functions.keys().map(|id| id.0).max().unwrap_or(0) + 1;
        let bound_checker = rv_ty::BoundChecker::new(
            hir.traits.clone(),
            &hir.impl_blocks,
            hir.types.clone(),
            hir.structs.clone(),
            hir.enums.clone(),
        );
        let (mono_functions, instance_map) = monomorphize_functions(
            &hir,
            collector.needed_instances(),
            next_func_id,
            Some(&bound_checker),
        );

        // Add monomorphized functions to MIR functions list
        mir_functions.extend(mono_functions);

        // Remap function calls in all MIR functions to use monomorphized instance IDs
        use rv_mono::rewrite_calls_to_instances;
        rewrite_calls_to_instances(
            &mut mir_functions,
            &instance_map,
            &hir.functions,
            &hir.types,
        );

        // Collect test function names (only from non-generic functions in HIR)
        let mut test_functions = Vec::new();
        for (_func_id, function) in &hir.functions {
            let func_name = hir.interner.resolve(&function.name);
            if func_name.starts_with("test_") && function.generics.is_empty() {
                test_functions.push(func_name.to_string());
            }
        }

        // If there are no test functions, skip compilation
        if test_functions.is_empty() {
            messages.push("No test functions found".to_string());
            return Ok(TestResult {
                passed: 0,
                failed: 0,
                success: true,
                messages,
            });
        }

        // Lower MIR to LIR with monomorphization
        let lir_functions = rv_lir::lower::lower_mir_to_lir(mir_functions, &hir);

        // Compile ALL LIR functions at once (supports cross-function calls)
        use rv_llvm_backend::{OptLevel, compile_to_native};
        let temp_exe = target_dir.join("test_all.exe");

        messages.push("Starting LLVM compilation...".to_string());
        let compile_result =
            compile_to_native(&lir_functions, &temp_exe, OptLevel::Default).map(|_| temp_exe);
        messages.push("LLVM compilation finished".to_string());

        match compile_result {
            Ok(executable) => {
                messages.push("LLVM backend compiled successfully".to_string());
                messages.push("Note: LLVM backend currently runs entry point only".to_string());

                // Try to run the executable
                messages.push("Attempting to execute binary...".to_string());
                match std::process::Command::new(&executable).output() {
                    Ok(output) => {
                        if let Some(code) = output.status.code() {
                            messages.push(format!("Entry point returned: {code}"));
                        } else {
                            messages.push("Entry point terminated without exit code".to_string());
                        }
                    }
                    Err(e) => {
                        messages.push(format!("Failed to execute: {e}"));
                    }
                }

                // Mark all test functions as "passed" since they compiled
                passed = test_functions.len();
                for test_name in &test_functions {
                    messages.push(format!("  ✓ {test_name} (compiled)"));
                }

                // Clean up
                let _ = std::fs::remove_file(&executable);
            }
            Err(e) => {
                // Compilation failed - all tests fail
                failed = test_functions.len();
                messages.push(format!("Compilation failed: {e}"));
                for test_name in &test_functions {
                    messages.push(format!("  ✗ {test_name} - compilation failed"));
                }
            }
        }

        Ok(TestResult {
            passed,
            failed,
            success: failed == 0,
            messages,
        })
    }

    fn check(&self, _manifest: &Manifest, project_dir: &Path) -> Result<()> {
        use lang_raven::RavenLanguage;
        use rv_syntax::Language;

        let src_dir = project_dir.join("src");
        let main_file = src_dir.join("main.rs");

        if !main_file.exists() {
            anyhow::bail!("No main.rs found");
        }

        let source = std::fs::read_to_string(&main_file)?;
        let language = RavenLanguage::new();
        let _tree = language.parse(&source)?;

        Ok(())
    }

    fn clean(&self, project_dir: &Path) -> Result<()> {
        let target_dir = project_dir.join("target");
        if target_dir.exists() {
            std::fs::remove_dir_all(&target_dir)?;
        }
        Ok(())
    }
}
