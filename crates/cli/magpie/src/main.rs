#![allow(
    clippy::print_stdout,
    clippy::print_stderr,
    reason = "CLI tool needs to print to stdout/stderr"
)]

use anyhow::{Context, Result, anyhow};
use clap::{Parser, Subcommand};
use magpie::backend::Backend;
use magpie::backends::{CraneliftBackend, LLVMBackend, RavenBackend};
use magpie::manifest::Manifest;
use std::env;
use std::path::PathBuf;

#[derive(Parser)]
#[clap(name = "magpie", version, about = "Package manager for Raven")]
struct Cli {
    #[clap(subcommand)]
    command: Command,

    /// Path to the project directory
    #[clap(long, global = true)]
    project_dir: Option<PathBuf>,

    /// Backend to use (interpreter or jit)
    #[clap(long, global = true, default_value = "interpreter")]
    backend: String,
}

#[derive(Subcommand)]
enum Command {
    /// Build the project
    Build,

    /// Run the project
    Run {
        /// Arguments to pass to the program
        #[clap(trailing_var_arg = true)]
        args: Vec<String>,
    },

    /// Compile and run a single file (for testing)
    #[clap(hide = true)]
    Compile {
        /// Source file to compile
        file: PathBuf,

        /// Library search path (rustc compat, ignored)
        #[clap(short = 'L', action = clap::ArgAction::Append)]
        lib_paths: Vec<String>,

        /// Target triple (rustc compat, ignored)
        #[clap(long)]
        target: Option<String>,

        /// Error format (rustc compat, ignored)
        #[clap(long)]
        error_format: Option<String>,

        /// Codegen options (rustc compat, ignored)
        #[clap(short = 'C', action = clap::ArgAction::Append)]
        codegen: Vec<String>,

        /// Output file (rustc compat, ignored)
        #[clap(short = 'o', long)]
        output: Option<PathBuf>,

        /// Arguments to pass to the program
        #[clap(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },

    /// Run tests
    Test,

    /// Check the project without building
    Check,

    /// Clean build artifacts
    Clean,

    /// Create a new project
    New {
        /// Project name
        name: String,

        /// Create a library instead of a binary
        #[clap(long)]
        lib: bool,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Command::Build => cmd_build(&cli)?,
        Command::Run { ref args } => cmd_run(&cli, args)?,
        Command::Compile {
            ref file,
            ref output,
            ref args,
            ..
        } => cmd_compile(&cli, file, output.as_ref(), args)?,
        Command::Test => cmd_test(&cli)?,
        Command::Check => cmd_check(&cli)?,
        Command::Clean => cmd_clean(&cli)?,
        Command::New { name, lib } => cmd_new(name, lib)?,
    }

    Ok(())
}

fn get_project_dir(cli: &Cli) -> PathBuf {
    cli.project_dir
        .clone()
        .unwrap_or_else(|| env::current_dir().unwrap())
}

fn cmd_build(cli: &Cli) -> Result<()> {
    let project_dir = get_project_dir(cli);
    let manifest = Manifest::find_in_dir(&project_dir)?;

    let result = match cli.backend.as_str() {
        "interpreter" => {
            let backend = RavenBackend::new();
            backend.build(&manifest, &project_dir)?
        }
        "jit" => {
            let backend = CraneliftBackend::new()?;
            backend.build(&manifest, &project_dir)?
        }
        _ => return Err(anyhow!("Unknown backend: {}", cli.backend)),
    };

    for message in &result.messages {
        println!("{message}");
    }

    if !result.success {
        anyhow::bail!("Build failed");
    }

    Ok(())
}

fn cmd_run(cli: &Cli, args: &[String]) -> Result<()> {
    let project_dir = get_project_dir(cli);
    let manifest = Manifest::find_in_dir(&project_dir)?;

    match cli.backend.as_str() {
        "interpreter" => {
            let backend = RavenBackend::new();
            backend.run(&manifest, &project_dir, args)?;
        }
        "jit" => {
            let backend = CraneliftBackend::new()?;
            backend.run(&manifest, &project_dir, args)?;
        }
        _ => return Err(anyhow!("Unknown backend: {}", cli.backend)),
    }

    Ok(())
}

fn cmd_test(cli: &Cli) -> Result<()> {
    let project_dir = get_project_dir(cli);
    let manifest = Manifest::find_in_dir(&project_dir)?;

    let result = match cli.backend.as_str() {
        "interpreter" => {
            let backend = RavenBackend::new();
            backend.test(&manifest, &project_dir)?
        }
        "jit" => {
            let backend = CraneliftBackend::new()?;
            backend.test(&manifest, &project_dir)?
        }
        "llvm" => {
            let backend = LLVMBackend::new()?;
            backend.test(&manifest, &project_dir)?
        }
        _ => return Err(anyhow!("Unknown backend: {}", cli.backend)),
    };

    for message in &result.messages {
        println!("{message}");
    }

    println!();
    println!(
        "Test result: {} passed, {} failed",
        result.passed, result.failed
    );

    if !result.success {
        anyhow::bail!("Tests failed");
    }

    Ok(())
}

fn cmd_check(cli: &Cli) -> Result<()> {
    let project_dir = get_project_dir(cli);
    let manifest = Manifest::find_in_dir(&project_dir)?;

    let backend = RavenBackend::new();
    backend.check(&manifest, &project_dir)?;

    println!("Check completed successfully");

    Ok(())
}

fn cmd_clean(cli: &Cli) -> Result<()> {
    let project_dir = get_project_dir(cli);

    let backend = RavenBackend::new();
    backend.clean(&project_dir)?;

    println!("Clean completed");

    Ok(())
}

fn cmd_compile(
    cli: &Cli,
    file: &PathBuf,
    output_file: Option<&PathBuf>,
    args: &[String],
) -> Result<()> {
    if !file.exists() {
        anyhow::bail!("File '{}' not found", file.display());
    }

    // If -o is specified, compile to native executable using LLVM backend
    if let Some(output) = output_file {
        use lang_raven::RavenLanguage;
        use rv_hir_lower::lower_source_file;
        use rv_mir_lower::LoweringContext;
        use rv_syntax::Language;

        // Read source file
        let source = std::fs::read_to_string(file)?;

        // Parse source code
        let language = RavenLanguage::new();
        let tree = language.parse(&source)?;

        // Lower to HIR
        let root = language.lower_node(&tree.root_node(), &source);
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

        // ARCHITECTURE: Type inference is MANDATORY before MIR lowering
        // ALL non-generic functions must have types inferred here
        for (_, func) in &hir.functions {
            if func.generics.is_empty() {
                type_inference.infer_function(func);
            }
        }

        // Evaluate const and static items
        let const_values = rv_const_eval::evaluate_const_items(&hir.const_items, &hir.interner);
        let static_values = rv_const_eval::evaluate_static_items(
            &hir.static_items,
            &hir.const_items,
            &const_values,
            &hir.interner,
        );

        // Lower non-generic functions to MIR (entry points)
        // ARCHITECTURE: No catch_unwind - let panics bubble up to expose bugs
        let mut mir_functions: Vec<_> = hir
            .functions
            .iter()
            .filter(|(_, func)| func.generics.is_empty())
            .map(|(_, func)| {
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
                magpie::print_mir_diagnostics(&mir_result.diagnostics);
                mir_result.function
            })
            .collect();

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

        // Run borrow checker on all MIR functions
        let mut borrow_errors = false;
        for mir_func in &mir_functions {
            let func_name = hir
                .functions
                .get(&mir_func.id)
                .map(|f| hir.interner.resolve(&f.name).to_string())
                .unwrap_or_else(|| format!("{:?}", mir_func.id));
            if !magpie::run_borrow_check(mir_func, &func_name) {
                borrow_errors = true;
            }
        }
        if borrow_errors {
            anyhow::bail!("Borrow check failed");
        }

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
            output,
            OptLevel::Default,
        )?;

        return Ok(());
    }

    // No output file specified - run directly
    let runtime_args: Vec<String> = args
        .iter()
        .filter(|arg| {
            // Skip rustc-style flags
            !arg.starts_with('-')
        })
        .cloned()
        .collect();

    match cli.backend.as_str() {
        "interpreter" => {
            let backend = RavenBackend::new();
            backend.compile_and_run(file, &runtime_args)?;
        }
        "jit" => {
            let backend = CraneliftBackend::new()?;
            backend.compile_and_run(file, &runtime_args)?;
        }
        _ => return Err(anyhow!("Unknown backend: {}", cli.backend)),
    }

    Ok(())
}

fn cmd_new(name: String, lib: bool) -> Result<()> {
    let project_dir = PathBuf::from(&name);

    if project_dir.exists() {
        anyhow::bail!("Directory '{name}' already exists");
    }

    // Extract just the project name (last component of path)
    let project_name = project_dir
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(&name)
        .to_string();

    std::fs::create_dir_all(&project_dir)
        .with_context(|| format!("Failed to create directory '{name}'"))?;

    let src_dir = project_dir.join("src");
    std::fs::create_dir(&src_dir).context("Failed to create src directory")?;

    // Create Cargo.toml
    let manifest_content = if lib {
        format!(
            r#"[package]
name = "{project_name}"
version = "0.1.0"
edition = "2024"

[dependencies]

[lib]
path = "src/lib.rs"
"#
        )
    } else {
        format!(
            r#"[package]
name = "{project_name}"
version = "0.1.0"
edition = "2024"

[dependencies]

[[bin]]
name = "{project_name}"
path = "src/main.rs"
"#
        )
    };

    std::fs::write(project_dir.join("Cargo.toml"), manifest_content)
        .context("Failed to write Cargo.toml")?;

    // Create main source file
    let main_content = if lib {
        r#"fn test() -> i64 {
    42
}
"#
    } else {
        r#"fn main() -> i64 {
    42
}
"#
    };

    let main_file = if lib { "lib.rs" } else { "main.rs" };
    std::fs::write(src_dir.join(main_file), main_content)
        .with_context(|| format!("Failed to write src/{main_file}"))?;

    println!(
        "Created {} project '{}'",
        if lib { "library" } else { "binary" },
        name
    );

    Ok(())
}
