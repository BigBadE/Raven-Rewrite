//! Magpie - Package manager for Raven
//!
//! A flexible package manager that supports multiple backends.

#![allow(
    clippy::print_stdout,
    clippy::print_stderr,
    reason = "CLI tool needs to print to stdout/stderr"
)]

pub mod backend;
pub mod backends;
pub mod manifest;

use anyhow::{anyhow, Context, Result};
use backend::Backend;
use backends::{CraneliftBackend, LLVMBackend, RavenBackend};
use clap::{Parser, Subcommand};
use manifest::Manifest;
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
        Command::Compile { ref file, ref output, ref args, .. } => cmd_compile(&cli, file, output.as_ref(), args)?,
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

fn cmd_compile(cli: &Cli, file: &PathBuf, output_file: Option<&PathBuf>, args: &[String]) -> Result<()> {
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

        // Lower HIR to MIR with type inference
        use rv_ty::TypeInference;
        let mut type_inference = TypeInference::with_hir_context(
            &hir.impl_blocks,
            &hir.functions,
            &hir.types,
            &hir.structs,
            &hir.enums,
            &hir.traits,
            &hir.interner,
        );

        // ARCHITECTURE: Type inference is MANDATORY before MIR lowering
        // ALL non-generic functions must have types inferred here
        for (_, func) in &hir.functions {
            if func.generics.is_empty() {
                type_inference.infer_function(func);
            }
        }

        // Lower non-generic functions to MIR (entry points)
        // Use filter_map with catch_unwind to skip functions that fail to lower (e.g., trait methods)
        let mut mir_functions: Vec<_> = hir
            .functions
            .iter()
            .filter(|(_, func)| func.generics.is_empty())
            .filter_map(|(_, func)| {
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    LoweringContext::lower_function(
                        func,
                        type_inference.context_mut(),
                        &hir.structs,
                        &hir.enums,
                        &hir.impl_blocks,
                        &hir.functions,
                        &hir.types,
                        &hir.traits,
                        &hir.interner,
                    )
                })).ok()
            })
            .collect();

        // Monomorphization: collect generic function instantiations needed from MIR
        use rv_mono::MonoCollector;
        let mut collector = MonoCollector::new();

        // Only collect from non-generic functions (entry points)
        for mir_func in &mir_functions {
            if let Some(hir_func) = hir.functions.get(&mir_func.id) {
                if hir_func.generics.is_empty() {
                    collector.collect_from_mir(mir_func);
                }
            }
        }

        // Generate monomorphized instances (catch panics from type errors)
        use rv_mono::monomorphize_functions;
        let next_func_id = hir.functions.keys().map(|id| id.0).max().unwrap_or(0) + 1;
        let mono_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            monomorphize_functions(
                &hir,
                type_inference.context(),
                collector.needed_instances(),
                next_func_id,
            )
        }));

        if let Ok((mono_functions, instance_map)) = mono_result {
            // Add monomorphized functions to MIR functions list
            mir_functions.extend(mono_functions);

            // Remap function calls in all MIR functions to use monomorphized instance IDs
            use rv_mono::rewrite_calls_to_instances;
            rewrite_calls_to_instances(&mut mir_functions, &instance_map);
        }
        // If monomorphization fails, continue with just the non-generic functions

        // Lower MIR to LIR (now all generics are monomorphized)
        let lir_functions = rv_lir::lower::lower_mir_to_lir(mir_functions, &hir);

        // Compile LIR to LLVM IR and generate object file
        use rv_llvm_backend::{compile_to_native_with_externals, OptLevel};
        compile_to_native_with_externals(
            &lir_functions,
            &hir.external_functions,
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

    println!("Created {} project '{}'", if lib { "library" } else { "binary" }, name);

    Ok(())
}
