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

    // If -o is specified, create a wrapper script instead of running directly
    if let Some(output) = output_file {
        // Get absolute path to magpie and source file
        let magpie_path = std::env::current_exe()
            .context("Failed to get magpie executable path")?;
        let source_path = file.canonicalize()
            .with_context(|| format!("Failed to canonicalize source path: {}", file.display()))?;

        // Create a wrapper script that calls magpie
        let wrapper_content = format!(
            "#!/bin/bash\nexec '{}' compile '{}' \"$@\"\n",
            magpie_path.display(),
            source_path.display()
        );

        std::fs::write(&output, wrapper_content)
            .with_context(|| format!("Failed to write output file: {}", output.display()))?;

        // Make it executable
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut perms = std::fs::metadata(&output)?.permissions();
            perms.set_mode(0o755);
            std::fs::set_permissions(&output, perms)?;
        }

        // Success - wrapper created
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
