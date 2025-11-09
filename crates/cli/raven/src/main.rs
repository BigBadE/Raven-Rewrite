//! Raven compiler CLI
//!
//! Main entry point for the Raven compiler toolchain

use anyhow::Result;
use clap::{Parser, Subcommand};
use std::path::PathBuf;

mod build;
mod check;
mod compiler;
mod new;
mod run;

#[derive(Parser)]
#[command(name = "raven")]
#[command(about = "Raven compiler toolchain", long_about = None)]
#[command(version)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Build a Raven project
    Build {
        /// Path to the project or source file
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Backend to use (interpreter or jit)
        #[arg(long, default_value = "jit")]
        backend: String,

        /// Release mode (optimizations)
        #[arg(long)]
        release: bool,
    },

    /// Run a Raven project
    Run {
        /// Path to the project or source file
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Backend to use (interpreter or jit)
        #[arg(long, default_value = "jit")]
        backend: String,

        /// Release mode (optimizations)
        #[arg(long)]
        release: bool,
    },

    /// Check a Raven project for errors
    Check {
        /// Path to the project or source file
        #[arg(default_value = ".")]
        path: PathBuf,
    },

    /// Create a new Raven project
    New {
        /// Project name
        name: String,

        /// Project type (bin or lib)
        #[arg(long, default_value = "bin")]
        template: String,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Build { path, backend, release } => {
            build::build(&path, &backend, release)?;
        }
        Commands::Run { path, backend, release } => {
            run::run(&path, &backend, release)?;
        }
        Commands::Check { path } => {
            check::check(&path)?;
        }
        Commands::New { name, template } => {
            new::create_project(&name, &template)?;
        }
    }

    Ok(())
}
