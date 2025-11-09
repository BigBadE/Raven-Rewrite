//! Raven code analyzer CLI
//!
//! Static analysis tools for Raven code

use anyhow::Result;
use clap::{Parser, Subcommand};
use std::path::PathBuf;

mod compiler;
mod duplicates;
mod lint;
mod metrics;

#[derive(Parser)]
#[command(name = "raven-analyzer")]
#[command(about = "Raven code analysis tools", long_about = None)]
#[command(version)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Run lint checks on code
    Lint {
        /// Path to the project or source file
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Output format (text or json)
        #[arg(long, default_value = "text")]
        format: String,

        /// Maximum complexity threshold
        #[arg(long, default_value = "10")]
        max_complexity: usize,

        /// Maximum parameters threshold
        #[arg(long, default_value = "5")]
        max_parameters: usize,
    },

    /// Calculate code metrics
    Metrics {
        /// Path to the project or source file
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Output format (text or json)
        #[arg(long, default_value = "text")]
        format: String,
    },

    /// Detect duplicate code
    Duplicates {
        /// Path to the project or source file
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Output format (text or json)
        #[arg(long, default_value = "text")]
        format: String,

        /// Minimum similarity threshold (0-100)
        #[arg(long, default_value = "80")]
        min_similarity: u8,

        /// Minimum expressions to consider
        #[arg(long, default_value = "3")]
        min_expressions: usize,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Lint {
            path,
            format,
            max_complexity,
            max_parameters,
        } => {
            lint::run_lint(&path, &format, max_complexity, max_parameters)?;
        }
        Commands::Metrics { path, format } => {
            metrics::calculate_metrics(&path, &format)?;
        }
        Commands::Duplicates {
            path,
            format,
            min_similarity,
            min_expressions,
        } => {
            duplicates::detect_duplicates(&path, &format, min_similarity, min_expressions)?;
        }
    }

    Ok(())
}
