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

/// Print any diagnostics produced during MIR lowering.
pub fn print_mir_diagnostics(diagnostics: &[rv_mir_lower::MirDiagnostic]) {
    for diag in diagnostics {
        let severity = match diag.severity {
            rv_mir_lower::MirDiagnosticSeverity::Warning => "warning",
            rv_mir_lower::MirDiagnosticSeverity::Error => "error",
        };
        eprintln!("{}[mir]: {}", severity, diag.message);
    }
}

/// Run borrow checking on a MIR function. Reports errors to stderr.
/// Returns true if no borrow errors were found.
pub fn run_borrow_check(mir_func: &rv_mir::MirFunction, func_name: &str) -> bool {
    match rv_borrow_check::BorrowChecker::check(mir_func) {
        Ok(()) => true,
        Err(errors) => {
            for error in &errors {
                eprintln!(
                    "error[borrow-check]: in function '{}': {}",
                    func_name,
                    error.detailed_message()
                );
            }
            false
        }
    }
}
