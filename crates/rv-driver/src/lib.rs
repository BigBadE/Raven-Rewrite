//! Pipeline orchestration — the one crate that knows every phase.
//!
//! `source ──parse──▶ AST ──lower──▶ IR<Parsed> ──elaborate──▶ IR<Lowerable> + obligations`
//! then each obligation is discharged by the solver registry, and the verified
//! `IR<Lowerable>` is compiled to bytecode and (optionally) run.
//!
//! This is *outside* the trust base: a bug here yields a rejected program or a
//! failed obligation, never an unsound "verified".
//!
//! # Incremental engine
//!
//! As of the salsa integration, the driver no longer chains the pipeline phases
//! by hand. It delegates to [`rv_db`], where parse → lower → elaborate →
//! borrow-check → discharge is a graph of memoized, dependency-tracked salsa
//! queries (see the `rv-db` crate docs for the query graph). The driver's job is
//! now just to translate `rv-db`'s salsa-friendly [`rv_db::AnalysisResult`] back
//! into the public [`Report`] shape and to drive optional execution. The public
//! API and behavior are unchanged.

pub use rv_vm::Value;

pub mod unify;

/// The outcome of one verification obligation.
#[derive(Debug)]
pub struct ObligationResult {
    pub origin: String,
    /// Whether the solver registry discharged this obligation.
    pub discharged: bool,
}
impl ObligationResult {
    pub fn ok(&self) -> bool {
        self.discharged
    }
}

/// The end-to-end result of running the pipeline on a source program.
#[derive(Debug)]
pub struct Report {
    pub obligations: Vec<ObligationResult>,
    /// Borrow/ownership violations (use-after-move, borrow conflicts). Empty = clean.
    pub borrow_errors: Vec<String>,
    /// `Some` if an entry point was requested: the value it returned, or a runtime error.
    pub run: Option<Result<Value, String>>,
}
impl Report {
    /// Did every obligation discharge AND the borrow checker pass?
    pub fn all_verified(&self) -> bool {
        self.borrow_errors.is_empty() && self.obligations.iter().all(ObligationResult::ok)
    }
    pub fn num_failed(&self) -> usize {
        self.obligations.iter().filter(|o| !o.ok()).count() + self.borrow_errors.len()
    }
}

/// Run the full pipeline. If `entry` is `Some`, the *verified* program is compiled
/// and that entry point is executed with no arguments.
///
/// Returns `Err` only for *front-end* failures (parse / lower / type errors).
/// Verification failures are reported in [`Report::obligations`], not as `Err` —
/// the program is still well-formed, it just isn't proved.
pub fn run_pipeline(src: &str, entry: Option<&str>) -> Result<Report, String> {
    // Delegate the whole front end + verification to the salsa query graph in
    // `rv-db`. `compile_and_run` builds a `Database`, sets the `SourceProgram`
    // input, runs the memoized `analyze` query, and (re-using the memoized
    // elaboration) optionally compiles + runs the requested entry point.
    let (analysis, run) = rv_db::compile_and_run(src, entry);

    // A front-end (parse / lower / type) failure surfaces as `Err`, exactly as
    // the old hand-chained pipeline did.
    let analysis = match analysis {
        rv_db::AnalysisResult::Analyzed(a) => a,
        rv_db::AnalysisResult::FrontendError(e) => return Err(e),
    };

    // Translate the salsa-friendly summary back into the public `Report` shape.
    let obligations = analysis
        .obligations
        .into_iter()
        .map(|o| ObligationResult { origin: o.origin, discharged: o.ok })
        .collect();

    Ok(Report { obligations, borrow_errors: analysis.borrow_errors, run })
}

/// Convenience: verify only (no execution).
pub fn verify(src: &str) -> Result<Report, String> {
    run_pipeline(src, None)
}

// ---------------------------------------------------------------------------
// The verified-Raven path: the dependent-type-theory kernel + its surface.
// ---------------------------------------------------------------------------

/// The result of verifying (and optionally running) a Raven *kernel-surface* program:
/// which `fn`s had their correctness obligations discharged, which remain open, and the
/// rendered value of an evaluated entry point.
#[derive(Debug)]
pub struct RavenReport {
    pub verified: Vec<String>,
    pub open: Vec<String>,
    /// `Some` if an entry point was evaluated: its rendered value, or an eval error.
    pub run: Option<Result<String, String>>,
}
impl RavenReport {
    /// Every declared `fn` obligation discharged?
    pub fn all_verified(&self) -> bool {
        self.open.is_empty()
    }
}


/// Verify a Raven `.rv` program through the dependent kernel, loading only the **logic**
/// prelude (`Eq`, `And`/`Or`/`False`, `Not`/`Iff`) — *not* the full stdlib — so a `.rv` file
/// is self-contained and brings its own data types (`enum`s) and proofs. This is the unified
/// `.rv` surface's proof/verification path; obligations are discharged by the kernel.
pub fn verify_rv(src: &str, entry: Option<&str>) -> Result<RavenReport, String> {
    // The proof path now runs entirely through the **single** `rv-syntax` parser: the
    // prelude and the program are parsed by one lexer+parser and translated to kernel
    // Commands (see `unify`). The kernel re-checks every term.
    let mut session = rv_kernel::verify::Session::new();
    rv_kernel::logic::declare_logic(&mut session.k)?;
    run_unified(&mut session, RAVEN_PRELUDE).map_err(|e| format!("in the standard prelude: {e}"))?;
    run_unified(&mut session, src)?;
    let run = entry.map(|e| session.run_entry(e));
    Ok(RavenReport { verified: session.verified_fns(), open: session.open_fns(), run })
}

/// Parse `src` with the single `rv-syntax` parser, translate to kernel commands, and run
/// them on `session` (setting the source for span diagnostics).
fn run_unified(session: &mut rv_kernel::verify::Session, src: &str) -> Result<(), String> {
    let mut syms = rv_core::Symbols::new();
    let module = rv_syntax::parse(src, &mut syms)?;
    let cmds = unify::module_to_commands(&module, &syms)?;
    session.set_source(src);
    session.run_commands(cmds)
}

/// Verify a Raven `.rv` program through the **unified front-end**: the single
/// `rv-syntax` parser produces the one AST, which [`unify::module_to_commands`]
/// translates into kernel [`Command`](rv_kernel::surface::Command)s — no second text
/// parser. Semantics match [`verify_rv`] (same prelude, same kernel), but the proof
/// path now shares the executable surface's lexer+parser.
pub fn verify_rv_unified(src: &str, entry: Option<&str>) -> Result<RavenReport, String> {
    verify_rv(src, entry)
}

/// The Raven standard proof prelude (`Eq` combinators), written in Raven itself.
pub const RAVEN_PRELUDE: &str = include_str!("../prelude.rv");
