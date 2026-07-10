//! `rv-db` — the **incremental** front-end for the raven-v3 pipeline, built on the
//! [salsa](https://crates.io/crates/salsa) on-demand incremental-computation framework
//! (version `0.27`).
//!
//! Instead of the straight function chain in `rv-driver`, the pipeline here is modeled
//! as a graph of **memoized, dependency-tracked queries**. Salsa records which inputs
//! each query read; when an input changes, only the queries that (transitively) depend
//! on it are recomputed. Re-running the top query with an *unchanged* input does not
//! re-execute any tracked function — the cached value is returned.
//!
//! # The query graph
//!
//! ```text
//!         ┌──────────────────────────┐
//!  INPUT  │ SourceProgram { text }   │   (a #[salsa::input]; the only mutable cell)
//!         └────────────┬─────────────┘
//!                      │ reads text
//!         ┌────────────▼─────────────┐
//!  query  │ parse_and_lower(src)     │   parse → lower; memoizes a Frontend
//!         │   summary (function names + parse/lower Ok/Err)
//!         └────────────┬─────────────┘
//!                      │
//!         ┌────────────▼─────────────┐
//!  query  │ elaborate(src)           │   infer types/phases + generate obligations
//!         │   memoizes: ElaboratedProgram  (Arc<IR<Lowerable> + Vec<Obligation>>)
//!         └────────────┬─────────────┘
//!                      │
//!         ┌────────────▼─────────────┐
//!  query  │ analyze(src)             │   borrow-check + discharge every obligation
//!         │   memoizes: AnalysisResult (salsa-friendly summary)
//!         └──────────────────────────┘
//! ```
//!
//! Each box is a salsa **tracked function** keyed on the `SourceProgram` input. Because
//! every query reads (directly or via a callee) `SourceProgram::text`, changing the text
//! invalidates all three; re-running with the same text re-executes none of them.
//!
//! # Handling the non-salsa-friendly IR
//!
//! Salsa requires every tracked-function return value to implement `salsa::Update` (and,
//! for the derive, effectively `'static`). The heavy intermediate values — `rv_ir::Program`
//! and `rv_infer::Elaborated` — are *not* `Eq`/`Update` and we are not allowed to change
//! the leaf crates. We therefore:
//!
//! * have the front-end query [`parse_and_lower`] return only a salsa-friendly [`Frontend`]
//!   *summary* (the un-cloneable, by-value-consumed `IR<Parsed>` never crosses a query edge),
//! * carry the elaboration bundle behind an [`Arc`] inside a thin newtype
//!   ([`ElaboratedProgram`]),
//! * hand-write an `unsafe impl salsa::Update` for that newtype that always reports the
//!   value as "changed" (a conservative, always-sound choice — it can only cause *extra*
//!   downstream recomputation, never a stale cache),
//! * and have the *top* query [`analyze`] return a fully salsa-friendly
//!   [`AnalysisResult`] (`Clone + PartialEq + Eq + Debug`), which is what callers and the
//!   driver consume. So the memoization that matters — "same source ⇒ no work" — is exact,
//!   while the un-comparable IR never has to be compared.
//!
//! `Symbols` (needed mutably by parse/lower) is threaded *inside* each query and stashed in
//! the `Arc` bundle so the next stage can reuse it, never crossing a salsa boundary as a
//! bare value.

use std::sync::Arc;

use rv_core::Symbols;
use rv_infer::Elaborated;
use rv_ir::{Parsed, Program};

// ---------------------------------------------------------------------------
// Database
// ---------------------------------------------------------------------------

/// The salsa database: owns the memoization storage for every query and input.
///
/// `Default` builds an empty database; `Clone` snapshots it (salsa storage is
/// reference-counted internally). The optional event hook installed by
/// [`Database::with_logger`] lets tests observe which tracked functions actually
/// *execute* (vs. are served from cache).
#[salsa::db]
#[derive(Clone)]
pub struct Database {
    storage: salsa::Storage<Self>,
}

impl Default for Database {
    fn default() -> Self {
        Self { storage: salsa::Storage::new(None) }
    }
}

#[salsa::db]
impl salsa::Database for Database {}

impl Database {
    /// Build a database that records the name of every tracked function salsa
    /// *executes* (a `WillExecute` event) into `log`. Used by the incrementality
    /// test to prove that a re-run with unchanged input does no work.
    pub fn with_logger(log: Arc<std::sync::Mutex<Vec<String>>>) -> Self {
        let storage = salsa::Storage::new(Some(Box::new(move |event| {
            if let salsa::EventKind::WillExecute { .. } = event.kind {
                log.lock().unwrap().push(format!("{:?}", event.kind));
            }
        })));
        Self { storage }
    }
}

// ---------------------------------------------------------------------------
// Input
// ---------------------------------------------------------------------------

/// The single salsa **input**: the program's source text. Mutating it (via the
/// generated `set_text` setter) is what drives incremental recomputation.
#[salsa::input]
pub struct SourceProgram {
    #[returns(ref)]
    pub text: String,
}

// ---------------------------------------------------------------------------
// Front-end summary  (salsa-friendly; the `parse_and_lower` output)
// ---------------------------------------------------------------------------

/// A salsa-friendly summary of a successful parse+lower: the lowered function
/// names. `Program<Parsed>` is *not* `Clone`/`Eq` and `rv_infer::elaborate`
/// consumes it *by value*, so the un-cloneable IR cannot be moved across a query
/// edge and cached. We therefore make [`parse_and_lower`] return this lightweight,
/// fully `Clone + Eq` summary; it still reads `SourceProgram::text` and so is a
/// genuine memoized dependency, and downstream queries reuse its cached
/// validation (and short-circuit on its `Err`) before re-deriving owned IR.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Frontend {
    /// Names of the functions the program lowered to (a cheap fingerprint).
    pub functions: Vec<String>,
}

/// `IR<Lowerable>` + obligations (the elaboration result) plus its `Symbols`,
/// behind an `Arc`. Produced (owned) by [`elaborate`] and consumed by [`analyze`]
/// for borrow-checking, discharge, and (in the driver) codegen+run. The `Arc`
/// lets it move across the `elaborate → analyze` edge without cloning the IR.
#[derive(Clone)]
pub struct ElaboratedProgram(pub Arc<ElaboratedInner>);
pub struct ElaboratedInner {
    pub elaborated: Elaborated,
    pub syms: Symbols,
}

// SAFETY: `maybe_update` may conservatively report "changed". This bundle wraps
// IR we cannot compare for equality, so we always report `true`. Consequence:
// `analyze` is re-validated whenever `elaborate` re-executed — never stale.
// Salsa still won't run `elaborate` at all if `SourceProgram::text` is unchanged,
// so "same source ⇒ no recompute" is unaffected; only redundant work is possible,
// and only after a real source change.
unsafe impl salsa::Update for ElaboratedProgram {
    unsafe fn maybe_update(old: *mut Self, new: Self) -> bool {
        unsafe { *old = new };
        true
    }
}

// Salsa also uses `PartialEq` on a tracked return value to *backdate* (skip
// downstream work when a recomputed output equals the previous one). We cannot
// compare the wrapped IR, so we report "never equal": this only forfeits the
// backdating optimization across a real source change, never memoization of an
// unchanged input. `Eq` is the same conservative relation.
impl PartialEq for ElaboratedProgram {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}
impl Eq for ElaboratedProgram {}

// ---------------------------------------------------------------------------
// The salsa-friendly result summary
// ---------------------------------------------------------------------------

/// One discharged obligation, summarized to a salsa-friendly shape.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ObligationOutcome {
    pub origin: String,
    pub ok: bool,
}

/// Either the analysis summary, or a front-end (parse/lower/type) error.
///
/// This is the value the top query [`analyze`] memoizes. It is fully
/// `Clone + PartialEq + Eq + Debug`, so salsa can cache, compare, and backdate it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AnalysisResult {
    /// Front-end failure (parse / lower / type error). Mirrors `rv-driver`'s `Err`.
    FrontendError(String),
    /// The program is well-formed; here is its verification verdict.
    Analyzed(Analysis),
}

/// The verification verdict for a well-formed program.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Analysis {
    /// (origin, ok) for every verification obligation, in order.
    pub obligations: Vec<ObligationOutcome>,
    /// Borrow/ownership violation strings (empty = clean).
    pub borrow_errors: Vec<String>,
    /// Did every obligation discharge AND the borrow checker pass?
    pub all_verified: bool,
}

// ---------------------------------------------------------------------------
// Tracked queries
// ---------------------------------------------------------------------------

/// Parse + lower the source into owned `IR<Parsed>` and its `Symbols`. Shared by
/// the [`parse_and_lower`] query (which summarizes it) and [`elaborate`] (which
/// consumes it). Not a query itself — the IR it produces is not salsa-friendly.
fn do_parse_and_lower(text: &str) -> Result<(Program<Parsed>, Symbols), String> {
    let mut syms = Symbols::new();
    let module = rv_syntax::parse(text, &mut syms)?;
    let prog = rv_lower::lower(&module, &mut syms)?;
    Ok((prog, syms))
}

/// **Query 1.** parse → lower. Reads `SourceProgram::text`; memoizes a
/// salsa-friendly [`Frontend`] summary (the lowered function names). Returns
/// `Err(String)` for a front-end parse/lower error. The un-cloneable
/// `IR<Parsed>` itself is *not* cached (it can't cross a query edge); [`elaborate`]
/// re-derives it on demand. This query exists so the front end is a first-class
/// memoized stage and so callers can validate parsing in isolation.
#[salsa::tracked]
pub fn parse_and_lower(db: &dyn salsa::Database, src: SourceProgram) -> Result<Frontend, String> {
    let (prog, syms) = do_parse_and_lower(src.text(db))?;
    let functions = prog.funcs.iter().map(|f| syms.resolve(f.name).to_string()).collect();
    Ok(Frontend { functions })
}

/// **Query 2.** elaborate. Depends on [`parse_and_lower`] (to reuse its memoized
/// validation and short-circuit on parse/lower errors), then produces the owned
/// `IR<Lowerable>` + obligations bundle that it memoizes behind an `Arc`. `Err`
/// for a static type error.
#[salsa::tracked]
pub fn elaborate(db: &dyn salsa::Database, src: SourceProgram) -> Result<ElaboratedProgram, String> {
    // Reuse the memoized front-end result: surfaces parse/lower errors and makes
    // `elaborate` a genuine dependent of `parse_and_lower` in the query graph.
    parse_and_lower(db, src)?;
    // `rv_infer::elaborate` consumes `Program<Parsed>` by value and the IR isn't
    // `Clone`, so we obtain a fresh owned copy here rather than across a query edge.
    let (prog, syms) = do_parse_and_lower(src.text(db))?;
    let elaborated = rv_infer::elaborate(prog, &syms)?;
    Ok(ElaboratedProgram(Arc::new(ElaboratedInner { elaborated, syms })))
}

/// **Query 3 (top).** borrow-check + discharge every obligation. Depends on
/// [`elaborate`]; memoizes the salsa-friendly [`AnalysisResult`]. This is the
/// query the driver and `compile_source` invoke.
#[salsa::tracked]
pub fn analyze(db: &dyn salsa::Database, src: SourceProgram) -> AnalysisResult {
    let elaborated = match elaborate(db, src) {
        Ok(e) => e,
        Err(e) => return AnalysisResult::FrontendError(e),
    };
    let ElaboratedInner { elaborated, syms } = &*elaborated.0;

    // Borrow / ownership check over the typed program.
    let borrow_errors = rv_borrowck::check(&elaborated.prog, syms)
        .into_iter()
        .map(|e| format!("{}: {}", e.func, e.message))
        .collect::<Vec<_>>();

    // Discharge each obligation with the built-in solvers.
    let registry = rv_solve::default_registry();
    let obligations: Vec<ObligationOutcome> = elaborated
        .obligations
        .iter()
        .map(|ob| ObligationOutcome {
            origin: ob.origin.clone(),
            ok: registry.discharge(ob).is_discharged(),
        })
        .collect();

    let all_verified = borrow_errors.is_empty() && obligations.iter().all(|o| o.ok);
    AnalysisResult::Analyzed(Analysis { obligations, borrow_errors, all_verified })
}

// ---------------------------------------------------------------------------
// Convenience entry points (callers need not know salsa exists)
// ---------------------------------------------------------------------------

/// Analyze one source string end-to-end: build a fresh [`Database`], set the
/// [`SourceProgram`] input, and run the [`analyze`] query. Returns the
/// salsa-memoized [`AnalysisResult`].
pub fn compile_source(text: &str) -> AnalysisResult {
    let db = Database::default();
    let src = SourceProgram::new(&db, text.to_string());
    analyze(&db, src)
}

/// Like [`compile_source`], but if the program verifies clean (all solver
/// obligations discharged and no borrow errors) and `entry` is `Some`, also
/// compile to bytecode and run that entry point.
///
/// Codegen + execution intentionally live *outside* the memoized query graph: a
/// VM `Value`/runtime error isn't salsa-friendly, and running is a side-effecting
/// leaf the driver wants on demand. We reuse the memoized [`elaborate`] result so
/// no front-end work is repeated.
pub fn compile_and_run(text: &str, entry: Option<&str>) -> (AnalysisResult, Option<Result<rv_vm::Value, String>>) {
    let db = Database::default();
    let src = SourceProgram::new(&db, text.to_string());
    let analysis = analyze(&db, src);

    let run = match (entry, &analysis) {
        // Execution is a continuation of successful checking, not a separate
        // escape hatch.  In particular, an unresolved safety obligation must
        // prevent bytecode from being emitted and run.
        (Some(e), AnalysisResult::Analyzed(a)) if a.all_verified => {
            // Reuse the memoized elaboration (no re-parse/-lower/-elaborate).
            let elaborated = elaborate(&db, src).expect("analyze already proved front-end ok");
            let ElaboratedInner { elaborated, syms } = &*elaborated.0;
            let bytecode = rv_codegen::compile(&elaborated.prog, syms);
            Some(rv_vm::run(&bytecode, e, &[]))
        }
        _ => None,
    };
    (analysis, run)
}

#[cfg(test)]
mod tests;
