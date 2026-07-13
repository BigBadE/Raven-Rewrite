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

// Untrusted schema-installer methods (`install_quot`/`install_trunc`/`install_funext`/
// `check_usage`/`declare_inductive`/...) on `rv_kernel::Kernel` come from this
// extension trait now that the trusted core lives in `rv-kernel-core`; see
// `rv_kernel::kernel_ext` for why.
use rv_kernel::KernelExt as _;

pub mod unify;
mod erased_vm;

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
#[derive(Debug, Default)]
pub struct Report {
    pub obligations: Vec<ObligationResult>,
    /// Borrow/ownership violations (use-after-move, borrow conflicts). Empty = clean.
    pub borrow_errors: Vec<String>,
    /// Proof-fragment `fn`s whose dependent-kernel obligation discharged.
    pub proof_verified: Vec<String>,
    /// Proof-fragment `fn`s whose obligation is still open (failed to verify).
    pub proof_open: Vec<String>,
    /// `Some` if an executable entry point was requested: the value it returned, or a
    /// runtime error (the VM path).
    pub run: Option<Result<Value, String>>,
    /// `Some` if a *proof-fragment* entry point was evaluated through the kernel: its
    /// rendered value, or an eval error. (Stage D will fold this into [`Report::run`].)
    pub proof_run: Option<Result<String, String>>,
    /// Proof-fragment declarations that erase to nothing (grade-0 ghosts: proofs).
    pub proofs_erased: Vec<String>,
    /// Proof-fragment declarations that survive QTT erasure as runtime code.
    pub runtime_defs: Vec<String>,
}
impl Report {
    /// Did every obligation discharge — executable (`rv-solve`) *and* proof (kernel) —
    /// AND the borrow checker pass?
    pub fn all_verified(&self) -> bool {
        self.borrow_errors.is_empty()
            && self.obligations.iter().all(ObligationResult::ok)
            && self.proof_open.is_empty()
    }
    pub fn num_failed(&self) -> usize {
        self.obligations.iter().filter(|o| !o.ok()).count()
            + self.borrow_errors.len()
            + self.proof_open.len()
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

    Ok(Report { obligations, borrow_errors: analysis.borrow_errors, run, ..Default::default() })
}

/// Convenience: verify only (no execution).
pub fn verify(src: &str) -> Result<Report, String> {
    run_pipeline(src, None)
}

// ---------------------------------------------------------------------------
// The unified path: one `.rv` file, both backends, one merged report.
// ---------------------------------------------------------------------------

/// Analyze a `.rv` program through **both** backends in one call, merged into a single
/// [`Report`]. The file is classified per-item ([`rv_syntax::classify`]): the executable
/// fragment flows through the salsa pipeline + `rv-solve` (and runs on the VM), while the
/// proof fragment is checked by the dependent kernel. A file verifies iff *every*
/// obligation — decidable and dependent — discharges and the borrow checker passes.
///
/// `entry`, if given, is executed once on whichever backend owns it: an executable entry
/// runs on the VM ([`Report::run`]); a proof-fragment entry is evaluated by the kernel
/// ([`Report::proof_run`]).
pub fn analyze_unified(src: &str, entry: Option<&str>) -> Result<Report, String> {
    use rv_syntax::Fragment;

    // Parse once to classify items and to locate the entry point's fragment.
    let mut syms = rv_core::Symbols::new();
    let module = rv_syntax::parse(src, &mut syms)?;
    let frags = rv_syntax::classify(&module);
    let has_proof = frags.iter().any(|f| matches!(f, Fragment::Proof));
    let entry_frag = entry.and_then(|name| entry_fragment(&module, &frags, &syms, name));

    // Executable backend: the salsa pipeline over the executable fragment (rv-lower
    // already skips proof items). Run the entry only if it is an executable `fn`.
    let exec_entry = matches!(entry_frag, Some(Fragment::Exec) | Some(Fragment::Shared))
        .then_some(entry)
        .flatten();
    let (analysis, run) = rv_db::compile_and_run(src, exec_entry);
    let analysis = match analysis {
        rv_db::AnalysisResult::Analyzed(a) => a,
        rv_db::AnalysisResult::FrontendError(e) => return Err(e),
    };
    let obligations = analysis
        .obligations
        .into_iter()
        .map(|o| ObligationResult { origin: o.origin, discharged: o.ok })
        .collect();

    // Proof backend: only spin up the kernel when there is a proof fragment to check.
    let mut run = run;
    let (proof_verified, proof_open, proof_run, proofs_erased, runtime_defs) = if has_proof {
        let kernel_entry =
            matches!(entry_frag, Some(Fragment::Proof)).then_some(entry).flatten();
        let rep = verify_rv(src, kernel_entry)?;
        // Stage D — a proof-fragment entry yields a real `rv_vm::Value` through the SAME
        // `run` channel as the executable backend (one value model). The rendered string
        // stays available in `proof_run` for display / non-data results.
        if kernel_entry.is_some() {
            if let Some(Ok(v)) = &rep.run_value {
                run = Some(Ok(v.clone()));
            }
        }
        // `verify_rv` returning `Ok` means every proof declaration *type-checked* (a bad
        // proof is a hard error). Surface those declarations as verified — they would not
        // otherwise appear, since the kernel's goal list tracks only `requires`/`ensures`
        // obligations, not proof-as-type theorems. Anything still open stays open.
        let open: std::collections::HashSet<&str> = rep.open.iter().map(String::as_str).collect();
        let mut verified = rep.verified.clone();
        for name in proof_decl_names(&module, &frags, &syms) {
            if !open.contains(name.as_str()) && !verified.contains(&name) {
                verified.push(name);
            }
        }
        // If the entry produced a VM value (now in `run`), drop the rendered duplicate;
        // keep `proof_run` only as a fallback for non-data results.
        let proof_run = if matches!(run, Some(Ok(_))) { None } else { rep.run };
        (verified, rep.open, proof_run, rep.proofs_erased, rep.runtime_defs)
    } else {
        (Vec::new(), Vec::new(), None, Vec::new(), Vec::new())
    };

    Ok(Report {
        obligations,
        borrow_errors: analysis.borrow_errors,
        proof_verified,
        proof_open,
        run,
        proof_run,
        proofs_erased,
        runtime_defs,
    })
}

/// The names of the proof-fragment declarations (`fn`/`def`/`instance`) the kernel checks.
fn proof_decl_names(
    module: &rv_syntax::ast::Module,
    frags: &[rv_syntax::Fragment],
    syms: &rv_core::Symbols,
) -> Vec<String> {
    use rv_syntax::ast::Item;
    module
        .items
        .iter()
        .zip(frags)
        .filter(|(_, f)| f.is_proof())
        .filter_map(|(item, _)| match item {
            Item::Fn(f) => Some(syms.resolve(f.name).to_string()),
            Item::Def(d) | Item::Instance(d) => Some(syms.resolve(d.name).to_string()),
            _ => None,
        })
        .collect()
}

/// Check the **QTT usage discipline** ([`rv_kernel::Kernel::check_usage`]) of every
/// proof-fragment declaration in `src` against `session`'s now-elaborated environment. A
/// graded binder (`fun (x :1 T) => …`, `forall (x :0 T), …` — see `rv-syntax`'s
/// `Parser::parse_binder_grade`) used off its declared discipline (linear used twice or
/// never, erased used relevantly) is rejected here with a clear message. Ungraded (`ω`,
/// the default) code is untouched — `check_usage` always passes it — so this never
/// rejects a proof that doesn't opt into grades.
fn check_graded_usage(session: &rv_kernel::verify::Session, src: &str) -> Result<(), String> {
    let mut syms = rv_core::Symbols::new();
    let Ok(module) = rv_syntax::parse(src, &mut syms) else { return Ok(()) };
    let frags = rv_syntax::classify(&module);
    for name in proof_decl_names(&module, &frags, &syms) {
        session.k.check_usage(&name)?;
    }
    Ok(())
}

/// Find the [`Fragment`](rv_syntax::Fragment) of the top-level `fn` named `name`, if any.
fn entry_fragment(
    module: &rv_syntax::ast::Module,
    frags: &[rv_syntax::Fragment],
    syms: &rv_core::Symbols,
    name: &str,
) -> Option<rv_syntax::Fragment> {
    use rv_syntax::ast::Item;
    module.items.iter().zip(frags).find_map(|(item, frag)| match item {
        Item::Fn(f) if syms.resolve(f.name) == name => Some(*frag),
        // `def`/`instance` are always proof-fragment; a matching name is a kernel entry.
        Item::Def(d) | Item::Instance(d) if syms.resolve(d.name) == name => Some(*frag),
        _ => None,
    })
}

// ---------------------------------------------------------------------------
// The verified-Raven path: the dependent-type-theory kernel + its surface.
// ---------------------------------------------------------------------------

/// The result of verifying (and optionally running) a Raven *kernel-surface* program:
/// which `fn`s had their correctness obligations discharged, which remain open, and the
/// rendered value of an evaluated entry point.
#[derive(Debug, Default)]
pub struct RavenReport {
    pub verified: Vec<String>,
    pub open: Vec<String>,
    /// `Some` if an entry point was evaluated: its rendered value, or an eval error.
    pub run: Option<Result<String, String>>,
    /// Proof-fragment declarations that erase to **nothing** (grade-0 ghosts: proofs and
    /// proof-returning functions). These cost zero bytes at runtime — the QTT erasure that
    /// justifies checking them in the kernel and running only the rest.
    pub proofs_erased: Vec<String>,
    /// Proof-fragment declarations that survive erasure as runtime code (the shared
    /// computational core the kernel reasons about *and* can run).
    pub runtime_defs: Vec<String>,
    /// `Some` if an entry point was evaluated *and* its normal form is first-order data:
    /// the same [`Value`] shape the VM produces, so both backends share one value model
    /// (Stage D). `None`/`Err` for higher-order or non-data results (still in [`run`]).
    pub run_value: Option<Result<Value, String>>,
}
impl RavenReport {
    /// Every declared `fn` obligation discharged?
    pub fn all_verified(&self) -> bool {
        self.open.is_empty()
    }
}


/// Build and run a `Session` (kernel + prelude + `src`) exactly the way [`verify_rv`] does,
/// but return the live session instead of a summary report. Exists for tooling/tests that
/// need to inspect the resulting environment after verification — e.g. the kernel's
/// independent re-check harness ([`rv_kernel::recheck_all_definitions`]), which re-verifies
/// every stored definition from scratch, ignoring how `Session` produced it.
pub fn verify_rv_session(src: &str) -> Result<rv_kernel::verify::Session, String> {
    let mut session = rv_kernel::verify::Session::new();
    rv_kernel::logic::declare_logic(&mut session.k)?;
    session.k.install_quot()?;
    session.k.install_trunc()?;
    session.k.install_funext()?;
    session.k.install_interval_hit()?;
    session.k.install_cubical()?;
    session.k.install_s1c()?;
    session.k.install_s2()?;
    session.k.install_torus()?;
    session.k.install_s3()?;
    session.k.install_set_quotient()?;
    session.k.install_equiv()?;
    session.k.install_contr()?;
    session.k.install_hae()?;
    session.k.install_ua()?;
    session.k.install_fiber2()?;
    session.k.install_equiv_algebra()?;
    session.k.declare_coinductive(rv_kernel::coinductive::stream_spec())?;
    run_unified(&mut session, RAVEN_PRELUDE).map_err(|e| format!("in the standard prelude: {e}"))?;
    run_unified(&mut session, src)?;
    check_graded_usage(&session, src)?;
    Ok(session)
}

/// Verify a Raven `.rv` program through the dependent kernel, loading only the **logic**
/// prelude (`Eq`, `And`/`Or`/`False`, `Not`/`Iff`) — *not* the full stdlib — so a `.rv` file
/// is self-contained and brings its own data types (`enum`s) and proofs. This is the unified
/// `.rv` surface's proof/verification path; obligations are discharged by the kernel.
pub fn verify_rv(src: &str, entry: Option<&str>) -> Result<RavenReport, String> {
    // The proof path now runs entirely through the **single** `rv-syntax` parser: the
    // prelude and the program are parsed by one lexer+parser and translated to kernel
    // Commands (see `unify`). The kernel re-checks every term.
    let session = verify_rv_session(src)?;

    // Grade-driven split (QTT erasure): partition the proof-fragment definitions into the
    // proofs that erase to nothing and the computational definitions that survive as
    // runtime code. `erase_def` also *checks* the grade discipline — a ghost leaking into a
    // runtime position is an error here, never a silently-kept term.
    let mut proofs_erased = Vec::new();
    let mut runtime_defs = Vec::new();
    {
        let mut syms = rv_core::Symbols::new();
        if let Ok(module) = rv_syntax::parse(src, &mut syms) {
            let frags = rv_syntax::classify(&module);
            for name in proof_decl_names(&module, &frags, &syms) {
                match rv_kernel::erase::erase_def(session.k.env(), &name) {
                    Ok(rv_kernel::erase::Erased::Opaque) => proofs_erased.push(name),
                    Ok(_) => runtime_defs.push(name),
                    // Not a stored definition (e.g. a `requires`/`ensures` `fn`, tracked as
                    // a goal instead) — already covered by `verified`/`open`.
                    Err(_) => {}
                }
            }
        }
    }

    let run = entry.map(|e| session.run_entry(e));
    // Stage D — execute a runtime entry on the **bytecode VM**: erase it, compile to
    // `rv-codegen` bytecode, and run on `rv-vm` — the same engine as the executable
    // fragment. If the entry uses a construct the erased-term compiler does not yet lower
    // (mutual/indexed recursors, …), fall back to evaluating it with the kernel's trusted
    // reducer and bridging the normal form to a `Value`. Either way the result is one
    // `rv_vm::Value` model, shared with the executable backend.
    let run_value = entry.map(|e| {
        erased_vm::run_entry_on_vm(session.k.env(), e)
            .or_else(|_| session.eval(e).and_then(|t| term_to_value(session.k.env(), &t)))
    });
    Ok(RavenReport {
        verified: session.verified_fns(),
        open: session.open_fns(),
        run,
        proofs_erased,
        runtime_defs,
        run_value,
    })
}

/// Verify `src` through the kernel, then compile-and-run the proof-fragment entry `entry`
/// on the **bytecode VM only** (no NbE fallback). Returns the VM value, or an error if the
/// entry uses a construct the erased-term→bytecode compiler does not yet lower. Used to test
/// the native execution path in isolation.
pub fn vm_eval(src: &str, entry: &str) -> Result<Value, String> {
    let mut session = rv_kernel::verify::Session::new();
    rv_kernel::logic::declare_logic(&mut session.k)?;
    session.k.install_quot()?;
    session.k.install_trunc()?;
    session.k.install_funext()?;
    session.k.install_interval_hit()?;
    session.k.install_cubical()?;
    session.k.install_s1c()?;
    session.k.install_s2()?;
    session.k.install_torus()?;
    session.k.install_s3()?;
    session.k.install_set_quotient()?;
    session.k.install_equiv()?;
    session.k.install_contr()?;
    session.k.install_hae()?;
    session.k.install_ua()?;
    session.k.install_fiber2()?;
    session.k.install_equiv_algebra()?;
    session.k.declare_coinductive(rv_kernel::coinductive::stream_spec())?;
    run_unified(&mut session, RAVEN_PRELUDE).map_err(|e| format!("in the standard prelude: {e}"))?;
    run_unified(&mut session, src)?;
    erased_vm::run_entry_on_vm(session.k.env(), entry)
}

/// Verify `src`, then evaluate the proof-fragment entry `entry` with the **kernel's trusted
/// reducer** (NbE) and bridge its normal form to a [`Value`]. The reference semantics that
/// [`vm_eval`]'s native bytecode execution must agree with.
pub fn nbe_eval(src: &str, entry: &str) -> Result<Value, String> {
    let mut session = rv_kernel::verify::Session::new();
    rv_kernel::logic::declare_logic(&mut session.k)?;
    session.k.install_quot()?;
    session.k.install_trunc()?;
    session.k.install_funext()?;
    session.k.install_interval_hit()?;
    session.k.install_cubical()?;
    session.k.install_s1c()?;
    session.k.install_s2()?;
    session.k.install_torus()?;
    session.k.install_s3()?;
    session.k.install_set_quotient()?;
    session.k.install_equiv()?;
    session.k.install_contr()?;
    session.k.install_hae()?;
    session.k.install_ua()?;
    session.k.install_fiber2()?;
    session.k.install_equiv_algebra()?;
    session.k.declare_coinductive(rv_kernel::coinductive::stream_spec())?;
    run_unified(&mut session, RAVEN_PRELUDE).map_err(|e| format!("in the standard prelude: {e}"))?;
    run_unified(&mut session, src)?;
    let t = session.eval(entry)?;
    term_to_value(session.k.env(), &t)
}

/// Convert a kernel normal-form [`Term`](rv_kernel::Term) — a constructor tree — into the
/// `rv_vm::Value` the VM uses for the same data. Errors if the result is not first-order
/// data (a function, a type, an open term). `Nat` literals become `Adt` like any other
/// inductive; the tag is the constructor's declaration index, matching codegen.
fn term_to_value(env: &rv_kernel::Env, t: &rv_kernel::Term) -> Result<Value, String> {
    let (head, args) = t.unfold_apps();
    match &head {
        rv_kernel::Term::Const(name, _) => match env.get(name) {
            Some(rv_kernel::Decl::Constructor(c)) => {
                // A constructor application is `Ctor params… fields…`; only the trailing
                // `num_fields` arguments are runtime data (the params are erased types).
                let fields = args
                    .iter()
                    .skip(args.len().saturating_sub(c.num_fields))
                    .map(|a| term_to_value(env, a))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Value::Adt { tag: c.index as u32, fields })
            }
            _ => Err(format!("entry result is not first-order data: `{name}`")),
        },
        _ => Err("entry result is not first-order data (a function or open term)".to_string()),
    }
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

#[cfg(test)]
mod i128_tests {
    //! End-to-end coverage for 128-bit integer literal/arithmetic support: a
    //! literal beyond `i64::MAX` magnitude round-trips through the whole
    //! pipeline (parse -> lower -> infer/verify -> compile -> run), in-range
    //! `i128`/`u128` wrapping arithmetic verifies AND runs to the right value,
    //! a genuine overflow at a sub-128 width still fails its obligation, and
    //! `u128`'s bit-pattern representation for magnitudes above `i128::MAX` is
    //! correct.
    use super::run_pipeline;

    /// A literal whose magnitude exceeds `i64::MAX` (`i128::MAX` itself) both
    /// verifies and runs to its exact value — this was impossible before the
    /// `Term::Int`/`Const::Int`/`Value::Int` carrier was widened to `i128`.
    #[test]
    fn i128_max_literal_round_trips_and_runs() {
        let src = "fn main() -> i128 { let big: i128 = 170141183460469231731687303715884105727; return big; }";
        let report = run_pipeline(src, Some("main")).expect("front end should accept");
        assert!(report.all_verified(), "expected all obligations to discharge: {report:?}");
        assert_eq!(
            report.run.expect("entry should run"),
            Ok(super::Value::Int(i128::MAX))
        );
    }

    /// `wrapping_sub` on `i128`-typed operands near `i128::MAX` verifies (the
    /// wrapping intrinsic opts out of the checked-overflow obligation) and runs
    /// to the exact `i128` result on the VM's native `i128` word.
    #[test]
    fn i128_wrapping_arithmetic_verifies_and_runs() {
        let src = "fn main() -> i128 { \
            let big: i128 = 170141183460469231731687303715884105727; \
            let one: i128 = 1; \
            return wrapping_sub(big, one); \
        }";
        let report = run_pipeline(src, Some("main")).expect("front end should accept");
        assert!(report.all_verified(), "expected all obligations to discharge: {report:?}");
        assert_eq!(
            report.run.expect("entry should run"),
            Ok(super::Value::Int(i128::MAX - 1))
        );
    }

    /// `u128` literals above `i64::MAX` (but well below `i128::MAX`) verify and
    /// run correctly, confirming full-magnitude `u128` values compose from the
    /// widened literal carrier without truncation.
    #[test]
    fn u128_wide_literal_verifies_and_runs() {
        let src = "fn main() -> u128 { \
            let big: u128 = 300000000000000000000; \
            let small: u128 = 5; \
            return wrapping_add(big, small); \
        }";
        let report = run_pipeline(src, Some("main")).expect("front end should accept");
        assert!(report.all_verified(), "expected all obligations to discharge: {report:?}");
        assert_eq!(
            report.run.expect("entry should run"),
            Ok(super::Value::Int(300000000000000000005))
        );
    }

    /// A genuine `u64` overflow, using literals whose magnitude exceeds
    /// `i64::MAX` (only expressible after the widened literal carrier), still
    /// fails its overflow obligation — the widening does not weaken existing
    /// overflow checking for sub-128 widths.
    #[test]
    fn u64_checked_overflow_with_wide_literals_still_fails() {
        let src = "fn main() -> u64 { \
            let a: u64 = 18000000000000000000; \
            let b: u64 = 1000000000000000000; \
            return a + b; \
        }";
        let report = run_pipeline(src, Some("main")).expect("front end should accept");
        assert!(!report.all_verified(), "a genuine u64 overflow must not verify: {report:?}");
    }

    /// `u128`'s upper half (magnitudes above `i128::MAX`, up to `u128::MAX`) is
    /// the one documented boundary of this widening: the lexer *parses* such a
    /// literal (as a `u128`, bit-reinterpreted into the `i128` `Term::Int`
    /// carrier — see `Tok::Int`'s doc comment), but the width's built-in range
    /// check compares that `Term` with signed `i128` semantics, so a magnitude
    /// above `i128::MAX` reads back as a *negative* `i128` and correctly (if
    /// unhelpfully) fails the `>= 0` obligation for a `u128` value — a sound
    /// rejection, not a crash or silent truncation. The supported `u128` range
    /// is therefore `0..=i128::MAX`; see `IntTy`'s doc comment in `rv-core`.
    #[test]
    fn u128_upper_half_is_soundly_rejected_not_silently_wrong() {
        let src = "fn main() -> u128 { \
            let near_max: u128 = 340282366920938463463374607431768211454; \
            return near_max; \
        }";
        let report = run_pipeline(src, Some("main")).expect("front end should accept");
        assert!(
            !report.all_verified(),
            "a u128 literal above i128::MAX must fail its range obligation, not verify: {report:?}"
        );
    }
}
