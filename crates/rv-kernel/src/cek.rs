//! **Tier 4 — a CEK abstract machine with resumable algebraic effect handlers.**
//!
//! Where [`crate::stlc`] evaluates by *searching* a term for the next redex (a
//! substitution-based small-step `step : Exp → OExp`), this module evaluates with an
//! **explicit control stack** and an **environment** — an abstract machine. A CEK machine
//! is a transition system over states
//!
//! ```text
//!   ⟨ C , E , K ⟩
//! ```
//!
//! the **C**ontrol (the term in focus), the **E**nvironment (the values of the de Bruijn
//! variables in scope), and the **K**ontinuation (a *defunctionalised* stack recording
//! "what to do with the value once C is done"). Functions are **closures** — a body paired
//! with the environment it captured — so there is **no substitution at all**. Each
//! transition is `O(1)`.
//!
//! ## Effects: handlers with first-class resumptions
//!
//! `handle body h` runs `body` under the handler `h : payload → resume → result`. When
//! `body` performs `op v`, the machine walks the continuation to the nearest handler and
//! calls `h` with the payload `v` **and a resumption** — the continuation captured at the
//! `op`, reified as a value `Val.vkont`. The handler may **resume** (apply the resumption
//! to a value, continuing the suspended computation — `λp. λk. k p` makes `op` behave like
//! a value-returning call) or **abort** (ignore the resumption, replacing the whole handled
//! expression — `λp. λk. p`). Resuming re-installs the handler, i.e. **deep** handlers.
//! This is full algebraic effects, not just exceptions.
//!
//! Reifying the resumption forces `Val`, `Env` and `Kont` into one **mutual** inductive
//! group (a value may be a continuation; a continuation frame may hold a value). Matching on
//! members of such a group — and the handler-search written as a *mutual function bundle*
//! over the group — is exactly what `elab2::compile_match_mutual` and the bundle compiler
//! make possible.
//!
//! Everything is verified Raven, kernel-checked, and **executable**: the tests run real
//! programs through the machine and read the resulting number back out.
//!
//!  * **Machine** — `Tm`, the mutually-inductive `Val`/`Env`/`Kont`, the `State`, the
//!    single transition `step`, and the fuelled driver `run`.
//!  * **Metatheory** ([`META`]) — the driver's fixed-point theorems.

use crate::verify::Session;

/// Logic, booleans, naturals (with addition), and the focused term language `Tm`.
pub const PRELUDE: &str = include_str!("raven/cek_prelude.rvk");

/// The machine: closures + environments + reified continuations, the state, the transition.
pub const MACHINE: &str = include_str!("raven/cek_machine.rvk");

/// **The machine-checked metatheory of the driver.** `step` is a *total function*, so
/// determinism is free; the content here is that the driver halts correctly:
///
///  * `step_final` — a **final** state (`sdone`/`sstuck`) is a fixed point of `step`.
///  * `run_final_fix` — starting from a final state, `run` returns it unchanged for **any**
///    fuel: once the machine answers, more steps never change the answer.
pub const META: &str = include_str!("raven/cek_meta.rvk");

/// The base session: the prelude + the machine, kernel-checked and ready to *run*.
pub fn session() -> Result<Session, String> {
    let mut s = Session::new();
    s.run(PRELUDE)?;
    s.run(MACHINE)?;
    Ok(s)
}

/// The machine session plus the [`META`] driver metatheory (the fixed-point theorems).
pub fn meta_session() -> Result<Session, String> {
    let mut s = session()?;
    s.run(META)?;
    Ok(s)
}

/// **Machine type-safety for the pure fragment.** A simple type system for `Tm`
/// (`var`/`lit`/`lam`/`app`/`add`/`ifz` — `op`/`handle` are deliberately left *untypable*,
/// so a well-typed program never performs an effect), lifted to the machine's runtime
/// objects: value typing `HasTyV` and environment typing `HasTyE` (mutual), continuation
/// typing `HasTyK k A B` ("feeding an `A` into `k` yields a final answer of type `B`"), and
/// state typing `HasTyS`. The payoff theorem is **preservation** (`step` preserves the
/// answer type) — and because the stuck state `sstuck` has *no* typing rule, preservation
/// alone says **a well-typed state never gets stuck**.
pub const SAFETY: &str = include_str!("raven/cek_safety.rvk");

/// **Inversion infrastructure** for value typing. Because `HasTyV`/`HasTyE` share the
/// `HasTyVE` inductive through the `VE`/`TC` injections, a plain `match` on a value-typing
/// proof cannot refine the underlying value (its index is `injv v`, not `v`). So the
/// canonical-forms lemmas use the standard inversion-via-equalities trick — generalise the
/// indices, then recover the value with `injv`-injectivity and rule out the impossible
/// constructors with no-confusion. The results are packaged in `NatInv`/`ClosInv`, whose
/// indices are the value *directly*, so the preservation proof can `match` them cleanly.
pub const SAFETY_INV: &str = include_str!("raven/cek_safety_inv.rvk");

/// The machine session plus the [`SAFETY`] type system (relations only; the metatheory
/// proofs are layered on top in further sessions).
pub fn safety_session() -> Result<Session, String> {
    let mut s = session()?;
    s.run(SAFETY)?;
    Ok(s)
}

/// **Environment-typing inversion + the lookup lemma.** `envConsInv` inverts an environment
/// typed at a non-empty context into a typed head + typed tail (the same VE/TC equations
/// technique as the value canonical forms), with the supporting no-confusion / injectivity
/// facts for the `inje`/`injc` injections and the `Ctx` constructors. `envLookup` then proves
/// `HasTyE env G -> Lookup G n A -> HasTyV (lookupEnv n env) A` by induction on the lookup
/// derivation, using the **convoy pattern** to thread the (environment-abstracted) induction
/// hypothesis through the inner `econs`-inversion. This is the inversion + lookup the `var`
/// case of preservation is built from.
pub const SAFETY_LOOKUP: &str = include_str!("raven/cek_safety_lookup.rvk");

/// The safety session plus the [`SAFETY_INV`] inversion infrastructure (canonical forms).
pub fn inv_session() -> Result<Session, String> {
    let mut s = safety_session()?;
    s.run(SAFETY_INV)?;
    Ok(s)
}

/// The inversion session plus the [`SAFETY_LOOKUP`] environment-typing inversion.
pub fn lookup_session() -> Result<Session, String> {
    let mut s = inv_session()?;
    s.run(SAFETY_LOOKUP)?;
    Ok(s)
}

/// **Machine type-safety: preservation + progress + the run-level safety corollary.**
///
///  * `preservation : HasTyS s B -> HasTyS (step s) B` — one transition preserves the state's
///    answer type. Proved by case analysis on the *typing derivation* (not the term): for a
///    running state (`seval`) we recurse on `HasTy`, for a returning state (`sret`) on `HasTyK`
///    — each constructor refines the term/frame and hands over its premises directly, so no
///    separate term/frame inversion is needed. Where `step` branches on a value (the `kapp2`,
///    `kadd*`, `kifz` frames) the value canonical forms (`canonNat`/`canonArr`) refine it,
///    discharging the stuck branches; the `var` case is closed by `envLookup`. Index-dependent
///    hypotheses are threaded with the convoy pattern. There is *no* rule for the effect frames
///    or for `op`/`handle`, so those simply never occur as arms.
///  * `notStuck : HasTyS s B -> (s = sstuck -> False)` — the progress half: a well-typed state
///    is never the stuck state (`sstuck` has no typing rule; no-confusion on `State`).
///  * `runPreserv : HasTyS s B -> HasTyS (run n s) B` — typing is preserved across the whole
///    fuelled driver (induction on fuel; structural case on the state so `run`'s `isFinal`
///    guard reduces).
///  * `neverStuck : HasTyS s B -> (run n s = sstuck -> False)` — **type safety**: a well-typed
///    program, run for any fuel, never reaches the stuck state. Effects make this sharp:
///    `op`/`handle` are deliberately untypable, so a well-typed program is effect-free.
///  * `answerWellTyped : HasTyS s B -> (run n s = sdone v) -> HasTyV v B` — the positive
///    direction: when a well-typed program does halt with an answer, the answer has its type.
pub const SAFETY_PRESERV: &str = include_str!("raven/cek_safety_preserv.rvk");

/// The lookup session plus the [`SAFETY_PRESERV`] proofs: preservation, progress, and the
/// run-level type-safety corollary for the CEK machine.
pub fn preserv_session() -> Result<Session, String> {
    let mut s = lookup_session()?;
    s.run(SAFETY_PRESERV)?;
    Ok(s)
}

/// **Machine adequacy.** Type-safety says the machine never *goes wrong*; adequacy says it
/// computes the *right* answer — the value a declarative big-step semantics assigns. We give
/// an environment-style big-step relation `Eval env e v` (no rule for `op`/`handle`, matching
/// the typed fragment) and the reflexive-transitive closure `Steps` of `step`, then prove:
///
///  * `sim : Eval env e v -> (k : Kont) -> Steps (seval e env k) (sret v k)` — forward
///    simulation: whatever the big-step semantics evaluates `e` to, the machine drives
///    `seval e env k` to `sret v k`, feeding the value to the same continuation. Induction on
///    the evaluation derivation, with the result curried over the continuation `k` so each
///    sub-evaluation's IH applies under the frame the machine pushes; single transitions are
///    prepended with `sstep`, sub-runs joined with transitivity `strans`.
///  * `adequacy : Eval enil e v -> Steps (load e) (sdone v)` — for a closed term, the loaded
///    machine steps all the way to the final answer the semantics predicts.
pub const ADEQUACY: &str = include_str!("raven/cek_adequacy.rvk");

/// The machine session plus the [`ADEQUACY`] big-step semantics and forward-simulation proof.
pub fn adequacy_session() -> Result<Session, String> {
    let mut s = session()?;
    s.run(ADEQUACY)?;
    Ok(s)
}

/// **The verified pipeline — connecting the source island to the machine.** A small first-order
/// source language `Src` (variables, literals, addition, conditional, and a `let` binder) is
/// given a big-step semantics `EvalSrc` and a compiler `compile : Src -> Tm` into the CEK term
/// language. `let` is compiled the classic way, as an immediately-applied lambda (β-redex):
/// `let x = e1 in e2 ↦ (λ e2) e1`. We then prove:
///
///  * `compileCorrect : EvalSrc env e v -> Eval env (compile e) v` — compiler correctness: the
///    compiled term evaluates (in the CEK big-step relation) to the value the source assigns.
///    Induction on the source-evaluation derivation; the `let` case is exactly the `app`/`lam`
///    rule of the target semantics.
///  * `pipeline : EvalSrc enil e v -> Steps (load (compile e)) (sdone v)` — composing compiler
///    correctness with [`ADEQUACY`]: a closed source program that evaluates to `v` compiles to
///    a CEK term that the machine actually runs, from the loaded state, all the way to `sdone v`.
///
/// This is the end-to-end thread: **source semantics → compile → machine execution**, every
/// arrow kernel-checked.
pub const PIPELINE: &str = include_str!("raven/cek_pipeline.rvk");

/// The adequacy session plus the [`PIPELINE`]: the source language, its compiler into the CEK
/// machine, compiler correctness, and the end-to-end pipeline theorem.
pub fn pipeline_session() -> Result<Session, String> {
    let mut s = adequacy_session()?;
    s.run(PIPELINE)?;
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build `Nat.succ^n Nat.zero` for fuel/program literals.
    fn nat(n: usize) -> String {
        let mut s = String::from("Nat.zero");
        for _ in 0..n {
            s = format!("Nat.succ ({s})");
        }
        s
    }

    /// Load `prog`, run it with `fuel` steps, and read back the resulting number.
    fn eval(prog: &str, fuel: usize) -> String {
        let mut s = session().unwrap();
        s.run(&format!("def prog : Tm := {prog}")).unwrap();
        s.run(&format!("def fuel : Nat := {}", nat(fuel))).unwrap();
        s.run("def answer : Nat := evalNat fuel prog").unwrap();
        s.run_entry("answer").unwrap()
    }

    #[test]
    fn beta_and_addition() {
        // (λx. x + 1) 2  ==>  3  (β extends the environment; no substitution)
        let prog = "Tm.app (Tm.lam (Tm.add (Tm.var Nat.zero) (Tm.lit (Nat.succ Nat.zero)))) \
                    (Tm.lit (Nat.succ (Nat.succ Nat.zero)))";
        assert_eq!(eval(prog, 20), "3");
    }

    #[test]
    fn closure_captures_its_environment() {
        // (λx. (λy. x) 9) 5  ==>  5   — the inner closure must capture x from the outer env.
        let inner = format!(
            "Tm.app (Tm.lam (Tm.var (Nat.succ Nat.zero))) (Tm.lit ({}))",
            nat(9)
        );
        let prog = format!("Tm.app (Tm.lam ({inner})) (Tm.lit ({}))", nat(5));
        assert_eq!(eval(&prog, 30), "5");
    }

    #[test]
    fn machine_type_system_kernel_checks() {
        // The type system for the CEK machine (term typing + value/env typing via the VE/TC
        // encoding + continuation + state typing) is well-formed and kernel-checked.
        let s = safety_session().expect("machine type system should kernel-check");
        for n in ["HasTy", "HasTyVE", "HasTyV", "HasTyE", "HasTyK", "HasTyS"] {
            assert!(s.k.env().contains(n), "missing relation: {n}");
        }
    }

    #[test]
    fn canonical_forms_and_inversions_kernel_check() {
        // The value canonical forms (a well-typed `tnat` value is a `vnat`; a `tarr` value is
        // a closure with a well-typed env+body) and the environment-typing inversion are
        // verified — the inversion infrastructure the preservation proof is built from.
        let s = lookup_session().expect("inversion infrastructure should kernel-check");
        for n in ["canonNat", "canonArr", "envConsInv", "envLookup", "injv_inj", "ve_nc"] {
            assert!(s.k.env().contains(n), "missing lemma: {n}");
        }
    }

    #[test]
    fn type_safety_kernel_checks() {
        // Preservation, progress (notStuck), driver preservation, and the run-level safety
        // corollary (neverStuck) for the CEK machine are all verified by the kernel.
        let s = preserv_session().expect("CEK machine type-safety should kernel-check");
        for n in ["preservation", "notStuck", "runPreserv", "neverStuck", "answerWellTyped"] {
            assert!(s.k.env().contains(n), "missing safety theorem: {n}");
        }
    }

    #[test]
    fn adequacy_kernel_checks() {
        // The big-step semantics, the forward-simulation lemma, and the closed-term adequacy
        // corollary (the machine computes the value the declarative semantics assigns) are
        // verified by the kernel.
        let s = adequacy_session().expect("CEK adequacy should kernel-check");
        for n in ["Eval", "Steps", "strans", "sim", "adequacy"] {
            assert!(s.k.env().contains(n), "missing adequacy item: {n}");
        }
    }

    #[test]
    fn pipeline_kernel_checks() {
        // The source language, its compiler into the CEK machine, compiler correctness, and the
        // end-to-end pipeline theorem (source big-step ⟹ the machine runs the compiled code to
        // the answer) are verified by the kernel.
        let s = pipeline_session().expect("the verified pipeline should kernel-check");
        for n in ["Src", "EvalSrc", "compile", "compileCorrect", "pipeline"] {
            assert!(s.k.env().contains(n), "missing pipeline item: {n}");
        }
    }

    #[test]
    fn compiled_source_runs_on_the_machine() {
        // Operational end-to-end: compile `let x = 2 in x + 3` and actually run it on the CEK
        // machine, reading back 5. (Complements the `pipeline` proof with a concrete execution.)
        let mut s = pipeline_session().unwrap();
        s.run("def prog : Src := Src.slet (Src.slit (Nat.succ (Nat.succ Nat.zero))) \
                 (Src.sadd (Src.svar Nat.zero) (Src.slit (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))")
            .unwrap();
        s.run("def fuel : Nat := Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ \
                 (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))))")
            .unwrap();
        s.run("def answer : Nat := evalNat fuel (compile(prog))").unwrap();
        assert_eq!(s.run_entry("answer").unwrap(), "5");
    }

    #[test]
    fn driver_metatheory_kernel_checks() {
        // The fixed-point theorems (step_final, run_final_fix) are verified by the kernel.
        let s = meta_session().expect("driver metatheory should kernel-check");
        assert!(s.k.env().contains("step_final"));
        assert!(s.k.env().contains("run_final_fix"));
        // Driver adequacy: fuel composes and answers are stable under more fuel.
        assert!(s.k.env().contains("run_compose"));
        assert!(s.k.env().contains("run_stable"));
    }
}
