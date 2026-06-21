//! **A verified type checker and evaluator for System F** (the polymorphic λ-calculus) —
//! the parametric-polymorphism tier, built as a *self-contained* development beside the
//! simply-typed [`crate::stlc`] so the two never disturb each other's proofs.
//!
//! The calculus is Church-style System F with explicit types and de Bruijn indices for
//! **both** namespaces (term variables and type variables):
//!
//!  * **Types** `FTy` — type variables, a base type `tnat`, the arrow, and `∀` (`tall`,
//!    whose body may mention `tvar 0`). Type substitution `tsubst`/`tshift` is the
//!    standard capture-avoiding de Bruijn machinery.
//!  * **Terms** `FExp` — variables, `nat` literals, λ (annotated), application, **type
//!    abstraction** `Λ` (`etlam`) and **type application** `e [T]` (`etapp`). Type
//!    application instantiates: `(Λ. e) [T] → e{T/0}`, substituting `T` into the type
//!    annotations inside `e` (`esubstTy`).
//!  * **Checker** — `fsynth : FExp → FCtx → FTy` and `fok : FExp → FCtx → Bool`, with a
//!    decidable `ftyeq`. Entering a `Λ` shifts the term context's types (`shiftCtx`),
//!    because a fresh type variable is introduced beneath them.
//!  * **Dynamics** — a call-by-value evaluator (`run`) over `step`, with λ and Λ as values.
//!
//! Checkpoint A (this layer) is purely computational — it type-checks and *runs*
//! polymorphic programs. The typing relation `FHasTy` and the soundness / type-safety
//! metatheory are layered on top in later sessions.

use crate::verify::Session;

/// Logic + booleans + naturals — the reusable proof core (shared shape with
/// [`crate::stlc::PRELUDE`], minus the STLC-specific object types).
pub const SF_PRELUDE: &str = include_str!("raven/systemf_sf_prelude.rvk");

/// System F types, the type-substitution machinery, terms, the checker, and the
/// decidable type equality.
pub const SF_LANG: &str = include_str!("raven/systemf_sf_lang.rvk");

/// The call-by-value dynamics: capture-avoiding term/type substitution and a fuelled
/// evaluator. λ and Λ are values; `eapp` β-reduces, `etapp` does the type-β step.
pub const SF_DYNAMICS: &str = include_str!("raven/systemf_sf_dynamics.rvk");

/// **The typing relation `FHasTy` (the spec) and the soundness theorem.** `fok_sound`
/// proves the decidable checker implies a real typing derivation:
/// `fok e Γ = true → FHasTy Γ e (fsynth e Γ)`, by structural recursion on `e`. The `etlam`
/// case uses the shifted context; `etapp` inverts the synthesized type to a `∀` (`all_inv`)
/// and lands on `tsubst`; `eapp` inverts to an arrow and rewrites the domain (as in the STLC).
pub const SF_SAFETY: &str = include_str!("raven/systemf_sf_safety.rvk");

/// **Progress.** A well-typed *closed* term is a value or can step: `FHasTy nil e T →
/// isValue e ∨ canStep e`. Built from canonical-forms lemmas (`canon_arrow`/`canon_all`,
/// a value's shape is dictated by its type) and a structural reducibility predicate
/// `canStep`. Proved by recursion on the typing derivation.
pub const SF_PROGRESS: &str = include_str!("raven/systemf_sf_progress.rvk");

/// **Step relation + inversion scaffolding** for preservation. The small-step relation
/// `Step` mirrors the executable `step`; the no-confusion principle (`exp_noconf` via a
/// constructor tag) and the projection/injectivity helpers let the preservation proof
/// invert a typing derivation whose subject is a concrete constructor application.
pub const SF_STEP: &str = include_str!("raven/systemf_sf_step.rvk");

/// **FHasTy inversions + type-constructor injectivity.** From a typing derivation whose
/// subject is a concrete constructor application, recover the premises — the core of the
/// preservation proof's redex cases. Each inverts by matching the derivation over a
/// *variable* index with the concreteness supplied as an `Eq` hypothesis (impossible
/// constructors discharged by `exp_noconf`).
pub const SF_INV: &str = include_str!("raven/systemf_sf_inv.rvk");

/// **de Bruijn type-operation lemmas** — the Nat-ordering facts and the
/// shift/substitution commutation lemmas that the type-weakening and type-substitution
/// preservation lemmas rest on. The classic (intricate) core of mechanized System F.
pub const SF_TYLEMMAS: &str = include_str!("raven/systemf_sf_tylemmas.rvk");

/// **Context operations + lookup weakening/inversion** — the structural plumbing the
/// substitution lemmas need: inserting a binding (`insertCtxF`), shifting/substituting the
/// types in a context (`shiftCtxAt`/`tysubstCtx`), and the `FLookup` weakening + inversion
/// lemmas (ported from the STLC's parallel-substitution development, adapted to System F's
/// two-sorted de Bruijn contexts).
pub const SF_CTXOPS: &str = include_str!("raven/systemf_sf_ctxops.rvk");

/// **Context-level commutation lemmas + `FLookup` type-shift/subst + shiftCtx inversion.**
/// Lifts the de Bruijn commutation lemmas (`tshift_exchange`/`subst_shift_comm`/`tcancel`)
/// from single types to whole contexts, and proves how `FLookup` interacts with shifting and
/// substituting the context's types — the facts the type-weakening / type-substitution
/// preservation lemmas need.
pub const SF_CTXCOMM: &str = include_str!("raven/systemf_sf_ctxcomm.rvk");

/// **Weakening theorems.** Term weakening (`FHasTy_tmweaken`: inserting a term binding
/// anywhere preserves typing, with the term shifted) and type weakening (`FHasTy_tyweaken`:
/// inserting a fresh type variable shifts the context's types, the term's annotations, and
/// the result type together). Both by 6-arm induction on the `FHasTy` derivation; the type
/// binder (`fttlam`) and type application (`fttapp`) arms discharge via the context-level
/// commutation lemmas and `shift_subst_comm`.
pub const SF_WEAKEN: &str = include_str!("raven/systemf_sf_weaken.rvk");

/// **Parallel term substitution + the bridge to the recursive `esubstTm`.** Following the
/// STLC's parallel-substitution technique (a substitution is a `Nat -> FExp`), `applySub`
/// applies one, lifting under term binders (`liftSubF`) and type binders (`liftSubTyF`). The
/// bridge `subst_bridge` proves `esubstTm e j v = applySub e (atSubjF j v)`, so the
/// substitution lemma (proved cleanly over the original context for `applySub`) transfers to
/// the `esubstTm` used by the operational semantics. Its two index lemmas reconcile the
/// single-substitution assignment under a lift with a shifted assignment.
pub const SF_TSUBSTA: &str = include_str!("raven/systemf_sf_tsubsta.rvk");

/// The index lemmas + the bridge (split out for isolation).
pub const SF_TSUBSTB: &str = include_str!("raven/systemf_sf_tsubstb.rvk");
pub const SF_TSUBSTC: &str = include_str!("raven/systemf_sf_tsubstc.rvk");
pub const SF_TSUBSTD: &str = include_str!("raven/systemf_sf_tsubstd.rvk");

/// **The term substitution lemma + `subst_preserves`.** A well-typed term stays well-typed
/// under any substitution mapping the context's variables to well-typed terms in a target
/// context (`subst_lemma`, proved over the original context so the variable case is trivial).
/// Term binders extend the substitution with `liftSubF` (typed by `liftSub_respects`), type
/// binders with `liftSubTyF` (typed by `liftSubTy_respects`, which crosses the type-shift via
/// `FHasTy_tyweaken`). `esubstTm_preserves` transports the single-variable instance back to
/// the operational `esubstTm` through the bridge — the β-redex case of preservation.
pub const SF_TSUBSTE: &str = include_str!("raven/systemf_sf_tsubste.rvk");

/// **The type substitution lemma + type-β preservation.** Substituting a type `S` for a
/// type variable in a well-typed term preserves typing, substituting `S` through the context
/// and result type too (`tysubst_lemma`, 6-arm induction; the `fttlam` arm uses the
/// context-level `subst_shift_comm`, the `fttapp` arm uses `subst_subst_comm`). Specialising
/// at variable 0 over a freshly-shifted context (cancelled by `tysubstCtx_shiftCtx_cancel`)
/// yields `tysubst_preserves` — the type-β redex case of preservation.
pub const SF_TYSUBST: &str = include_str!("raven/systemf_sf_tysubst.rvk");

/// **PRESERVATION** — the capstone. `Step e e2 → FHasTy G e T → FHasTy G e2 T`. By induction
/// on the reduction: congruences re-apply typing after inverting the compound term (and use
/// the IH `.rec`), the β-redex is discharged by `esubstTm_preserves` (after inverting the
/// λ and rewriting domain/codomain via arrow injectivity), and the type-β redex by
/// `tysubst_preserves` (after inverting the Λ and rewriting via `tall` injectivity). Together
/// with `progress`, this is full type safety for System F in the verified kernel.
pub const SF_PRES: &str = include_str!("raven/systemf_sf_pres.rvk");

/// Prelude + types + checker.
pub fn lang_session() -> Result<Session, String> {
    let mut s = Session::new();
    s.run(SF_PRELUDE)?;
    s.run(SF_LANG)?;
    Ok(s)
}

/// Additionally loads the evaluator, so polymorphic programs can be run.
pub fn runnable_session() -> Result<Session, String> {
    let mut s = lang_session()?;
    s.run(SF_DYNAMICS)?;
    Ok(s)
}

/// Loads the typing relation + soundness theorem on top of the checker.
pub fn safety_session() -> Result<Session, String> {
    let mut s = lang_session()?;
    s.run(SF_SAFETY)?;
    Ok(s)
}

/// Loads progress (needs the evaluator's `isValue` + the typing relation).
pub fn progress_session() -> Result<Session, String> {
    let mut s = lang_session()?;
    s.run(SF_DYNAMICS)?;
    s.run(SF_SAFETY)?;
    s.run(SF_PROGRESS)?;
    Ok(s)
}

/// Loads the Step relation + inversion scaffolding (toward preservation).
pub fn step_session() -> Result<Session, String> {
    let mut s = lang_session()?;
    s.run(SF_DYNAMICS)?;
    s.run(SF_SAFETY)?;
    s.run(SF_STEP)?;
    Ok(s)
}

/// Loads the FHasTy inversions (toward preservation's redex cases).
pub fn inv_session() -> Result<Session, String> {
    let mut s = step_session()?;
    s.run(SF_INV)?;
    Ok(s)
}

/// Loads the de Bruijn type-operation lemmas (toward the substitution lemmas) on top of
/// the full inversion stack (so it can reuse `SF_SAFETY`'s congruences + `eqNat_sound`).
pub fn tylemmas_session() -> Result<Session, String> {
    let mut s = inv_session()?;
    s.run(SF_TYLEMMAS)?;
    Ok(s)
}

/// Loads the context-operation + lookup weakening/inversion plumbing.
pub fn ctxops_session() -> Result<Session, String> {
    let mut s = tylemmas_session()?;
    s.run(SF_CTXOPS)?;
    Ok(s)
}

/// Loads the context-level commutation lemmas + FLookup type-shift/subst/inversion.
pub fn ctxcomm_session() -> Result<Session, String> {
    let mut s = ctxops_session()?;
    s.run(SF_CTXCOMM)?;
    Ok(s)
}

/// Loads the term + type weakening theorems.
pub fn weaken_session() -> Result<Session, String> {
    let mut s = ctxcomm_session()?;
    s.run(SF_WEAKEN)?;
    Ok(s)
}

/// Loads the parallel-substitution functions + congruences + applySub_ext.
pub fn tsubsta_session() -> Result<Session, String> {
    let mut s = weaken_session()?;
    s.run(SF_TSUBSTA)?;
    Ok(s)
}

/// Loads the index lemmas + the `esubstTm` bridge.
pub fn tsubstb_session() -> Result<Session, String> {
    let mut s = tsubsta_session()?;
    s.run(SF_TSUBSTB)?;
    s.run(SF_TSUBSTC)?;
    s.run(SF_TSUBSTD)?;
    Ok(s)
}

/// Loads the term substitution lemma + `subst_preserves`/`esubstTm_preserves`.
pub fn tsubst_session() -> Result<Session, String> {
    let mut s = tsubstb_session()?;
    s.run(SF_TSUBSTE)?;
    Ok(s)
}

/// Loads the type substitution lemma + type-β preservation.
pub fn tysubst_session() -> Result<Session, String> {
    let mut s = tsubst_session()?;
    s.run(SF_TYSUBST)?;
    Ok(s)
}

/// Loads **preservation** (needs the Step relation, the inversions, and both substitution
/// lemmas) — full System F type safety together with `progress`.
pub fn preservation_session() -> Result<Session, String> {
    let mut s = tysubst_session()?;
    s.run(SF_PRES)?;
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nat(n: u64) -> String {
        let mut s = String::from("Nat.zero");
        for _ in 0..n {
            s = format!("Nat.succ({s})");
        }
        s
    }

    /// The whole checker + evaluator layer elaborates and is kernel-checked.
    #[test]
    fn systemf_lang_checks() {
        runnable_session().expect("System F types + checker + evaluator should check");
    }

    /// The typing relation + **soundness theorem** (`fok_sound`) elaborates and is
    /// kernel-checked: a passing decidable check yields a real System F typing derivation.
    #[test]
    fn systemf_soundness_checks() {
        safety_session().expect("System F typing relation + soundness should check");
    }

    /// **Progress** (`FHasTy nil e T → isValue e ∨ canStep e`) elaborates and is kernel-checked.
    #[test]
    fn systemf_progress_checks() {
        progress_session().expect("System F progress should check");
    }

    /// The Step relation + inversion/no-confusion scaffolding (toward preservation) checks.
    #[test]
    fn systemf_step_checks() {
        step_session().expect("System F Step relation + scaffolding should check");
    }

    /// The FHasTy inversions (toward preservation) elaborate and are kernel-checked.
    #[test]
    fn systemf_inversions_check() {
        inv_session().expect("System F typing inversions should check");
    }

    /// The de Bruijn type-operation lemmas elaborate and are kernel-checked.
    #[test]
    fn systemf_tylemmas_check() {
        tylemmas_session().expect("System F de Bruijn type lemmas should check");
    }

    /// The context-operation + lookup weakening/inversion plumbing elaborates and checks.
    #[test]
    fn systemf_ctxops_check() {
        ctxops_session().expect("System F context-op + lookup lemmas should check");
    }

    /// The context-level commutation + FLookup shift/subst/inversion lemmas check.
    #[test]
    fn systemf_ctxcomm_check() {
        ctxcomm_session().expect("System F context commutation lemmas should check");
    }

    /// The term + type weakening theorems elaborate and are kernel-checked.
    #[test]
    fn systemf_weaken_check() {
        weaken_session().expect("System F weakening theorems should check");
    }

    /// The parallel-substitution functions + the `esubstTm` bridge elaborate and check.
    #[test]
    fn systemf_tsubsta_check() {
        tsubstb_session().expect("System F parallel substitution + bridge should check");
    }

    /// The term substitution lemma + `subst_preserves`/`esubstTm_preserves` check.
    #[test]
    fn systemf_tsubst_check() {
        tsubst_session().expect("System F term substitution lemma should check");
    }

    /// The type substitution lemma + type-β preservation elaborate and check.
    #[test]
    fn systemf_tysubst_check() {
        tysubst_session().expect("System F type substitution lemma should check");
    }

    /// **PRESERVATION** elaborates and is kernel-checked: System F reduction preserves typing.
    #[test]
    fn systemf_preservation_check() {
        preservation_session().expect("System F preservation should check");
    }

    /// **Preservation has teeth.** For the concrete type-β redex `(Λ. λ(x:tvar0). x) [nat]`,
    /// the kernel runs `preservation` on the actual `Step.s_ttbeta` derivation to produce a
    /// checked typing for the contractum `λ(x:nat). x` — at the *same* synthesized type.
    #[test]
    fn preservation_certifies_polymorphic_step() {
        let mut s = preservation_session().unwrap();
        s.run("def polyIdBody : FExp := FExp.elam(FTy.tvar(Nat.zero), FExp.evar(Nat.zero))").unwrap();
        s.run("def redex : FExp := FExp.etapp(FExp.etlam(polyIdBody), FTy.tnat)").unwrap();
        s.run("def redex_ty : FTy := fsynth(redex)(FCtx.nil)").unwrap();
        s.run("def redex_typed : FHasTy FCtx.nil redex redex_ty := fok_sound(redex)(FCtx.nil)(Eq.refl.{1} Bool Bool.true)").unwrap();
        s.run(
            "def stepped_typed : FHasTy FCtx.nil (esubstTy(polyIdBody)(Nat.zero)(FTy.tnat)) redex_ty := \
               preservation(redex)(esubstTy(polyIdBody)(Nat.zero)(FTy.tnat))(Step.s_ttbeta polyIdBody FTy.tnat)(FCtx.nil)(redex_ty)(redex_typed)",
        )
        .expect("preservation should certify the contractum at the same type");
        assert!(s.k.env().contains("stepped_typed"));
    }

    /// **Soundness has teeth.** For the polymorphic identity, the `refl` certificate exists,
    /// so `fok_sound` produces a kernel-checked derivation `FHasTy nil polyId (∀.0→0)`.
    #[test]
    fn soundness_certifies_polymorphic_identity() {
        let mut s = safety_session().unwrap();
        s.run("def polyId : FExp := FExp.etlam(FExp.elam(FTy.tvar(Nat.zero), FExp.evar(Nat.zero)))").unwrap();
        s.run(
            "def polyId_typed : FHasTy FCtx.nil polyId (fsynth(polyId)(FCtx.nil)) := \
               fok_sound(polyId)(FCtx.nil)(Eq.refl.{1} Bool Bool.true)",
        )
        .expect("a well-typed polymorphic term has a checked derivation");
        assert!(s.k.env().contains("polyId_typed"));
    }

    /// **Polymorphism type-checks and runs.** The polymorphic identity
    /// `Λ. λ(x:tvar0). x : ∀. tvar0 → tvar0`, instantiated at `nat` and applied to `5`,
    /// synthesizes `nat` and runs to `5` — type application substitutes `nat` into the
    /// λ's annotation, then β-reduces.
    #[test]
    fn polymorphic_identity_runs() {
        let mut s = runnable_session().unwrap();
        s.run("def polyId : FExp := FExp.etlam(FExp.elam(FTy.tvar(Nat.zero), FExp.evar(Nat.zero)))").unwrap();
        s.run("def polyId_ty : FTy := fsynth(polyId)(FCtx.nil)").unwrap();
        s.run("def polyId_ok : Bool := fok(polyId)(FCtx.nil)").unwrap();
        // (polyId [nat]) 5
        s.run(&format!(
            "def app : FExp := FExp.eapp(FExp.etapp(polyId, FTy.tnat), FExp.enat({}))", nat(5)
        )).unwrap();
        s.run("def app_ty : FTy := fsynth(app)(FCtx.nil)").unwrap();
        s.run("def app_ok : Bool := fok(app)(FCtx.nil)").unwrap();
        s.run(&format!("def app_val : FExp := run({})(app)", nat(10))).unwrap();
        assert_eq!(s.run_entry("polyId_ok").unwrap(), "Bool.true");
        assert_eq!(s.run_entry("polyId_ty").unwrap(), "FTy.tall (FTy.tarrow (FTy.tvar 0) (FTy.tvar 0))");
        assert_eq!(s.run_entry("app_ok").unwrap(), "Bool.true", "instantiated application is well typed");
        assert_eq!(s.run_entry("app_ty").unwrap(), "FTy.tnat", "polyId [nat] 5 : nat");
        assert_eq!(s.run_entry("app_val").unwrap(), "FExp.enat 5", "polyId [nat] 5 = 5");
    }
}
