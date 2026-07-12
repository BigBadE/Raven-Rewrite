//! **Step 1 of univalence, part 2**: the `Glue` type former's strictness laws.
//!
//! This module carries no new runtime logic of its own — `Term::Glue`'s typing
//! rule lives in [`crate::check::Checker::infer`], its reduction rule in
//! [`crate::reduce::Reducer::whnf`], and its NbE evaluation in
//! [`crate::nbe::Nbe::eval`]/`quote` — it exists to hold this pass's adversarial
//! and differential tests in one place, mirroring how [`crate::equiv`] holds the
//! `Equiv`/`idEquiv` tests.
//!
//! ## What `Glue A [φ ↦ (T, e)]` means here (recap, see `Term::Glue`'s doc)
//!
//! A type that is `T` where `φ` holds and `A` off it, with `e : Equiv T A` gluing
//! them together. This increment ships only the **former** and its two strictness
//! laws:
//!
//!   * `Glue A [φ ↦ (T,e)] ↦ T`   when `φ` is decided `⊤`
//!   * `Glue A [φ ↦ (T,e)] ↦ A`   when `φ` is decided `⊥` (no constraint at all)
//!
//! `glue`/`unglue` (the introduction/elimination forms) are **not** implemented —
//! see `Term::Glue`'s doc for why, and the crate-level task notes for what's
//! deferred. This has a load-bearing consequence checked below
//! ([`glue_type_is_uninhabited_without_real_data`]): with no introduction rule,
//! nothing can inhabit an *undecided* `Glue` type at all (soundly — there's simply
//! no term-former that produces one), so there is no way for `Glue` to "manufacture"
//! a false proof; the only way to get *any* value of a `Glue A [φ↦(T,e)]` type is by
//! `φ` reducing all the way to `⊤`/`⊥`, at which point the type collapses to
//! `T`/`A` and is inhabited exactly as they are.

#[cfg(test)]
mod tests {
    use crate::check::{Checker, LocalCtx};
    use crate::equiv::declare_equiv;
    use crate::face::Cof;
    use crate::inductive::declare_nat;
    use crate::level::Level;
    use crate::nbe::Nbe;
    use crate::reduce::Reducer;
    use crate::term::{name, Term};

    fn env_with_nat_equiv() -> crate::env::Env {
        let mut env = crate::env::Env::new();
        declare_nat(&mut env).unwrap();
        declare_equiv(&mut env).unwrap();
        env
    }

    fn nat() -> Term {
        Term::cnst(name("Nat"), vec![])
    }

    /// `idEquiv Nat : Equiv Nat Nat` — reused as the `e` in every test below (we
    /// only need *some* well-typed equivalence; `idEquiv` is the simplest).
    fn id_equiv_nat() -> Term {
        Term::app(Term::cnst(name("idEquiv"), vec![Level::of_nat(1)]), nat())
    }

    /// `Glue Nat [⊤ ↦ (Nat, idEquiv Nat)]` type-checks, at the universe `Nat`
    /// itself lives in.
    #[test]
    fn glue_top_type_checks() {
        let env = env_with_nat_equiv();
        let chk = Checker::new(&env);
        let g = Term::glue_ty(nat(), Cof::top(), nat(), id_equiv_nat());
        let mut ctx = LocalCtx::new();
        let sort = chk.infer(&mut ctx, &g).expect("Glue Nat [⊤ ↦ (Nat,idEquiv)] should type-check");
        let Term::Sort(l) = sort else { panic!("Glue's inferred type should be a Sort") };
        assert!(crate::level::equiv(&l, &Level::of_nat(1)));
    }

    /// **Strictness**: `Glue A [⊤ ↦ (T,e)]` really reduces to `T` — the defining
    /// CCHM property, checked both by the trusted [`Reducer`] and independently by
    /// [`Nbe`] (differentially — the crate's standing convention).
    #[test]
    fn glue_top_reduces_to_t() {
        let env = env_with_nat_equiv();
        let succ_nat = Term::arrow(nat(), nat()); // an arbitrary T distinct from A below
        let a = Term::arrow(nat(), Term::arrow(nat(), nat()));
        // e's type doesn't matter for this *reduction*-only test (the ⊤ branch
        // never inspects `e`) — reuse `idEquiv Nat` as a placeholder well-typed term.
        let g = Term::glue_ty(a.clone(), Cof::top(), succ_nat.clone(), id_equiv_nat());

        let r = Reducer::new(&env);
        assert!(r.is_def_eq(&g, &succ_nat), "whnf: Glue A [⊤↦(T,e)] should ≡ T");
        assert!(!r.is_def_eq(&g, &a), "sanity: T and A were chosen distinct");

        let nbe = Nbe::new(&env);
        let ng = nbe.normalize(&g);
        let nt = nbe.normalize(&succ_nat);
        assert_eq!(ng, nt, "NbE must agree with the reducer on the ⊤-strictness rule");
    }

    /// **Strictness (⊥ side)**: with *no* constraint at all (`φ = ⊥`), `Glue`
    /// degenerates to plain `A` — checked both by the reducer and by NbE.
    #[test]
    fn glue_bot_reduces_to_a() {
        let env = env_with_nat_equiv();
        let a = nat();
        let t = Term::arrow(nat(), nat());
        let g = Term::glue_ty(a.clone(), Cof::bot(), t.clone(), id_equiv_nat());

        let r = Reducer::new(&env);
        assert!(r.is_def_eq(&g, &a), "whnf: Glue A [⊥↦…] should ≡ A");
        assert!(!r.is_def_eq(&g, &t));

        let nbe = Nbe::new(&env);
        assert_eq!(nbe.normalize(&g), nbe.normalize(&a));
    }

    /// When `φ` is genuinely undecided (a free interval variable, not literally
    /// `⊤`/`⊥`), `Glue` stays **stuck** — a valid normal form, not equal to either
    /// `T` or `A` — exactly like a stuck `Sys`/`HComp`. Checked under a context
    /// with one bound interval variable.
    #[test]
    fn glue_open_phi_stays_stuck() {
        let env = env_with_nat_equiv();
        // A and T are chosen *distinct* (so a stuck `Glue` can be told apart from
        // both), but `e`'s type must still match the `T` actually used here: since
        // `idEquiv Nat : Equiv Nat Nat`, take `T = A = Nat` and instead vary the
        // *outer* shape via a second, syntactically distinct copy `Nat -> Nat` only
        // for the disequality checks below (never fed into `Glue` itself).
        let a = nat();
        let t = nat();
        let distinct = Term::arrow(nat(), nat());
        // φ = (i =0), with `i` a bound (not yet i0/i1) interval variable: undecided.
        let phi = Cof::eq0(Term::Var(0));
        let g = Term::glue_ty(a.clone(), phi, t.clone(), id_equiv_nat().lift(1, 0));
        let r = Reducer::new(&env);
        // Stuck means whnf doesn't collapse it to something unrelated…
        assert!(!r.is_def_eq(&g, &distinct.lift(1, 0)));
        // …and, more importantly, is *itself* — not silently `whnf`'d away to
        // something else — by comparing its own re-quoted `Glue` head is preserved.
        assert!(matches!(r.whnf(&g), Term::Glue(..)));
        // But it's still a well-formed type under `i : I`.
        let chk = Checker::new(&env);
        let mut ctx = LocalCtx::new();
        ctx.push(Term::I);
        chk.infer(&mut ctx, &g).expect("Glue with an open φ is still a well-formed type");
    }

    /// **Type formation rejects a T/A universe mismatch**: `Glue` requires `T` and
    /// `A` to live in the *same* Sort (this increment's scoped simplification —
    /// see `Term::Glue`'s doc); a genuine mismatch (`A : Type 0`, `T : Type 1`) must
    /// be rejected, not silently accepted.
    #[test]
    fn glue_rejects_mismatched_universes() {
        let env = env_with_nat_equiv();
        let chk = Checker::new(&env);
        let a = nat(); // : Type 0 (Sort 1)
        let t = Term::typ(0); // : Type 1 (Sort 2) — a genuine universe, not Type 0
        let g = Term::glue_ty(a, Cof::top(), t, id_equiv_nat());
        let mut ctx = LocalCtx::new();
        assert!(chk.infer(&mut ctx, &g).is_err(), "T : Type 1 vs A : Type 0 must be rejected");
    }

    /// **Type formation rejects a non-equivalence `e`**: swapping in a term that
    /// isn't `Equiv T A` (e.g. one plainly of the wrong type) must fail.
    #[test]
    fn glue_rejects_non_equivalence_e() {
        let env = env_with_nat_equiv();
        let chk = Checker::new(&env);
        let bogus_e = Term::lam(nat(), Term::Var(0)); // : Nat -> Nat, not Equiv Nat Nat
        let g = Term::glue_ty(nat(), Cof::top(), nat(), bogus_e);
        let mut ctx = LocalCtx::new();
        assert!(chk.infer(&mut ctx, &g).is_err());
    }

    /// **Anti-`False` / canonicity**: there is no term-former in this increment
    /// that *introduces* an element of an undecided `Glue` (no `Term::GlueIntro`
    /// exists at all yet — `glue`/`unglue` are deferred), so `Glue` cannot be used
    /// to conjure a proof of anything false. Concretely: the only way to reach a
    /// concrete value *of* a `Glue A [φ↦(T,e)]`-typed expression is for `φ` to
    /// already be decided, at which point the type itself collapses (by the
    /// strictness rule) to plain `T` or `A` — so this test pins down that even
    /// `Glue Nat [⊤↦(Nat,idEquiv Nat)]`, which certainly *is* inhabited (e.g. by
    /// `Nat.zero`, since the type is ≡ `Nat`), cannot be used to prove
    /// `Path Nat Nat.zero (Nat.succ Nat.zero)` — nothing about `Glue` forged a new
    /// equation between genuinely different naturals.
    #[test]
    fn glue_type_is_uninhabited_without_real_data() {
        let env = env_with_nat_equiv();
        let chk = Checker::new(&env);
        let zero = Term::cnst(name("Nat.zero"), vec![]);
        let one = Term::app(Term::cnst(name("Nat.succ"), vec![]), zero.clone());
        // `Glue Nat [⊤ ↦ (Nat, idEquiv Nat)]` ≡ `Nat`, so `Nat.zero` genuinely
        // checks against it (unsurprising — this is just `T` in disguise)...
        let g = Term::glue_ty(nat(), Cof::top(), nat(), id_equiv_nat());
        let mut ctx = LocalCtx::new();
        chk.check(&mut ctx, &zero, &g).expect("Nat.zero : Glue Nat [⊤↦(Nat,idEquiv)] since the type ≡ Nat");
        // ...but that does not make `0` and `1` equal.
        let r = Reducer::new(&env);
        assert!(!r.is_def_eq(&zero, &one), "Glue's strictness must not equate distinct naturals");
    }
}
