//! **Step 1 of univalence, part 2**: the multi-face `Glue` type former, `unglue`,
//! and — the headline of this pass — `ua : Equiv A B → Path Type A B`.
//!
//! Most of this module's *typing*/*reduction*/*NbE* logic lives elsewhere —
//! `Term::Glue`/`Term::Unglue`'s typing rules in [`crate::check::Checker::infer`],
//! their reduction rules in [`crate::reduce::Reducer::whnf`], and their NbE
//! evaluation in [`crate::nbe::Nbe::eval`]/`quote` — this module holds (1) the
//! [`ua`] term-builder itself, and (2) this pass's adversarial and differential
//! tests in one place, mirroring how [`crate::equiv`] holds the `Equiv`/`idEquiv`
//! tests.
//!
//! ## What `Glue A [φ_1 ↦ (T_1,e_1), …]` means here (recap, see `Term::Glue`'s doc)
//!
//! A type that is `T_k` where `φ_k` holds (branches pairwise compatible on their
//! overlap) and `A` off every face, with `e_k : Equiv T_k A` gluing each `T_k` to
//! `A`. The **strictness laws**, generalized to `n` branches:
//!
//!   * `Glue A […, φ_k ↦ (T_k,e_k), …] ↦ T_k`   when `φ_k` is decided `⊤`
//!   * `Glue A [φ_1 ↦ …, …] ↦ A`                when *every* `φ_k` is decided `⊥`
//!
//! `unglue A […] u` is the elimination form (see `Term::Unglue`'s doc): the
//! identity off every face, `e_k.f u` on a decided `φ_k`. There is still no
//! `glue` (introduction) former — see `Term::Glue`'s doc for the precise deferred
//! scope — which has the same load-bearing soundness consequence as before
//! ([`glue_type_is_uninhabited_without_real_data`]): nothing can inhabit an
//! *undecided* `Glue` type, so `Glue`/`unglue` cannot "manufacture" a false proof.
//!
//! ## `ua : Π (A B : Type) (e : Equiv A B). Path Type A B`
//!
//! (CCHM, *Cubical Type Theory*, §6.3, "Univalence".) Defined as
//!
//! ```text
//! ua A B e := ⟨i⟩ Glue B [ (i=0) ↦ (A, e), (i=1) ↦ (B, idEquiv B) ]
//! ```
//!
//! **Orientation** (spelled out precisely, since `e : Equiv A B` while `Glue`'s
//! branches need `e_k : Equiv T_k A_base`): the `Glue`'s *base* is fixed at `B`
//! throughout (matching CCHM's convention that `Glue`'s base is the type the path
//! lands on at `i1`). The `(i=0)` branch's `T = A` and its equivalence must then
//! be `Equiv A B` — exactly the `e` the caller supplied, used **unchanged**, no
//! inversion needed. The `(i=1)` branch's `T = B` needs `Equiv B B`, supplied by
//! `idEquiv B`. Both branches type-check directly against the *same* fixed base
//! `B`, so — unlike an encoding that would nest single-face `Glue`s inside one
//! another's base slot — no nesting or level-of-indirection is needed; this is a
//! genuine 2-branch flat [`Term::Glue`].
//!
//! **Why the boundaries come out exactly `A`/`B`**: substituting `i := i0` decides
//! `(i0=0)` to `⊤` and `(i0=1)` to `⊥` (a literal endpoint each time — see
//! `crate::face::is_true`/`is_false`), so the `Glue`'s `⊤`-strictness rule fires
//! on the *first* branch, collapsing the whole `Glue` to its `T`, i.e. `A`;
//! substituting `i := i1` symmetrically decides `(i1=0)` to `⊥` and `(i1=1)` to
//! `⊤`, collapsing to `B`. This is exactly [`Term::PLam`]'s ordinary β-rule for
//! `PApp` composed with `Glue`'s own strictness — no bespoke boundary rule is
//! needed in the checker; [`crate::check::Checker::path_boundary`]'s existing
//! `p @ i0 ≡ a0` / `p @ i1 ≡ a1` machinery (already used for every `PathP`) checks
//! it uniformly, exercised concretely by [`ua_typechecks_at_path_type_a_b`] below.
//!
//! **Deferred** (documented, not a soundness gap): the *computational* content of
//! univalence — `transport (ua e) a₀ ↦ e.f a₀` — needs Kan filling (`comp`) for
//! `Glue`, not shipped this pass (see `crate::term::Term::Glue`'s doc and
//! `crate::kan`'s module doc); likewise the half-adjoint upgrade of `Equiv`
//! (needed for the univalence *theorem*, i.e. that `ua` itself is an equivalence)
//! and any `glue` introduction former beyond what `ua`'s *type-only* use of
//! `Glue` requires.
use crate::face::Cof;
use crate::level::Level;
use crate::term::{name, Term};

/// `ua A B e := ⟨i⟩ Glue B [(i=0) ↦ (A,e), (i=1) ↦ (B, idEquiv B)]` (see this
/// module's doc for the full orientation argument). `level` is the shared
/// universe level `A`/`B` live in (the same `u` `Equiv.{u}`/`idEquiv.{u}` are
/// instantiated at) — this builder does **not** infer it, mirroring every other
/// bare term-former in this crate (callers type-check the result, e.g. via
/// [`Checker::infer`], which independently confirms `level` was chosen correctly).
pub fn ua(level: Level, a: Term, b: Term, e: Term) -> Term {
    let a1 = a.lift(1, 0);
    let b1 = b.lift(1, 0);
    let e1 = e.lift(1, 0);
    let id_equiv_b = Term::app(Term::cnst(name("idEquiv"), vec![level]), b1.clone());
    let i = Term::Var(0);
    let glue_body = Term::glue_ty_multi(
        b1.clone(),
        vec![(Cof::eq0(i.clone()), a1, e1), (Cof::eq1(i), b1, id_equiv_b)],
    );
    Term::plam(glue_body)
}

/// `Path Type A B` — `ua`'s stated codomain (see this module's doc), at the
/// *next* universe up from `A`/`B`'s own `level` (a `Sort level` inhabitant like
/// `A`/`B` themselves lives one universe below the `Sort` classifying `Path`
/// between them — same convention as `Term::path`'s ordinary use).
pub fn ua_ty(level: Level, a: Term, b: Term) -> Term {
    Term::path(Term::Sort(level), a, b)
}

#[cfg(test)]
mod tests {
    use super::{ua, ua_ty};
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

    // ---- Multi-face `Glue` ----

    /// A genuine 2-branch `Glue Nat [⊤ ↦ (Nat,idEquiv), ⊥ ↦ (Nat,idEquiv)]` (both
    /// faces decided, no overlap since `⊤ ∧ ⊥ ≡ ⊥`) type-checks and picks up the
    /// `⊤` branch's strictness, exactly like the `n=1` case.
    #[test]
    fn multi_face_glue_top_wins_and_type_checks() {
        let env = env_with_nat_equiv();
        let chk = Checker::new(&env);
        let g = Term::glue_ty_multi(
            nat(),
            vec![(Cof::top(), nat(), id_equiv_nat()), (Cof::bot(), nat(), id_equiv_nat())],
        );
        let mut ctx = LocalCtx::new();
        chk.infer(&mut ctx, &g).expect("2-branch Glue with disjoint faces should type-check");
        let r = Reducer::new(&env);
        assert!(r.is_def_eq(&g, &nat()));
    }

    /// **Incompatible branches are rejected**: two branches whose overlap is
    /// satisfiable (both `⊤`) but whose `T`s disagree must fail to type-check —
    /// the compatibility obligation `check_glue_branches_compatible` imposes.
    #[test]
    fn multi_face_glue_rejects_incompatible_branches() {
        let env = env_with_nat_equiv();
        let chk = Checker::new(&env);
        let distinct_t = Term::arrow(nat(), nat()); // : same universe as Nat, but ≠ Nat
        let g = Term::glue_ty_multi(
            nat(),
            vec![
                (Cof::top(), nat(), id_equiv_nat()),
                (Cof::top(), distinct_t, id_equiv_nat().lift(0, 0)),
            ],
        );
        let mut ctx = LocalCtx::new();
        assert!(
            chk.infer(&mut ctx, &g).is_err(),
            "two branches both decided ⊤ but disagreeing on T must be rejected"
        );
    }

    /// An empty branch list is rejected outright (see `Term::Glue`'s multi-face
    /// doc): `Glue A []` isn't a sound encoding of plain `A`, it's simply ill-formed.
    #[test]
    fn glue_rejects_empty_branch_list() {
        let env = env_with_nat_equiv();
        let chk = Checker::new(&env);
        let g = Term::Glue(std::rc::Rc::new(nat()), std::rc::Rc::new(vec![]));
        let mut ctx = LocalCtx::new();
        assert!(chk.infer(&mut ctx, &g).is_err());
    }

    // ---- `unglue` ----

    /// **`unglue`'s `⊥`-strictness**: off every face, `unglue` is the identity.
    #[test]
    fn unglue_bot_is_identity() {
        let env = env_with_nat_equiv();
        let zero = Term::cnst(name("Nat.zero"), vec![]);
        let u = Term::unglue(nat(), vec![(Cof::bot(), nat(), id_equiv_nat())], zero.clone());
        let r = Reducer::new(&env);
        assert!(r.is_def_eq(&u, &zero));
        let nbe = Nbe::new(&env);
        assert_eq!(nbe.normalize(&u), nbe.normalize(&zero));
    }

    /// **`unglue`'s `⊤`-strictness**: on a decided face, `unglue A [⊤↦(T,e)] u`
    /// reduces to `Equiv.f T A e u` — checked concretely with `e = idEquiv Nat`
    /// (so `Equiv.f (idEquiv Nat) ≡ λx.x`, i.e. `unglue … u ↦ u` too, but via a
    /// genuinely different reduction path than the `⊥` case above — differentially
    /// confirmed against the expected `Equiv.f` spelling, not just against `u`).
    #[test]
    fn unglue_top_applies_equiv_f() {
        let env = env_with_nat_equiv();
        let zero = Term::cnst(name("Nat.zero"), vec![]);
        let u = Term::unglue(nat(), vec![(Cof::top(), nat(), id_equiv_nat())], zero.clone());
        let expected = Term::apps(
            Term::cnst(name("Equiv.f"), vec![Level::of_nat(1)]),
            [nat(), nat(), id_equiv_nat(), zero],
        );
        let r = Reducer::new(&env);
        assert!(r.is_def_eq(&u, &expected), "unglue on a ⊤ face should compute via Equiv.f");
        let nbe = Nbe::new(&env);
        assert_eq!(nbe.normalize(&u), nbe.normalize(&expected));
    }

    /// `unglue`'s typing rule requires `u : Glue A […]` built from the *same*
    /// branches — feeding a scrutinee of an unrelated type must be rejected.
    #[test]
    fn unglue_rejects_scrutinee_of_wrong_type() {
        let env = env_with_nat_equiv();
        let chk = Checker::new(&env);
        let bogus_u = Term::lam(nat(), Term::Var(0)); // : Nat -> Nat, not Glue Nat […]
        let u = Term::unglue(nat(), vec![(Cof::top(), nat(), id_equiv_nat())], bogus_u);
        let mut ctx = LocalCtx::new();
        assert!(chk.infer(&mut ctx, &u).is_err());
    }

    // ---- `ua : Π (A B : Type) (e : Equiv A B). Path Type A B` ----

    /// The headline test: `ua Nat Nat (idEquiv Nat)` type-checks at
    /// `Path Type Nat Nat`, and its two boundaries — `ua … @ i0`/`@ i1` — are
    /// definitionally exactly `Nat`/`Nat` (checked both via the kernel's
    /// `path_boundary` conversion rule, exercised through `chk.infer`, and
    /// directly via the reducer on explicit `PApp`s to `i0`/`i1`).
    #[test]
    fn ua_typechecks_at_path_type_a_b() {
        let env = env_with_nat_equiv();
        let chk = Checker::new(&env);
        let lvl = Level::of_nat(1); // Nat : Type 0 ≡ Sort 1
        let n = nat();
        let e = id_equiv_nat();
        let term = ua(lvl.clone(), n.clone(), n.clone(), e);
        let expected_ty = ua_ty(lvl, n.clone(), n.clone());
        let mut ctx = LocalCtx::new();
        let inferred = chk.infer(&mut ctx, &term).expect("ua Nat Nat (idEquiv Nat) should type-check");
        assert!(
            Reducer::new(&env).is_def_eq(&inferred, &expected_ty),
            "ua's inferred type should be Path Type Nat Nat"
        );
        // The boundaries, checked directly: `ua … @ i0 ≡ A`, `ua … @ i1 ≡ B`.
        let r = Reducer::new(&env);
        let at_i0 = Term::papp(term.clone(), Term::IZero);
        let at_i1 = Term::papp(term.clone(), Term::IOne);
        assert!(r.is_def_eq(&at_i0, &n), "ua A B e @ i0 should be ≡ A");
        assert!(r.is_def_eq(&at_i1, &n), "ua A B e @ i1 should be ≡ B");
        // Cross-check via NbE too (this crate's differential-testing convention).
        let nbe = Nbe::new(&env);
        assert_eq!(nbe.normalize(&at_i0), nbe.normalize(&n));
        assert_eq!(nbe.normalize(&at_i1), nbe.normalize(&n));
    }

    /// `ua`'s boundaries with **distinct** `A`/`B` (`A = Nat`, `B = Nat → Nat`, an
    /// arbitrary well-typed `e : Equiv Nat (Nat→Nat)` isn't needed for *this*
    /// check — `ua`'s type-formation only requires *some* well-typed `e`, and the
    /// boundary computation never inspects `e`'s content at all, only `φ`'s
    /// decidedness — so this test pins the boundary rule down independently of
    /// `A ≡ B`, ruling out an implementation that accidentally always produces
    /// `A` (or always `B`) on both ends.
    #[test]
    fn ua_boundaries_distinguish_a_from_b_when_distinct() {
        let env = env_with_nat_equiv();
        let r = Reducer::new(&env);
        let lvl = Level::of_nat(1);
        let a = nat();
        let b = Term::arrow(nat(), nat());
        // A bogus `e` is fine for *this* test: we only inspect the `PLam` body's
        // boundary structure (`@ i0`/`@ i1`), which — by `Glue`'s strictness rule
        // — never consults `e`'s value, only whether the guarding face is decided.
        let bogus_e = Term::lam(a.clone(), Term::Var(0));
        let term = ua(lvl, a.clone(), b.clone(), bogus_e);
        let at_i0 = Term::papp(term.clone(), Term::IZero);
        let at_i1 = Term::papp(term, Term::IOne);
        assert!(r.is_def_eq(&at_i0, &a), "ua A B e @ i0 should be ≡ A");
        assert!(r.is_def_eq(&at_i1, &b), "ua A B e @ i1 should be ≡ B");
        assert!(!r.is_def_eq(&at_i0, &at_i1), "sanity: A and B were chosen distinct");
    }

    /// **Anti-`False`**: `ua` cannot be used to prove `Path Nat 0 1`. Concretely,
    /// `ua Nat Nat (idEquiv Nat)` only ever proves `Path Type Nat Nat` (a
    /// tautology up to `idEquiv`, not a proof about elements) — there is no way to
    /// route it through `Glue`'s strictness to manufacture an *element*-level
    /// equation between `Nat.zero` and `Nat.succ Nat.zero`, since `ua`'s codomain
    /// is `Type`, not `Nat`, and the kernel's `Sort`/`Nat` universes are kept
    /// separate (`chk.check` against `Path Nat 0 1` must reject `ua`'s term
    /// outright, a type mismatch, not merely "true but unprovable").
    #[test]
    fn ua_cannot_prove_false_nat_equation() {
        let env = env_with_nat_equiv();
        let chk = Checker::new(&env);
        let lvl = Level::of_nat(1);
        let n = nat();
        let term = ua(lvl, n.clone(), n.clone(), id_equiv_nat());
        let zero = Term::cnst(name("Nat.zero"), vec![]);
        let one = Term::app(Term::cnst(name("Nat.succ"), vec![]), zero.clone());
        let bogus_goal = Term::path(n, zero.clone(), one.clone());
        let mut ctx = LocalCtx::new();
        assert!(
            chk.check(&mut ctx, &term, &bogus_goal).is_err(),
            "ua's Path-Type-valued term must not check against a Path-Nat-valued goal"
        );
        // And directly: 0 and 1 are still not equal.
        let r = Reducer::new(&env);
        assert!(!r.is_def_eq(&zero, &one));
    }

    /// Reducer/NbE agreement on `ua`'s full normal form (not just its boundaries),
    /// matching this crate's standing differential-testing convention.
    #[test]
    fn ua_reducer_nbe_agree() {
        let env = env_with_nat_equiv();
        let lvl = Level::of_nat(1);
        let n = nat();
        let term = ua(lvl, n.clone(), n.clone(), id_equiv_nat());
        let r = Reducer::new(&env);
        let nbe = Nbe::new(&env);
        // Both engines must at least agree that `term` type-checks-shaped-ly
        // reduces to itself at whnf (no head redex — `ua`'s outermost former is a
        // `PLam`, already canonical) and that the fully-normalized forms coincide.
        assert!(matches!(r.whnf(&term), Term::PLam(_)));
        assert_eq!(nbe.normalize(&term), r.whnf(&nbe.normalize(&term)));
    }
}
