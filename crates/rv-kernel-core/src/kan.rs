//! **Phase 3** of the cubical build: the Kan operations — `transp` (transport along
//! a line of types) and `hcomp` (homogeneous composition, filling an open box).
//! Read `crate::cubical` (the interval `I`, `Path`/`PathP`, Phase 1) and
//! `crate::face` (cofibrations, `Sys`/`Partial`, Phase 2) first.
//!
//! # This phase ships a deliberately MINIMAL sound core
//!
//! This is the soundness-critical phase: the Kan operations define how types
//! *compute* under composition, and a wrong computation rule silently makes the
//! checker inconsistent (a derivable `Empty`/`False`). Real cubical type theory
//! (Cohen–Coquand–Huber–Mörtberg, "Cubical Type Theory: a constructive
//! interpretation of the univalence axiom") defines `transp`/`comp` by structural
//! recursion on the type former (`Π`, `Σ`, `PathP`, `Glue`, inductives, …), and the
//! `Π` case is **contravariant**: transporting a function's *argument* backwards
//! requires reversing the direction of the interval line (in CCHM this is the `~`
//! De Morgan connective; Cartesian systems without connections instead need a
//! *generalized* `coe`, parameterized by two arbitrary interval endpoints `r → r'`,
//! not just the fixed `i0 → i1` this task specifies).
//!
//! **This kernel's Phase 1 deliberately chose a Cartesian interval with no
//! De Morgan connectives** (see `crate::cubical`'s module doc, "Which interval").
//! That was the right call for Phase 1 (no Kan operations needed them yet), but it
//! means the textbook `Π`/`PathP` transport rules **cannot be written down here
//! without either (a) adding De Morgan reversal — a nontrivial, its-own-soundness-
//! burden extension explicitly out of scope for this pass, or (b) generalizing
//! `transp` to two arbitrary endpoints — a substantially larger redesign than "add
//! transp/hcomp to the existing i0→i1-only `Term::Transp`/`Term::HComp`". Neither is
//! achievable *and independently, adversarially soundness-checked* in this pass.
//!
//! Per the task's own instruction — "if the composition rules cannot be made
//! demonstrably sound within this pass, implement the largest sound subset (or
//! nothing), and report honestly" — this phase ships exactly the subset that
//! **is** demonstrably sound, and defers the rest. Concretely:
//!
//! * **`transp`** ([`crate::term::Term::Transp`]): only the **regularity rule** —
//!   transport along a family that is *structurally* independent of the interval
//!   variable is the identity. **No** per-type-former (Π/Σ/PathP) filling rule is
//!   implemented; a `transp` along a genuinely-varying family simply stays stuck
//!   (valid, inert data — like a neutral variable), rather than being given a
//!   wrong or partial computation rule.
//! * **`hcomp`** ([`crate::term::Term::HComp`]): only the **trivial-system rule** —
//!   when the guard `φ` is *decided* `⊤`, the composite is the system's value at
//!   `i1`. `hcomp`'s type argument is a single **fixed** type (not a family), so
//!   there is no Π/Σ/PathP-composition case to speak of here either — real cubical
//!   `hcomp` doesn't need one for a non-varying type; that structural recursion is
//!   only needed once `hcomp` is generalized to compose along a varying family
//!   (`comp`), which is explicitly deferred (see below).
//! * **`J`/derived `transport`/`subst`-based rewriting are NOT implemented** in
//!   this pass. The standard connection-free constructions of `J` from
//!   `transp`+`hcomp` (e.g. via contractibility of the based path space, built
//!   using an `hcomp`-filled square) are themselves delicate cubical arguments
//!   that this crate's own tests would need to adversarially re-derive to trust —
//!   attempting that construction on top of an admittedly-partial `transp` (no
//!   Π/PathP case) is exactly the kind of "ship something you can't stand behind"
//!   this task explicitly warns against. **Deferred, not shipped.**
//!
//! This is a real, if narrow, payoff: the regularity rule alone already gives
//! `Path`'s `refl`/`funext`/`ap` (Phase 1) a genuine (if restricted) computational
//! transport — `transp (λ_. A) φ a` is the identity, checked and adversarially
//! tested below — and every well-formedness/erasure/unification pass in the
//! untrusted elaborator (`rv-kernel`) now knows how to structurally traverse the
//! two new term formers, so a later pass can extend the *reduction* rules (in
//! `reduce.rs`/`nbe.rs` only) without another crate-wide plumbing pass.
//!
//! # A soundness bug caught and fixed *during* this pass
//!
//! An earlier draft of this phase additionally fired `transp`'s identity rule
//! whenever `φ` was *decided* `⊤` (mirroring `hcomp`'s trivial rule, and a literal
//! reading of the task's phrasing "whenever φ = ⊤, transp is the identity"). **This
//! is unsound** and was reverted before landing: `φ` is bookkeeping metadata
//! checked only for well-formedness (`Checker::infer`'s `Term::Transp` arm calls
//! `check_cof_wellformed`, nothing else) — it is never required to actually
//! *entail* that `family` is constant. Concretely, given an (entirely legal, if
//! perhaps individually inconsistent — no different from any other axiom) axiom
//! `p : Path (Sort n) A B` for two distinct closed types `A`/`B`, the family
//! `family := p @ Var(0)` genuinely varies (`family[i:=i0] ≡ A`, `family[i:=i1] ≡
//! B`, by the Phase-1 `path_boundary` rule) yet is a perfectly well-typed line of
//! types. `transp family ⊤ a` for `a : A` would then — under the *now-reverted*
//! rule — reduce straight to `a`, while `Checker::infer` independently reports its
//! type as `family[i:=i1] ≡ B`: a value of (real, checked) type `A` masquerading,
//! by a wrong reduction rule, as a value of type `B`. That is precisely the kind
//! of silent inconsistency this task's priorities rank above all else. The fix:
//! **the reduction rule never consults `φ`** — only the purely structural
//! `!mentions_var(family, 0)` check fires the identity rule (see the adversarial
//! test [`kernel_tests::transp_along_a_type_level_path_axiom_does_not_smuggle_a_type_change`]
//! below, which pins exactly this scenario down as "stays stuck", not "wrongly
//! reduces"). `hcomp`'s `φ = ⊤` rule has **no** analogous problem and was kept
//! as-is — see the soundness argument below for why.
//!
//! # Soundness argument
//!
//! ## `transp`'s regularity rule is sound
//!
//! `Checker::infer`'s `Term::Transp(family, φ, a)` arm requires `a : family[i:=i0]`
//! and reports the result type as `family[i:=i1]`. The **only** reduction rule
//! (`reduce::Reducer::whnf`/`nbe::Nbe::eval`, differentially tested) fires when
//! `family` does not mention the bound interval variable at all
//! (`!mentions_var(family, 0)`, a purely syntactic check on the *raw*, unevaluated
//! term). [`Term::subst`]'s own definition makes this airtight: substituting *any*
//! replacement for `Var(0)` in a term that contains no free `Var(0)` occurrence
//! never actually touches the replacement value — every other free variable is
//! simply shifted down by one, identically regardless of what's being substituted
//! in. So when the rule fires, `family[i:=i0]` and `family[i:=i1]` are not merely
//! *convertible* — they are the **literal same term** (both equal "`family` with
//! its free variables shifted down by one"). Consequently `a`'s checked type
//! (`family[i:=i0]`) and the `Transp` node's inferred type (`family[i:=i1]`) are
//! syntactically identical whenever the rule can fire, so reducing to `a` never
//! changes what type the result is considered to have. When `family` *does*
//! mention the interval variable, the term simply never reduces (stays stuck, a
//! valid normal form, exactly like an unresolved `Sys`) — this cannot manufacture
//! any new equation, for the same reason Phase 2's stuck `Sys` can't (see
//! `crate::face`'s soundness argument, point 3).
//!
//! ## `hcomp`'s trivial-system rule is sound
//!
//! `Checker::infer`'s `Term::HComp(ty, φ, u, u0)` arm type-checks `u` (under an
//! interval binder) against `Partial φ ty` **with `ty` held fixed** — this
//! minimal `hcomp` is *homogeneous* in the strongest sense: it does not even
//! accept a *family* of types, only one fixed `ty`, so there is no `A(i0)` vs
//! `A(i1)` mismatch to worry about in the first place (contrast `transp`, which
//! risked exactly that and is why its `φ=⊤` shortcut was unsound). It additionally
//! requires the cap agreement `u[i:=i0] ≡ u0` **unconditionally** (not only when
//! `φ` holds — a strictly *stronger*, and hence still-sound, requirement than the
//! textbook rule, at the cost of accepting fewer programs). The one reduction
//! rule fires only when `φ` is *decided* `⊤` (`crate::face::is_true`, the same
//! decision procedure Phase 2's `Sys` reduction already trusts), producing
//! `u[i:=i1]`. By the admissible substitution property of a checked derivation
//! (if `Γ, i:I ⊢ u : Partial φ ty` then `Γ ⊢ u[i:=r] : Partial φ[i:=r] ty` for any
//! well-typed `r : I` — an ordinary substitution lemma, not something this phase
//! introduces) `u[i:=i1]` is exactly as well-typed as `u` was; and since `ty`
//! never varies, there is no former-specific filling needed to land back at `ty`.
//! Every attempt to construct a counterexample (see the adversarial tests below,
//! in particular routing an *opaque* `Partial`-typed axiom through `u`) is blocked
//! by the *combination* of the independent `check(u0, ty)` and
//! `is_def_eq(u[i:=i0], u0)` obligations, both already-sound primitives.
//!
//! ## Neither rule adds a new source of equations between unrelated closed terms
//!
//! The structural `compare`/`is_def_eq`/`conv` cases added for `Transp`/`HComp`
//! (in `check.rs`/`reduce.rs`/`nbe.rs`) are exactly as conservative as Phase 1/2's
//! (component-wise structural equality, `φ` up to `crate::face::cof_equiv`) — they
//! can only equate two `Transp`/`HComp` nodes that already agree on every
//! component, never a `Transp`/`HComp` with an unrelated term.
//!
//! # What's deferred (explicitly, and why)
//!
//! * **Per-type-former `Π`/`Σ`/`PathP` transport/composition.** Blocked by the
//!   Cartesian-interval design (see above) for `Π` specifically; `Σ`/`PathP` are
//!   in principle derivable without reversal (covariant), but implementing *only*
//!   those without `Π` would produce an asymmetric, easy-to-misuse partial
//!   feature (transport works through half your type formers and silently
//!   doesn't through the other half) for a single-pass addition that couldn't
//!   also get the adversarial scrutiny this task demands — deferred as a unit.
//! * **`comp`** (composition along a *varying* family) — needs the same
//!   per-former recursion as `transp`'s general case, so inherits the same block.
//! * **`J`, derived `transport : Path Type A B -> A -> B`, `subst`-based
//!   rewriting.** All standard derivations route through either the general
//!   `Π`/`PathP` Kan rules or an hcomp-filled square whose own well-typedness
//!   argument this crate would need to re-derive from scratch — deferred rather
//!   than risking an under-scrutinized "payoff" construction.
//! * **`Glue`/univalence, De Morgan connections, Kan ops for user inductives/HITs**
//!   — out of scope for this task already, unaffected by this phase.
//!
//! None of this is wired to look complete: `Term::pretty` renders `transp`/`hcomp`
//! plainly, erasure (`rv_kernel::erase`) explicitly *errors* rather than silently
//! treating them as opaque (see `erase.rs`'s `Term::Transp | Term::HComp` arm),
//! and this module's doc is the single place documenting exactly how far the
//! implementation goes.

#[cfg(test)]
mod kernel_tests {
    use crate::face::Cof;
    use crate::kernel::Kernel;
    use crate::term::{name, Term};

    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    /// `A B : Type 0`, `a b c : A`.
    fn base_env() -> Kernel {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("B", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        k.add_axiom("b", 0, cn("A")).unwrap();
        k.add_axiom("c", 0, cn("A")).unwrap();
        k
    }

    // ---- transp: the regularity rule ----

    /// `transp (λ_. A) ⊥ a : A` and definitionally reduces to `a` — the core
    /// payoff of this phase.
    #[test]
    fn transp_along_a_constant_family_typechecks_and_is_the_identity() {
        let k = base_env();
        let fam = cn("A").lift(1, 0); // doesn't mention the new interval binder
        let t = Term::transp(fam, Cof::bot(), cn("a"));
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &cn("A")));
        assert!(k.def_eq(&t, &cn("a")));
    }

    /// Same, but with `φ = ⊤` — the guard's value must not matter for a genuinely
    /// constant family (it still reduces, since regularity never looks at `φ`).
    #[test]
    fn transp_along_a_constant_family_is_the_identity_regardless_of_phi() {
        let k = base_env();
        let fam = cn("A").lift(1, 0);
        let t = Term::transp(fam, Cof::top(), cn("a"));
        assert!(k.def_eq(&t, &cn("a")));
    }

    /// Differential check (this crate's standing convention): the trusted reducer
    /// and NbE agree on the regularity reduction.
    #[test]
    fn transp_regularity_agrees_between_reducer_and_nbe() {
        let k = base_env();
        let fam = cn("A").lift(1, 0);
        let t = Term::transp(fam, Cof::bot(), cn("a"));
        let reducer = crate::reduce::Reducer::new(k.env());
        let nbe = crate::nbe::Nbe::new(k.env());
        assert!(reducer.is_def_eq(&t, &cn("a")));
        assert!(nbe.conv(&t, &cn("a")));
    }

    /// `check` also accepts `transp` at its reduced form's type (not just `infer`).
    #[test]
    fn transp_along_a_constant_family_checks_against_a() {
        let k = base_env();
        let fam = cn("A").lift(1, 0);
        let t = Term::transp(fam, Cof::bot(), cn("a"));
        k.check(&t, &cn("A")).unwrap();
    }

    /// Sanity: a definition built from `transp` survives the independent recheck
    /// harness (mirrors Phase 1/2's equivalent coverage).
    #[test]
    fn transp_definitions_survive_independent_recheck() {
        let mut k = base_env();
        let fam = cn("A").lift(1, 0);
        k.add_definition("ta", 0, cn("A"), Term::transp(fam, Cof::bot(), cn("a"))).unwrap();
        assert_eq!(crate::kernel::recheck_all_definitions(k.env()).unwrap(), 1);
    }

    // ---- transp: adversarial soundness tests ----

    /// **Adversarial**: a `transp` whose family genuinely varies (mentions the
    /// interval variable) stays **stuck** — it must NOT reduce to `a` (that would
    /// be exactly the unsound shortcut this module's doc describes and reverted).
    /// Built via `p @ Var(0)` for an axiomatized `p : Path (Sort 1) A B` (i.e. `A`
    /// and `B`, both `: Type 0`, connected by an — individually opaque, like any
    /// axiom — path *in the universe*).
    #[test]
    fn transp_along_a_type_level_path_axiom_does_not_smuggle_a_type_change() {
        let mut k = base_env();
        // p : Path (Type 0's own sort) A B  (A B : Type 0, i.e. both `: Sort 1`).
        k.add_axiom("p", 0, Term::path(Term::typ(0), cn("A"), cn("B"))).unwrap();
        let fam = Term::papp(cn("p").lift(1, 0), Term::Var(0));
        // Sanity: this family genuinely mentions the interval variable, and its
        // endpoints are (via the Phase-1 boundary rule) A and B respectively —
        // otherwise this wouldn't be exercising the case at all.
        assert!(crate::term::mentions_var(&fam, 0));
        let fam_i0 = fam.instantiate(&Term::IZero);
        let fam_i1 = fam.instantiate(&Term::IOne);
        assert!(k.def_eq(&fam_i0, &cn("A")));
        assert!(k.def_eq(&fam_i1, &cn("B")));

        let t = Term::transp(fam, Cof::top(), cn("a"));
        // It still type-checks (infer succeeds, `a : A` matches `fam[i:=i0] ≡ A`)…
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &cn("B")));
        // …but it must NOT reduce to `a` (which has type `A`, not `B`) — the
        // reducer/NbE must leave it stuck, not silently launder a type change.
        let reducer = crate::reduce::Reducer::new(k.env());
        let nbe = crate::nbe::Nbe::new(k.env());
        assert!(!reducer.is_def_eq(&t, &cn("a")));
        assert!(!nbe.conv(&Term::app(Term::lam(cn("B"), Term::Var(0)), t.clone()).unfold_apps().0, &cn("a")));
        // Directly: whnf leaves the head as a stuck `Transp`, not `a`.
        let whnf = reducer.whnf(&t);
        assert!(matches!(whnf, Term::Transp(..)), "expected a stuck Transp, got {}", whnf.pretty());
    }

    /// **Adversarial**: no closed, non-stuck term of `Path Type A B` can itself be
    /// *constructed* from `a : A` alone (this is really Phase 1's guarantee, but
    /// re-confirmed here since `transp` is the thing that would try to *use* such
    /// a path if one existed) — `refl` only ever proves reflexivity, so `A` and
    /// `B` (distinct axioms) stay unrelated absent an explicit (opaque, axiom-only)
    /// postulate.
    #[test]
    fn no_path_between_distinct_types_is_derivable_without_an_axiom() {
        let k = base_env();
        assert!(!k.def_eq(&cn("A"), &cn("B")));
        assert!(k
            .check(&crate::cubical::refl(&cn("A")), &Term::path(Term::typ(1), cn("A"), cn("B")))
            .is_err());
    }

    /// **Adversarial**: `transp` cannot manufacture a proof of `Path A a b` for
    /// distinct closed `a`/`b` (i.e. it doesn't let you sidestep Phase 1's
    /// "no `False`" guarantee for ordinary paths either) — since `transp`'s only
    /// firing rule is the identity, the result is always def-eq to the very `a`
    /// you started with; it can never produce a *different* closed value.
    #[test]
    fn transp_never_produces_a_value_other_than_its_own_input() {
        let k = base_env();
        let fam = cn("A").lift(1, 0);
        let t = Term::transp(fam, Cof::bot(), cn("a"));
        assert!(k.def_eq(&t, &cn("a")));
        assert!(!k.def_eq(&t, &cn("b")));
        assert!(!k.def_eq(&t, &cn("c")));
    }

    /// **Adversarial**: `transp`'s declared source type is enforced — you cannot
    /// check `a : A` as if it already had a *different*, unrelated type by
    /// wrapping it in `transp` with a mismatched claimed source.
    #[test]
    fn transp_source_type_mismatch_is_rejected() {
        let k = base_env();
        // family is (lifted) B, but `a : A` — a genuine mismatch, no path involved.
        let fam = cn("B").lift(1, 0);
        let t = Term::transp(fam, Cof::bot(), cn("a"));
        assert!(k.infer(&t).is_err());
    }

    // ---- hcomp: the trivial-system rule ----

    /// `hcomp A ⊤ (⟨i⟩ a) a : A` and reduces to `a` (the single-branch, always-on
    /// system case).
    #[test]
    fn hcomp_with_top_guard_reduces_to_the_lines_value_at_i1() {
        let k = base_env();
        // `u`'s type is `Partial φ A`, only ever inhabited by a `Sys` (see
        // `crate::face`) — `⟨i⟩ [⊤ ↦ a]`, a constant line built through a system.
        let u = Term::sys(vec![(Cof::top(), cn("a").lift(1, 0))]);
        let t = Term::hcomp(cn("A"), Cof::top(), u, cn("a"));
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &cn("A")));
        assert!(k.def_eq(&t, &cn("a")));
    }

    /// A genuinely varying (but still well-typed and cap-agreeing) line: `⟨i⟩
    /// [(i=i0)↦a, (i=i1)↦b]`— wait, that wouldn't cap-agree with `a` unless `a ≡
    /// b`. Use `[⊤ ↦ a]` reshaped so the line is trivially `a` at every point but
    /// built through a `Sys`, exercising `Sys`-inside-`hcomp` end to end.
    #[test]
    fn hcomp_line_built_from_a_system_reduces_correctly() {
        let k = base_env();
        let u = Term::sys(vec![(Cof::top(), cn("a").lift(1, 0))]);
        let t = Term::hcomp(cn("A"), Cof::top(), u, cn("a"));
        assert!(k.def_eq(&t, &cn("a")));
    }

    /// Differential check: reducer and NbE agree on the trivial `hcomp` rule.
    #[test]
    fn hcomp_trivial_rule_agrees_between_reducer_and_nbe() {
        let k = base_env();
        let u = Term::sys(vec![(Cof::top(), cn("a").lift(1, 0))]);
        let t = Term::hcomp(cn("A"), Cof::top(), u, cn("a"));
        let reducer = crate::reduce::Reducer::new(k.env());
        let nbe = crate::nbe::Nbe::new(k.env());
        assert!(reducer.is_def_eq(&t, &cn("a")));
        assert!(nbe.conv(&t, &cn("a")));
    }

    /// Sanity: an `hcomp`-built definition survives the independent recheck
    /// harness.
    #[test]
    fn hcomp_definitions_survive_independent_recheck() {
        let mut k = base_env();
        let u = Term::sys(vec![(Cof::top(), cn("a").lift(1, 0))]);
        k.add_definition("ha", 0, cn("A"), Term::hcomp(cn("A"), Cof::top(), u, cn("a"))).unwrap();
        assert_eq!(crate::kernel::recheck_all_definitions(k.env()).unwrap(), 1);
    }

    // ---- hcomp: well-formedness / adversarial tests ----

    /// The cap-agreement obligation (`u[i:=i0] ≡ u0`) is enforced — a line whose
    /// value at `i0` disagrees with the supplied cap is rejected.
    #[test]
    fn hcomp_rejects_a_cap_mismatch() {
        let k = base_env();
        let u = cn("b").lift(1, 0); // constant line ⟨i⟩ b
        let t = Term::hcomp(cn("A"), Cof::top(), u, cn("a")); // cap claims `a`, line is `b`
        assert!(k.infer(&t).is_err());
    }

    /// `hcomp` with `φ = ⊥` (an empty system) still requires a well-typed `u`/`u0`
    /// pair (cap agreement is required *unconditionally* — see the module doc for
    /// why this stricter-than-textbook rule keeps the design simple and sound) but
    /// never *reduces* (no branch is ever decided true) — it stays stuck, valid
    /// inert data, exactly like an unresolved `Sys`.
    #[test]
    fn hcomp_with_bot_guard_typechecks_but_stays_stuck() {
        let k = base_env();
        // `⊥` trivially entails the coverage obligation for *any* branches, so a
        // `⊤`-guarded (i.e. always-reducible-once-forced) line still checks fine
        // against `Partial ⊥ A` — but the outer `hcomp`'s own guard (`⊥`) is what
        // gates the *hcomp* reduction rule, and that's never decided true.
        let u = Term::sys(vec![(Cof::top(), cn("a").lift(1, 0))]);
        let t = Term::hcomp(cn("A"), Cof::bot(), u, cn("a"));
        k.infer(&t).unwrap(); // well-typed (cap agrees: ⟨i⟩[⊤↦a] at i0 reduces to a)
        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&t);
        assert!(matches!(whnf, Term::HComp(..)), "expected a stuck HComp, got {}", whnf.pretty());
    }

    /// **Adversarial**: `hcomp` cannot conjure an inhabitant of an unrelated,
    /// otherwise-uninhabited axiom type `E` — the only way to populate `u0`/`u` is
    /// with an already-well-typed-at-`E` term, and there is none to reuse (`a` is
    /// at the wrong type `A`, not `E`).
    #[test]
    fn hcomp_cannot_conjure_an_inhabitant_of_an_unrelated_axiom() {
        let mut k = base_env();
        k.add_axiom("E", 0, Term::typ(0)).unwrap();
        let u = cn("a").lift(1, 0); // `a : A`, not `: E`
        let t = Term::hcomp(cn("E"), Cof::top(), u, cn("a"));
        assert!(k.infer(&t).is_err());
    }

    /// **Adversarial**: routing an opaque axiom of `Partial`-type through `hcomp`
    /// (attempting to sidestep the cap check by aliasing `u` and `u0` to the very
    /// same free-standing neutral) is rejected — `u0`'s independent `check(u0,
    /// ty)` obligation fails since the axiom's own type is `Partial ⊤ A`, not `A`
    /// (see the module doc's `hcomp` soundness argument for the general case).
    #[test]
    fn hcomp_opaque_partial_typed_axiom_cannot_bypass_the_cap_check() {
        let mut k = base_env();
        k.add_axiom("q", 0, Term::partial(Cof::top(), cn("A"))).unwrap();
        let u = cn("q").lift(1, 0); // doesn't mention the interval binder
        let t = Term::hcomp(cn("A"), Cof::top(), u, cn("q")); // u0 := q, at the wrong type
        assert!(k.infer(&t).is_err());
    }

    /// **Adversarial**: two structurally-distinct `hcomp` terms (different caps)
    /// are not equated merely by both being *some* `hcomp` of the same type — the
    /// structural `compare`/`is_def_eq` cases stay componentwise.
    #[test]
    fn distinct_hcomp_terms_are_not_conflated() {
        let k = base_env();
        let ua = cn("a").lift(1, 0);
        let ub = cn("b").lift(1, 0);
        let ta = Term::hcomp(cn("A"), Cof::top(), ua, cn("a"));
        let tb = Term::hcomp(cn("A"), Cof::top(), ub, cn("b"));
        assert!(!k.def_eq(&ta, &tb));
    }

    /// **Adversarial**: `I` still cannot be smuggled through `transp`/`hcomp` as a
    /// `Π` domain or as ordinary data (mirrors Phase 1/2's equivalent checks) —
    /// this phase adds no new way to make `I` fibrant.
    #[test]
    fn interval_still_cannot_be_a_pi_domain_with_kan_ops_in_scope() {
        let mut k = Kernel::new();
        let err = k.add_axiom("bad", 0, Term::pi(Term::I, Term::typ(0))).unwrap_err();
        assert!(err.contains('I'), "got: {err}");
    }

    /// **Adversarial**: `transp`'s guard `φ` must still be a genuine cofibration
    /// over interval-classified subjects — it cannot smuggle ordinary data through
    /// an atom's subject position (mirrors `Partial`'s equivalent check).
    #[test]
    fn transp_rejects_a_non_interval_cofibration_subject() {
        let k = base_env();
        let fam = cn("A").lift(1, 0);
        let bad_phi = Cof::eq0(cn("a")); // `a : A`, not `: I`
        let t = Term::transp(fam, bad_phi, cn("a"));
        assert!(k.infer(&t).is_err());
    }
}
