//! **Phase 1** of the cubical build: the interval `I` and `Path`/`PathP` types,
//! *without* Kan operations (`transp`/`hcomp`/`comp`/`glue`/faces — all deferred to a
//! later phase). This module is doc-comments-first: read it before touching
//! [`crate::term::Term::I`]/[`Term::IZero`]/[`Term::IOne`]/[`Term::PLam`]/
//! [`Term::PApp`]/[`Term::PathP`] or [`crate::check::Checker`]'s handling of them.
//!
//! # Which interval: Cartesian, not De Morgan
//!
//! Phase 1 implements the **simplest sound choice**: a *Cartesian* interval — just the
//! two endpoints `i0`/`i1` and interval *variables* — with **no** De Morgan connection
//! structure (`_∧_`, `_∨_`, `~_`). Those lattice operations exist to support Kan
//! composition/`hcomp` (they're what makes the "cube" a cube with faces you can fill);
//! since this phase deliberately excludes Kan entirely, there is nothing for them to
//! do yet, and adding them now would just be unused surface area with its own
//! (nontrivial — De Morgan laws must hold *definitionally*) soundness burden. A later
//! Kan phase can add them without disturbing anything here.
//!
//! # Representation: interval variables reuse the ordinary `Var` binder
//!
//! A naive design gives interval variables their own de Bruijn *namespace* (a second
//! counter, parallel to `Term::Var`), which then needs its own `lift`/`subst` pair
//! threaded through every existing binder, and its own value environment in the NbE
//! evaluator. Phase 1 avoids all of that: [`Term::PLam`] (path abstraction, `⟨i⟩ t`)
//! binds its interval variable using the **same** `Var`/de-Bruijn machinery as
//! [`Term::Lam`] — the bound `i` inside `t` really is `Term::Var(0)`, shifted by
//! `Term::lift`/`Term::instantiate` exactly like any other bound variable. The only
//! difference from an ordinary binder is that [`crate::check::LocalCtx`] records the
//! phantom [`Term::I`] as that binder's "type" (via `ctx.with(Term::I, ...)`) instead
//! of a real sort. This is what makes `I` **not fibrant**: `infer(Term::I)` is
//! rejected outright (see [`crate::check::Checker::infer`]'s `Term::I` arm), so a
//! `Term::I` can never itself be checked as a `Π`/`λ` domain or codomain — nothing can
//! quantify a genuine `Type` over the interval, which is exactly the "no transport
//! yet" restriction Phase 1 needs.
//!
//! The payoff: every existing `lift`/`subst`/`subst_ctx`/`instantiate_levels`/
//! `has_meta` case for `Var` needed **no new logic**, and the NbE evaluator's existing
//! `Var`/`VEnv`/closure infrastructure evaluates and quotes path abstractions the same
//! way it does ordinary lambdas (see [`crate::nbe::Value::PLam`]). The only genuinely
//! new machinery is: (1) [`crate::check::Checker`]'s four new `infer` cases
//! (`I`/`IZero`/`IOne` are trivial; `PLam`/`PApp`/`PathP` mirror `Lam`/`App`/`Pi`); (2)
//! one new β-rule in both [`crate::reduce::Reducer::whnf`] and
//! [`crate::nbe::Nbe::vpapp`] (differentially cross-checked, matching this crate's
//! existing convention for every other computation rule); (3) structural
//! definitional-equality cases in both conversion checkers.
//!
//! # The one computation rule, and its Phase-1 boundary
//!
//! ```text
//!   (⟨i⟩ t) @ i0  ↦  t[i := i0]
//!   (⟨i⟩ t) @ i1  ↦  t[i := i1]
//!   (⟨i⟩ t) @ r   ↦  t[i := r]     (general β, r any interval term)
//! ```
//!
//! `PathP`'s well-formedness check (in `Checker::infer`'s `Term::PathP` arm) requires
//! the two declared endpoints to be *definitionally equal* to the family instantiated
//! at `i0`/`i1` — not syntactically identical — so "the boundary holds by conversion"
//! for anything actually built through `PLam` (directly, or via a `Const` that
//! δ-unfolds to one): `whnf` unfolds through `Let`/`Const`/`Lam`/ι/ν/etc. exactly as it
//! always did, and *then* fires the `PApp` rule once the head reaches a literal
//! `PLam`.
//!
//! **The boundary equation also holds for neutral `p`** — not just a literal `PLam` —
//! via a second, *type-directed* rule in [`crate::check::Checker::path_boundary`]
//! (checked from [`crate::check::Checker::compare`], the authoritative conversion):
//! for any `p` whose *inferred* type is `PathP (λi. A) a0 a1` (a bound variable, an
//! axiom, a stuck application — anything), `p @ i0 ≡ a0` and `p @ i1 ≡ a1`
//! definitionally, because `a0`/`a1` are exactly the endpoints that `p`'s `PathP` type
//! was *already checked against* (`Checker::infer`'s `Term::PathP` arm — see above).
//! This mirrors real cubical type theory (`p i0` reduces for *any* `p : Path A a0 a1`,
//! not only literal path abstractions) and is what lets the derived `funext`/`ap`
//! below type-check at their *stated*, fully general types even when composed with an
//! abstract/neutral path hypothesis (see `ap_boundaries_compute`,
//! `funext_typechecks`). It is exactly analogous to [proof
//! irrelevance](crate::check::Checker::proof_irrelevant) — another type-directed
//! equation the purely structural reducer/NbE conversion can't express, added only at
//! the authoritative [`crate::check::Checker::compare`] layer, not in the lower-level
//! [`crate::reduce::Reducer::is_def_eq`]/[`crate::nbe::Nbe::conv`] (which stay purely
//! structural — the differential tests below only compare those two against each
//! other on the literal-`PLam` β-rule, which both of them do implement identically).
//!
//! This is still strictly conservative: it introduces **no new equation** beyond what
//! a prior, independently-checked typing judgement already forced. See soundness
//! point 3 below.
//!
//! # Soundness argument: Path (without Kan) proves nothing new
//!
//! Phase 1 cannot be used to derive `False` (or equate any two distinct closed
//! values) that the pre-existing kernel couldn't already derive. Sketch:
//!
//! 1. **No transport.** The only way to move a term from one type to another in this
//!    kernel is via conversion (`is_def_eq`) — there is no `J`/`transp`/`subst`
//!    operator over `Path`/`PathP` in Phase 1 (that's the Kan phase). So a `Path A a
//!    b` witness can never be *used* to turn a value at type `A` into a value at some
//!    other type, or to rewrite one side of an unrelated goal — it just sits there as
//!    inert data.
//! 2. **Conservative extension of conversion.** The new definitional-equality cases
//!    added to `reduce::is_def_eq`/`check::compare`/`nbe::alpha_eta_eq` are purely
//!    *structural* (`PLam ≡ PLam` iff bodies `≡`, `PathP ≡ PathP` iff components `≡`,
//!    `IZero ≡ IZero`, …) plus the one β-rule above, plus the type-directed
//!    `path_boundary` rule (see above). None of them can make two pre-existing
//!    (non-Path) terms equal that weren't already: the structural cases are additive
//!    branches in a `match` over the *new* constructors only (a `Sort`/`Pi`/`Lam`/
//!    application/etc. is still only ever compared against another term of the same
//!    head shape, exactly as before this change — every pre-Phase-1 test in the
//!    existing 586-test suite is byte-for-byte unaffected, since no old term can ever
//!    contain a new constructor), and `path_boundary` only ever equates `p @ i0`/`p @
//!    i1` with the endpoint *already recorded in `p`'s own previously-checked type* —
//!    it cannot introduce an equation between two terms that weren't already tied
//!    together by an earlier, independent typing judgement.
//! 3. **Closing a `Path` requires an actual proof.** `Checker::infer`'s `Term::PLam`
//!    arm *computes* the endpoints as `body.instantiate(&IZero)`/`instantiate(&IOne)`
//!    — they are not asserted, they are read off the body you supplied. So
//!    `PLam(body) : Path A a b` only type-checks when `body[i:=i0]` and `body[i:=i1]`
//!    are *literally* (up to the kernel's existing, already-sound conversion) `a` and
//!    `b`. There is no way to write a `PLam` whose type lies about its endpoints (see
//!    the adversarial test `plam_cannot_lie_about_its_endpoints` below) — this is
//!    exactly parallel to how `refl : Eq a a` can't be abused to prove `Eq a b` for
//!    distinct `a`,`b` in the pre-existing `Eq`/inductive-equality machinery.
//! 4. **`I` can't smuggle data.** Since `infer(I)` errors, no `Π`/`λ` can be built
//!    with `I` as a domain or codomain, so an interval variable can never flow into a
//!    position that expects a real `Type`-classified value (e.g. it can't be handed to
//!    a function expecting `Nat`, or used as a motive) — `is_def_eq` would have to
//!    equate `I` with that function's declared domain type, and the structural cases
//!    added above only equate `I` with `I`.
//!
//! Net effect: Phase 1 is exactly what the task calls it — "a conservative
//! presentation of a reflexive/congruent relation with definitional endpoints". The
//! adversarial tests below exercise points 3 and 4 directly, plus the boundary
//! computation itself and the derived `refl`/`funext`/`ap` terms.
//!
//! # What's deferred to later (Kan) phases
//!
//! `transp`/`J`-for-`Path` (transporting along a path), `hcomp`/`comp` (composition —
//! filling an open box), `Glue` types, and face formulas/systems (`[φ ↦ u]`,
//! partial elements) are **all out of scope here**. They are exactly the pieces that
//! turn `Path` from inert data into something that can move proofs between types —
//! i.e. exactly the pieces whose soundness this module's argument depends on
//! *excluding*.

use crate::face::Cof;
use crate::level::Level;
use crate::term::{name, Term};

// ============================================================================
// Phase 3.5: the De Morgan interval — connections, reversal, and definitional
// normalization.
// ============================================================================
//
// Phase 1 (above) deliberately stopped at a *Cartesian* interval: `i0`/`i1` and
// variables only, no `∧`/`∨`/`~`. This phase adds them, as [`Term::INeg`]/
// [`Term::IMeet`]/[`Term::IJoin`], and — the hard part — a definitional equality on
// interval expressions that validates the free **De Morgan algebra** laws:
//
// ```text
//   ~i0 = i1                    ~i1 = i0                    ~~r = r
//   ~(r∧s) = ~r ∨ ~s            ~(r∨s) = ~r ∧ ~s            (De Morgan duality)
//   r∧r = r,  r∨r = r           (idempotence)
//   r∧s = s∧r,  r∨s = s∨r       (commutativity)
//   (r∧s)∧t = r∧(s∧t), similarly for ∨   (associativity)
//   r∧(r∨s) = r,  r∨(r∧s) = r   (absorption)
//   r∧i0 = i0,  r∨i1 = i1,  r∧i1 = r,  r∨i0 = r   (bounded lattice)
// ```
//
// # Why *De Morgan*, not *Boolean*
//
// A **Boolean** algebra would additionally satisfy the complement laws `r ∧ ~r = i0`
// and `r ∨ ~r = i1`. The interval of cubical type theory does **not** satisfy these —
// geometrically, `i ∧ ~i` is *not* the constant `i0` line, it is a genuinely
// nontrivial path in the interval (`i0` at both endpoints `i=0` and `i=1`, but `i0`
// itself only at those two points — think of `i ∧ ~i` as the "tent function" hitting
// `i1`-ish behaviour only conceptually nowhere: concretely it is `i0` at `i=0` and at
// `i=1`, but it is a *distinct term* from the literal constant `i0` at every other
// point of the abstract syntax, and, crucially, nothing in the free algebra forces it
// to reduce to `i0`). Treating `r ∧ ~r = i0` as a definitional law would be **unsound**:
// it would let `transp`/face-lattice reasoning (a later/adjacent phase) treat two
// genuinely different open boxes as the same closed one, collapsing distinctions a
// model of cubical sets does not identify. This module's normal form is exactly the
// canonical form of the *free bounded distributive lattice with a De Morgan
// involution* on the interval variables — the standard semantic model (de Morgan
// frames / the cubical interval presheaf `□`) — and `normalize_interval` decides
// **exactly** those laws, deliberately no more. [`tests::the_boolean_law_does_not_hold`]
// pins this down adversarially.
//
// # The normal form
//
// An interval expression built from `{Var, IZero, IOne, INeg, IMeet, IJoin}` is first
// put in **negation-normal form** (NNF) by pushing every `~` down to the variables
// via the De Morgan/double-negation laws (so the only place `INeg` can survive is
// directly wrapping a `Var`) — this uses the De Morgan and double-negation laws
// *by construction*, not as a check. The NNF tree (built from `Var`, `~Var`, `i0`,
// `i1`, `∧`, `∨`) is then flattened to a **disjunctive normal form**: a finite set of
// *clauses*, each clause a finite set of *literals* (a literal being `Var(i)` or
// `~Var(i)`), representing `⋁ⱼ ⋀ᵢ lit(i,j)`. `i0` is the empty disjunction (no
// clauses); `i1` is the disjunction of the empty conjunction (one clause, no
// literals). `∧`/`∨` combine clause-sets exactly like [`crate::face::to_dnf`]'s
// `Cof` DNF (same distributive-lattice algorithm — the interval and the cofibration
// lattice share this shape), **except** there is no `self_contradictory` pruning: a
// clause containing both `Var(i)` and `~Var(i)` is *not* dropped (that pruning is
// exactly the Boolean law this module must NOT assume). Finally the clause set is
// **minimized** (duplicate clauses removed, and any clause that is a superset of
// another clause's literals is dropped — the absorption law, `r∧(r∨s)=r`) and put in
// a canonical sorted order. Two interval terms are De Morgan-equal iff their
// normal forms (as clause sets) are identical — this is exactly deciding equality in
// the free distributive lattice with De Morgan involution, a standard and terminating
// procedure (finite terms ⇒ finite variable set ⇒ finite clause universe).
//
// [`normalize_interval`] is **total**: every arm of the match handles its case
// directly (no partial function, no panics), and the DNF/minimization passes only
// ever grow-then-shrink finite `Vec`s — no unbounded recursion (`INeg` recurses into
// one strictly smaller subterm; `IMeet`/`IJoin` each into two).

/// A literal: `Var(i)` (`negated = false`) or `~Var(i)` (`negated = true`).
type Lit = (usize, bool);
/// A clause: a finite, sorted, deduplicated set of literals (the empty clause is the
/// vacuous conjunction, `i1`).
type Clause = Vec<Lit>;

/// Negation-normal form, as a clause-set (disjunctive normal form) directly — pushes
/// `~` to the variables and distributes `∧`/`∨` in the same pass. `neg` tracks whether
/// the enclosing context has applied an odd number of reversals (so this doubles as
/// the De Morgan/double-negation reduction: `nnf_dnf(~t, neg)` is just
/// `nnf_dnf(t, !neg)`, no separate pass needed).
fn nnf_dnf(t: &Term, neg: bool) -> Vec<Clause> {
    match t {
        Term::IZero => {
            if neg {
                vec![vec![]]
            } else {
                vec![]
            }
        }
        Term::IOne => {
            if neg {
                vec![]
            } else {
                vec![vec![]]
            }
        }
        Term::INeg(r) => nnf_dnf(r, !neg),
        Term::IMeet(r, s) => {
            let (a, b) = (nnf_dnf(r, neg), nnf_dnf(s, neg));
            if neg { dnf_or(&a, &b) } else { dnf_and(&a, &b) }
        }
        Term::IJoin(r, s) => {
            let (a, b) = (nnf_dnf(r, neg), nnf_dnf(s, neg));
            if neg { dnf_and(&a, &b) } else { dnf_or(&a, &b) }
        }
        // Base case: a variable (or, for a malformed/non-interval subterm reached
        // defensively, treated as an opaque atom keyed by its own structural identity
        // via a synthetic index derived from nothing else being available — see the
        // `Term::Var` case below, the only one that can arise in a well-typed interval
        // expression; anything else falls through to the conservative default in
        // [`normalize_interval`], which never calls this helper).
        Term::Var(i) => vec![vec![(*i, neg)]],
        // Defensive: not a real interval expression. Treat as an indivisible atom so
        // the function stays total; `normalize_interval` never routes a non-interval
        // term here (see its own fallback), so this arm is unreachable in practice.
        _ => vec![vec![(usize::MAX, neg)]],
    }
}

/// DNF conjunction: pointwise-union every pair of clauses (**no** `i≠~i`
/// contradiction pruning — see the module doc for why that Boolean law must not be
/// assumed here).
fn dnf_and(a: &[Clause], b: &[Clause]) -> Vec<Clause> {
    let mut out = Vec::new();
    for ca in a {
        for cb in b {
            let mut merged = ca.clone();
            for lit in cb {
                if !merged.contains(lit) {
                    merged.push(*lit);
                }
            }
            out.push(merged);
        }
    }
    out
}

/// DNF disjunction: concatenate clause sets.
fn dnf_or(a: &[Clause], b: &[Clause]) -> Vec<Clause> {
    let mut out = a.to_vec();
    out.extend(b.iter().cloned());
    out
}

/// Canonicalize a clause: sort+dedup its literals.
fn canon_clause(c: &Clause) -> Clause {
    let mut c = c.clone();
    c.sort_unstable();
    c.dedup();
    c
}

/// Minimize a clause set: canonicalize each clause, drop duplicate clauses, and drop
/// any clause that is a (non-strict) superset of another — the absorption law
/// `r ∧ (r ∨ s) = r` says the smaller (more general) clause subsumes the larger (more
/// specific) one. Finally sort the clause set for a canonical `Vec` order.
fn minimize(clauses: Vec<Clause>) -> Vec<Clause> {
    let mut cs: Vec<Clause> = clauses.into_iter().map(|c| canon_clause(&c)).collect();
    cs.sort();
    cs.dedup();
    let mut out: Vec<Clause> = Vec::new();
    'outer: for (i, c) in cs.iter().enumerate() {
        for (j, d) in cs.iter().enumerate() {
            if i != j && d.iter().all(|lit| c.contains(lit)) && d.len() < c.len() {
                // some *other*, strictly smaller clause `d` is a subset of `c` ⇒ `c`
                // is absorbed (r∧(r∨s)=r): drop `c`.
                continue 'outer;
            }
        }
        out.push(c.clone());
    }
    out
}

/// Rebuild a canonical clause-set back into a `Term` (a join of meets of `Var`/`~Var`
/// literals), so [`normalize_interval`]'s result is directly comparable by ordinary
/// structural [`Term`] equality (`PartialEq`) — two De Morgan-equal interval
/// expressions normalize to *identical* `Term`s.
fn clauses_to_term(clauses: &[Clause]) -> Term {
    if clauses.is_empty() {
        return Term::IZero; // the empty disjunction is ⊥ of the lattice, i.e. `i0`.
    }
    let mut disj: Option<Term> = None;
    for clause in clauses {
        let mut conj: Option<Term> = None;
        for &(i, negated) in clause {
            let lit = if negated { Term::ineg(Term::Var(i)) } else { Term::Var(i) };
            conj = Some(match conj {
                None => lit,
                Some(c) => Term::imeet(c, lit),
            });
        }
        let clause_term = conj.unwrap_or(Term::IOne); // empty conjunction = ⊤ = i1
        disj = Some(match disj {
            None => clause_term,
            Some(d) => Term::ijoin(d, clause_term),
        });
    }
    disj.unwrap()
}

/// Is `t` built purely from the interval-expression grammar (`Var`/`IZero`/`IOne`/
/// `INeg`/`IMeet`/`IJoin`)? [`normalize_interval`] only canonicalizes such terms; any
/// other term is returned unchanged (see its doc for why that fallback is safe).
pub fn is_interval_expr(t: &Term) -> bool {
    match t {
        Term::Var(_) | Term::IZero | Term::IOne => true,
        Term::INeg(r) => is_interval_expr(r),
        Term::IMeet(r, s) | Term::IJoin(r, s) => is_interval_expr(r) && is_interval_expr(s),
        _ => false,
    }
}

/// **Definitional normalization of interval expressions.** Puts `t` in the canonical
/// normal form of the free De Morgan algebra (see the module doc): a join-of-meets of
/// `Var`/`~Var` literals, minimized and canonically ordered. Total: falls through to
/// returning `t.clone()` unchanged for anything that isn't a pure interval expression
/// (this is safe/conservative — see [`interval_eq`], the only caller that matters for
/// soundness: it only invokes this on subterms that are *already* required to have
/// inferred type `I`, i.e. that can only ever have been built from this grammar in a
/// well-typed term in the first place, per `crate::cubical`'s and `crate::check`'s
/// typing rules for [`Term::INeg`]/[`Term::IMeet`]/[`Term::IJoin`]/[`Term::PApp`]'s
/// argument/[`crate::face::Atom`]'s subject).
pub fn normalize_interval(t: &Term) -> Term {
    if !is_interval_expr(t) {
        return t.clone();
    }
    clauses_to_term(&minimize(nnf_dnf(t, false)))
}

/// Definitional equality of two interval expressions, up to the De Morgan algebra
/// laws (see the module doc). This is the routing point [`crate::check::Checker`]'s
/// `compare`, [`crate::reduce::Reducer`]'s `is_def_eq`, and [`crate::nbe::Nbe`]'s
/// conversion all call for any subterm that is interval-classified (a [`Term::PApp`]
/// argument, or an atom subject in [`crate::face`]) — see those modules' `PApp`/`Cof`
/// cases.
pub fn interval_eq(a: &Term, b: &Term) -> bool {
    normalize_interval(a) == normalize_interval(b)
}

/// `refl a : Path A a a` — the constant path `⟨i⟩ a` (the body doesn't mention `i`, so
/// it's `a` lifted past the new binder, exactly like [`Term::arrow`]'s non-dependent
/// codomain). A one-line *definitional* fact once `Path` exists, in contrast to the
/// quotient-derived `Eq`/`refl` already in the kernel (see `crate::quotient`), which is
/// an axiomatized computation rule rather than something `Path`'s own reduction gives
/// for free.
pub fn refl(a: &Term) -> Term {
    Term::plam(a.lift(1, 0))
}

/// `funext h : Path (Π x:A. B x) f g`, given `h : Π x:A. Path (B x) (f x) (g x)`.
/// Built as `⟨i⟩ λx. (h x) @ i` — swap the two binders of `h`'s pointwise paths for one
/// path of functions. `dom` is `A`, the shared domain of `f`/`g`/`h`'s telescope.
///
/// This is the *definitional* one-liner Phase 1's `Path` enables directly (no
/// computation rule needs to be axiomatized/derived for it — contrast the
/// quotient-derived `install_funext` schema elsewhere in the kernel, which exists
/// precisely because `Eq` there has no such direct proof).
pub fn funext(dom: &Term, h: &Term) -> Term {
    Term::plam(Term::lam(
        dom.lift(1, 0),
        Term::papp(Term::app(h.lift(2, 0), Term::Var(0)), Term::Var(1)),
    ))
}

/// `ap f p : Path B (f a) (f b)`, given `f : A -> B` and `p : Path A a b`. Built as
/// `⟨i⟩ f (p @ i)` — push `f` under the path.
pub fn ap(f: &Term, p: &Term) -> Term {
    Term::plam(Term::app(f.lift(1, 0), Term::papp(p.lift(1, 0), Term::Var(0))))
}

// ============================================================================
// Phase 3.7: `transport`/`subst`, and the `Path ↔ Eq` bridge.
// ============================================================================
//
// `crate::kan`'s Phase 3 shipped `transp`'s **regularity** rule: transport along a
// family that does not mention the interval variable is (definitionally) the
// identity. That is already enough — with **no new checking or reduction rule** —
// to derive the two classic Kan payoffs as plain `Term`-builders, exactly the way
// [`refl`]/[`funext`]/[`ap`] above are plain builders over `PLam`/`PApp`:
//
// * [`transport`]: `Π (A B : Type). Path Type A B → A → B`, specialized to a
//   concrete `p : Path Type A B` and `a : A` (mirroring how [`refl`]/[`ap`] above
//   take their already-elaborated arguments rather than re-abstracting the
//   universals — the universals are recovered from `p`'s/`a`'s own inferred types
//   at the call site, exactly as an elaborator would fill them in).
// * [`subst`]: `Π (A) (P : A → Type) (a b : A). Path A a b → P a → P b`, the
//   transport of a *predicate* along a path — same idea, one level up (`P`
//   supplies the varying family instead of `Path Type` itself).
//
// Both are literally `transp (λ i. ⟨family built from the path⟩) ⊥ ⟨input⟩` — the
// `family` argument to the existing, unmodified [`crate::term::Term::transp`]. No
// new primitive, no new reduction rule: `Checker::infer`'s `Term::Transp` arm (see
// `crate::kan`) is exactly what type-checks these, unchanged.
//
// # Completeness gap (not a soundness one): `refl` doesn't collapse
//
// `crate::kan`'s regularity rule fires only when the family is *syntactically*
// (structurally, `!mentions_var`) independent of the interval variable. For
// `transport (refl A) a`, the family is `λ i. (refl A) @ i`, which — even though
// `refl A`'s body doesn't depend on `i` at the *meta* level — is still, as a raw
// term, `PApp(PLam(A-lifted), Var(0))`: it *does* mention `Var(0)` syntactically
// (as the `PApp`'s argument), so `!mentions_var` is false and the identity rule
// does **not** fire; only the *literal-PLam* β-rule reduces `(refl A) @ i` down to
// `A` first (a `whnf`/`nbe` step *inside* the family, which the top-level
// `!mentions_var` syntactic check never performs — it inspects the family's own
// un-reduced head, not its head-normal form). So `transport (refl A) a` type-checks
// at exactly `A` (`family[i:=i0] ≡ family[i:=i1] ≡ A` by conversion — the boundary
// still holds *definitionally*, just not via the *original, purely syntactic* half
// of the `Transp` regularity β-rule alone). **This gap is now closed**:
// `crate::kan::family_is_constant`'s normalization-aware extension (see its doc)
// computes the family under a fresh neutral for the interval variable and finds it
// genuinely constant here, so `transport (refl A) a` now reduces, definitionally, to
// `a` — see [`tests::transport_along_refl_now_computes_to_its_input`] below, and the
// same gap closing for the Π-family analogue,
// `crate::kan`'s `transp_pi_rule_typechecks_on_a_refl_connected_pi_family` test.
//
// # The `Path ↔ Eq` bridge
//
// [`path_to_eq`]/[`eq_to_path`] connect this cubical layer to the *inductive*
// `Eq` (`crate::inductive::declare_eq`) the rest of the corpus (`examples/proofs/
// *.rv`) is built on:
//
// * [`path_to_eq`] is `subst (λ x. Eq A a x) p (Eq.refl A a)` — literally an
//   instance of [`subst`] above, no new machinery.
// * [`eq_to_path`] eliminates `Eq A a b` (via `Eq.rec`) into the motive
//   `λ (x:A) (_:Eq A a x). Path A a x`, with `refl a : Path A a a` as the
//   `Eq.refl`-case — this is the standard "J only needs *one* endpoint, the other
//   is `Eq`'s own index" trick; it needs no `hcomp`/box-filling because it's an
//   elimination of the *inductive* `Eq` (already a first-class recursor in this
//   kernel — see `crate::inductive::declare_eq`), not of `Path` itself (cubical `J`
//   for `Path`, which *would* need `hcomp`, stays deferred).
//
// `Eq`'s declared signature (see `crate::inductive::declare_eq`): `Eq.{u} : Π
// (A:Sort u) (a b:A). Prop` (so `Eq A a b` itself always lives in `Prop`,
// regardless of `u`), `Eq.refl.{u} : Π (A:Sort u)(a:A). Eq A a a`, and
// `Eq.rec.{u,v} : Π (A:Sort u)(a:A)(motive: Π(b:A). Eq A a b → Sort v)(refl_case:
// motive a (Eq.refl A a))(b:A)(h:Eq A a b). motive b h`. [`eq_to_path`] instantiates
// `Eq.rec`'s `v` at the **same** level `u` as `A` itself: `Path A a b`'s own sort is
// exactly `A`'s sort (`Checker::infer`'s `Term::PathP` arm reports `Sort(infer_sort
// (family))`, and the constant family `λ_.A` has the same sort as `A`) — see
// [`eq_to_path`]'s doc for the concrete level bookkeeping.
//
// # Soundness
//
// Every one of these four functions is, definitionally, nothing but
// [`crate::term::Term::transp`] (already proven sound in `crate::kan`) or
// `Eq.rec` (an unmodified, pre-existing inductive recursor whose ι-rule is exactly
// as sound as `Nat.rec`'s) wrapped in ordinary `Lam`/`App`/substitution — **no new
// checking or reduction rule is added by this section**, so type-preservation and
// canonicity are inherited, not re-argued. The adversarial tests below (in
// `tests::bridge`) re-run this crate's standing "no `False`" attacks through the
// new combinators specifically: `transport`/`subst` between two *closed, unrelated*
// axiom types are constructible **only** given an actual `Path Type A B` witness
// (which itself requires an axiom or a real proof — Phase 1's `refl` only proves
// reflexivity, see `crate::cubical`'s own soundness argument above), and
// `path_to_eq (refl a)`/`eq_to_path (Eq.refl a)` land at the *reflexive* endpoint,
// never a distinct one.

/// `transport p a : B`, given `p : Path Type A B` and `a : A` — moves `a` across a
/// path *in the universe* using nothing but the existing `transp` primitive:
/// `transp (λ i. p @ i) ⊥ a`. The boundary is exactly what makes this type-check:
/// `(λi. p@i)[i:=i0] ≡ p@i0 ≡ A` and `[i:=i1] ≡ p@i1 ≡ B`, both by Phase 1's
/// `path_boundary` rule (see the module doc above) — `Checker::infer`'s `Term::Transp`
/// arm (`crate::kan`) then reports the result type as exactly `B`.
///
/// `φ` is passed as `⊥` (`Cof::bot()`): per `crate::kan`'s own established
/// convention, `Transp`'s reduction rule never consults `φ`, so `⊥` is simply
/// always a well-formed placeholder (this is also literally the task's own stated
/// definition, `transp (λ i. p @ i) ⊥ a`).
pub fn transport(p: &Term, a: &Term) -> Term {
    let family = Term::papp(p.lift(1, 0), Term::Var(0));
    Term::transp(family, Cof::bot(), a.clone())
}

/// `subst motive p pa : P b`, given `motive = P : A → Type`, `p : Path A a b`, and
/// `pa : P a` — transports a *predicate* along a path: `transp (λ i. P (p @ i)) ⊥
/// pa`. Same shape as [`transport`], one level up: the varying family here is `P`
/// applied to the moving point `p @ i`, rather than `p @ i` itself.
pub fn subst(motive: &Term, p: &Term, pa: &Term) -> Term {
    let moving_point = Term::papp(p.lift(1, 0), Term::Var(0));
    let family = Term::app(motive.lift(1, 0), moving_point);
    Term::transp(family, Cof::bot(), pa.clone())
}

/// `path_to_eq level a_ty a p : Eq a_ty a b`, given `p : Path a_ty a b` — derived
/// via [`subst`] at the motive `λ x. Eq A a x`, starting from `Eq.refl A a : Eq A a
/// a`: `subst (λ x. Eq A a x) p (Eq.refl A a)`. `level` is `Eq`'s own universe
/// parameter (`u` in `Eq.{u} : Π (A:Sort u) …` — see `crate::inductive::declare_eq`),
/// i.e. the level at which `a_ty` itself is classified (`a_ty : Sort level`).
pub fn path_to_eq(level: Level, a_ty: &Term, a: &Term, p: &Term) -> Term {
    let eq_cnst = |args: [Term; 3]| Term::apps(Term::cnst(name("Eq"), vec![level.clone()]), args);
    // motive := λ (x : a_ty). Eq a_ty a x   (a_ty/a lifted past the new binder)
    let motive =
        Term::lam(a_ty.clone(), eq_cnst([a_ty.lift(1, 0), a.lift(1, 0), Term::Var(0)]));
    let refl_a =
        Term::apps(Term::cnst(name("Eq.refl"), vec![level]), [a_ty.clone(), a.clone()]);
    subst(&motive, p, &refl_a)
}

/// `eq_to_path level a_ty a b h : Path a_ty a b`, given `h : Eq a_ty a b` — the
/// converse bridge, built by eliminating `h` (via `Eq.rec`) into the motive `λ (x :
/// a_ty) (_ : Eq a_ty a x). Path a_ty a x` (constant in the `Eq`-proof argument),
/// with [`refl`]`(a) : Path a_ty a a` as the `Eq.refl`-case. This needs no
/// `hcomp`/box-filling — it is an elimination of the *inductive* `Eq` (an ordinary,
/// pre-existing recursor), not cubical `J` for `Path` itself (which — the task
/// explicitly defers — would need `hcomp`).
///
/// `level` instantiates *both* of `Eq.rec`'s universe parameters (`u` for `A`
/// itself, `v` for the motive's target sort) at the same value: `Path a_ty a x`'s
/// own sort is exactly `a_ty`'s sort (`Checker::infer`'s `Term::PathP` arm reports
/// `Sort(infer_sort(family))`, and the constant family `λ_. a_ty` has, by
/// definition, the same sort as `a_ty` itself) — so the motive's target sort `v`
/// and `A`'s own sort `u` coincide here, both equal to `level`.
pub fn eq_to_path(level: Level, a_ty: &Term, a: &Term, b: &Term, h: &Term) -> Term {
    let eq_cnst = |args: [Term; 3]| Term::apps(Term::cnst(name("Eq"), vec![level.clone()]), args);
    // motive := λ (x : a_ty) (_ : Eq a_ty a x). Path a_ty a x
    //   under [a_ty]:            a_ty=Var? -- built directly at the right frame.
    let motive = Term::lam(
        a_ty.clone(),
        Term::lam(
            eq_cnst([a_ty.lift(1, 0), a.lift(1, 0), Term::Var(0)]),
            Term::path(a_ty.lift(2, 0), a.lift(2, 0), Term::Var(1)),
        ),
    );
    let refl_case = refl(a);
    Term::apps(
        Term::cnst(name("Eq.rec"), vec![level.clone(), level]),
        [a_ty.clone(), a.clone(), motive, refl_case, b.clone(), h.clone()],
    )
}

// ============================================================================
// Phase 3.9: `J` (path induction) for cubical `Path`, as a derived `transport` term.
// ============================================================================
//
// `J : Π (A:Type) (a:A) (C: Π(x:A). Path A a x → Type) (d: C a (refl a)) (x:A)
//        (p: Path A a x). C x p`
//
// Standard CCHM construction (cross-checked against cubical Agda's `Cubical.
// Foundations.Prelude.J`, which defines it exactly this way from `transp`):
//
// ```text
//   J A a C d x p := transport (⟨i⟩ C (p @ i) (⟨j⟩ p @ (i ∧ j))) d
// ```
//
// i.e. `transp` along the line of *types* `i ↦ C (p @ i) (connect i)`, where
// `connect i := ⟨j⟩ p @ (i ∧ j)` is the **connection square**: the partial path
// from `a` to `p @ i` obtained by meeting the outer `i` with `p`'s own bound
// variable `j`.
//
// * At `i = i0`: `connect i0 = ⟨j⟩ p @ (i0 ∧ j)`. `i0 ∧ j` normalizes (by
//   [`normalize_interval`]'s bounded-lattice law `r ∧ i0 = i0`) to the literal
//   `i0`, so [`crate::check::Checker::path_boundary`] (the type-directed boundary
//   rule — see the module doc above) fires on `p @ (i0 ∧ j)` exactly as it would on
//   `p @ i0`, resolving it to `a` (the declared left endpoint of `p`'s own,
//   already-checked `Path` type) regardless of `p`'s syntactic shape. So `connect
//   i0`'s *body* is (definitionally) `a`, independent of `j` — matching `refl a`'s
//   body — and the family's `i0` boundary is `C a (refl a)`, exactly `d`'s type.
// * At `i = i1`: `connect i1 = ⟨j⟩ p @ (i1 ∧ j)`. `i1 ∧ j` normalizes to the literal
//   `j` (`r ∧ i1 = r`), so `connect i1`'s body is `p @ j` — i.e. `connect i1` is
//   `p`'s own **η-expansion** `⟨j⟩ p @ j`. The family's `i1` boundary is therefore
//   `C x (⟨j⟩ p @ j)`, which is `C x p` up to Path-η. This kernel's conversion
//   checker does not carry a *general* (neutral-`p`) η-rule for `PLam` (only
//   structural `PLam ≡ PLam` and, separately, ordinary `Lam` η — see
//   `Checker::compare`) — but for any `p` whose *own* body already routes its bound
//   variable straight through a `PApp` argument position (the case for every
//   concretely-built path in this corpus: `refl`, `ap`, `funext`, and any path
//   assembled from them), `⟨j⟩ p @ (i1 ∧ j)` reduces the *same way* `p` itself was
//   built, and `IMeet(IOne, Var(0))` vs `Var(0)` is compared via the dedicated
//   De-Morgan-normal-form arm of `compare` (both sides are pure interval
//   expressions — see [`interval_eq`]) rather than needing a fresh eta rule. See
//   `j_typechecks_on_refl`/`j_typechecks_on_a_composite_path` below, which exercise
//   this on concrete, non-axiomatized paths and confirm the full stated type
//   checks. A fully *opaque*/axiomatized `p` additionally needs a genuine,
//   unconditional Path-η law — `check::Checker::compare`/`nbe::alpha_eta_eq` now
//   carry exactly that (the interval-binder analogue of the pre-existing `Lam`-η
//   rule: `q ≡ ⟨j⟩ q @ j` for *any* `q : PathP`, literal `PLam` or neutral), so
//   `⟨j⟩ p @ (i1 ∧ j)` is recognized as equal to `p` itself even when `p` is
//   opaque. See `j_typechecks_on_an_opaque_axiomatized_path`/
//   `trans_typechecks_on_opaque_axiomatized_paths` below, which exercise this on
//   genuinely axiomatized (non-`PLam`) paths and confirm the full stated type
//   checks even without any concrete path structure to reduce against.
//
// This needs **no new checking or reduction rule**: `J` is nothing but
// [`Term::transp`] (already proven sound in `crate::kan`) applied to a family built
// entirely from [`Term::plam`]/[`Term::papp`]/[`Term::imeet`] (already proven sound
// above, Phase 1 and Phase 3.5) — exactly the same "derived term, not a new
// primitive" shape as [`transport`]/[`subst`] in Phase 3.7.
//
// # Computation on `refl`
//
// `J A a C d a (refl a)` **does** now reduce to `d`, definitionally. The family here
// is `λi. C ((refl a) @ i) (⟨j⟩ (refl a) @ (i ∧ j))`, which syntactically mentions
// `Var(0)` (as `PApp` arguments), so the *original*, purely syntactic half of
// `Transp`'s regularity rule (`crate::kan`, fires only when the family is
// syntactically independent of the interval variable) does not apply on its own —
// but `crate::kan::family_is_constant`'s normalization-aware extension *computes*
// the family under a fresh neutral for `Var(0)` and finds it collapses to the
// constant `C a (refl a)` (both `(refl a) @ i` and `⟨j⟩ (refl a) @ (i∧j)` β/η-reduce
// away every occurrence of the interval variable), so the rule fires and
// `J A a C d a (refl a)` reduces straight to `d`. See `j_on_refl_now_computes_to_d`
// below.
//
// # Soundness
//
// `J` cannot conjure `C x p` without an actual `p : Path A a x` and `d : C a (refl
// a)` — it is literally `transp`, whose `Checker::infer` rule (`crate::kan`)
// unconditionally requires `check(ctx, d, family.instantiate(&IZero))` to succeed,
// i.e. `d` must genuinely inhabit the family's `i0` boundary; there is no way to
// bypass that check. In particular there is no closed instantiation of `J`'s type
// variables that derives `Path Nat 0 1` (or any other `False`-shaped goal): doing so
// would require first supplying a closed `p : Path Nat 0 1`, which — per this
// module's own Phase-1 soundness argument (point 3, "closing a `Path` requires an
// actual proof") — cannot itself be constructed from nothing. The adversarial tests
// below (`j_cannot_manufacture_a_path_between_unrelated_axioms_from_nothing`, etc.)
// exercise this directly.
pub fn j(c: &Term, d: &Term, p: &Term) -> Term {
    // The family, built under one interval binder (`i = Var(0)`), matching
    // `Term::transp`'s calling convention (see `transport`/`subst` above, which are
    // built the identical way).
    let p_at_i = Term::papp(p.lift(1, 0), Term::Var(0)); // p @ i
    // connect := ⟨j⟩ p @ (i ∧ j) — built under a second interval binder (`j =
    // Var(0)`; the outer `i` is now `Var(1)`).
    let connect = Term::plam(Term::papp(p.lift(2, 0), Term::imeet(Term::Var(1), Term::Var(0))));
    let family = Term::app(Term::app(c.lift(1, 0), p_at_i), connect);
    Term::transp(family, Cof::bot(), d.clone())
}

// ============================================================================
// Phase 3.11: `trans` (path concatenation/transitivity), as a derived `J` term.
// ============================================================================
//
// `trans ty a c p q : Path ty a c`, given `p : Path ty a b` and `q : Path ty b c`
// (`b` is *inferred*, exactly like `J`'s own `x` — it is read off `p`'s checked
// type, not supplied as an argument). Standard `J`-based construction (this exact
// shape already appeared, hand-inlined and hard-wired to a fixed axiom `A`, as a
// private test helper `trans` in this module's `#[cfg(test)] mod tests` above —
// generalized here to an arbitrary `ty`/`a`/`c`, as a public combinator other
// modules can build on): eliminate `p : Path ty a b` with motive
//
// ```text
//   C := λ (y:ty) (_:Path ty a y). Path ty y c → Path ty a c
// ```
//
// base case `d := λ (r:Path ty a c). r` (at `y = a`, `C a (refl a)` is
// definitionally `Path ty a c → Path ty a c`, and the identity function inhabits
// exactly that), giving `J ty a C d b p : Path ty b c → Path ty a c`; applying that
// to `q` gives the result. Exactly [`j`] applied to a purpose-built motive — **no
// new checking or reduction rule**, so it inherits `j`'s (hence `transp`'s, hence
// `crate::kan`'s) soundness argument verbatim: `trans` cannot produce a `Path ty a
// c` without two actual path witnesses `p`/`q` genuinely composing end-to-end (`J`'s
// underlying `transp` unconditionally requires `d`'s type to match the family's
// `i0` boundary — there is no way around that check).
pub fn trans(ty: &Term, a: &Term, c: &Term, p: &Term, q: &Term) -> Term {
    // motive, ctx []: λ (y:ty) (_:Path ty a y). Path ty y c → Path ty a c
    let motive = Term::lam(
        ty.clone(),
        Term::lam(
            // ctx [y]: Path ty a y (ty/a lifted past the fresh `y` binder)
            Term::path(ty.lift(1, 0), a.lift(1, 0), Term::Var(0)),
            // ctx [y,_]: Path ty y c → Path ty a c (ty/a/c lifted past both binders)
            Term::arrow(
                Term::path(ty.lift(2, 0), Term::Var(1), c.lift(2, 0)),
                Term::path(ty.lift(2, 0), a.lift(2, 0), c.lift(2, 0)),
            ),
        ),
    );
    // d := λ (r:Path ty a c). r — the identity function at `C a (refl a)`.
    let d = Term::lam(Term::path(ty.clone(), a.clone(), c.clone()), Term::Var(0));
    Term::app(j(&motive, &d, p), q.clone())
}

// ============================================================================
// Phase 3.12: `trans3` (three-way path composition) — needed because *nesting*
// [`trans`] (i.e. feeding one `trans`-built term back in as the *subject* of a
// further `J`-elimination) does not type-check in this kernel: `trans`'s output is
// an `App(Transp(..), _)`-headed term, and the path-η rule that lets `J` eliminate
// an *opaque* subject (see `j`'s own module-doc section, "Payoff of path-η") does
// not, empirically, extend to that shape — confirmed directly (three axiomatized
// paths `p:w=x`, `q:x=y`, `r:y=z`; `trans(trans(p,q),r)` fails to type-check with a
// boundary mismatch inside the *second* `J`'s connection square, even though
// `trans(p,q)` alone infers exactly `Path A w y`; see this crate's `equiv_hae`
// module's own diagnostic test, `debug_nested_trans_hits_the_documented_completeness_gap`, kept in that
// module as the concrete record of this obstruction). This is a *completeness*
// gap, not a soundness one — `J`/`transp` themselves are unmodified and no new
// equation is introduced — but it does mean "just call `trans` twice" is not
// available for building 3-way (or longer) compositions.
//
// [`trans3`] works around it by eliminating only the **first**, genuinely opaque
// path `p` via `J` (exactly [`trans`]'s own pattern, known to work — see
// [`j`]'s "Payoff of path-η" tests), with a motive whose *base case* itself calls
// [`trans`] on two **bound variables** (`q'`/`r'`, i.e. `Term::Var`s — themselves
// opaque/neutral in exactly the shape the path-η rule *does* handle, matching
// `j_typechecks_on_an_opaque_axiomatized_path`'s pattern) rather than on an
// already-`J`-built term. The `J`-elimination of `p` then produces a genuine
// **function** `Path ty n1 n2 → Path ty n2 d → Path ty a d`, which `q`/`r` are
// applied to via ordinary function application — never as the *subject* of a
// further `J`, so the problematic shape above never arises.
pub fn trans3(
    ty: &Term,
    a: &Term,
    // `n1` (`p`'s right endpoint) is *not* threaded into the term below: `j`
    // infers it directly from `p`'s own checked type (exactly like `trans`'s `b`,
    // which is likewise never passed explicitly) — kept as a named parameter
    // purely so the call site documents the full `a --p--> n1 --q--> n2 --r--> d`
    // chain it's building, matching this function's own doc.
    _n1: &Term,
    n2: &Term,
    d: &Term,
    p: &Term,
    q: &Term,
    r: &Term,
) -> Term {
    // motive, ctx []: λ (y:ty) (_:Path ty a y). Path ty y n2 → Path ty n2 d → Path ty a d
    let motive = Term::lam(
        ty.clone(),
        Term::lam(
            Term::path(ty.lift(1, 0), a.lift(1, 0), Term::Var(0)),
            Term::arrow(
                Term::path(ty.lift(2, 0), Term::Var(1), n2.lift(2, 0)),
                Term::arrow(
                    Term::path(ty.lift(2, 0), n2.lift(2, 0), d.lift(2, 0)),
                    Term::path(ty.lift(2, 0), a.lift(2, 0), d.lift(2, 0)),
                ),
            ),
        ),
    );
    // base case, ctx []: λ (q':Path ty a n2) (r':Path ty n2 d). trans ty a d q' r'
    // — `q'`/`r'` are the two *bound* variables `trans` is called on here (not a
    // previously-`J`-built term), matching the pattern already confirmed to work.
    let d1 = Term::lam(
        Term::path(ty.clone(), a.clone(), n2.clone()),
        Term::lam(
            Term::path(ty.lift(1, 0), n2.lift(1, 0), d.lift(1, 0)),
            trans(&ty.lift(2, 0), &a.lift(2, 0), &d.lift(2, 0), &Term::Var(1), &Term::Var(0)),
        ),
    );
    // j_res : Path ty n1 n2 → Path ty n2 d → Path ty a d  (`n1` is `p`'s own
    // checked right endpoint, inferred by `j` exactly like `trans`'s own `b`).
    let j_res = j(&motive, &d1, p);
    Term::app(Term::app(j_res, q.clone()), r.clone())
}

// ============================================================================
// Phase 4 (square tooling): 2-dimensional paths — "squares" — and the
// fundamental builders HoTT's naturality/`J` arguments need on top of them.
//
// A **square** at type `ty` with sides `top : Path ty a b`, `bottom : Path ty c
// d`, `left : Path ty a c`, `right : Path ty b d` is drawn
//
// ```text
//        top
//    a ------> b
//    |         |
// left|         |right
//    v         v
//    c ------> d
//      bottom
// ```
//
// and is *itself* a path — a genuinely 2-dimensional one — between `top` and
// `bottom`, living in the (interval-varying) type `Path ty (left@i) (right@i)`:
//
// ```text
//   Square ty top bottom left right :≡ PathP (λi. Path ty (left@i) (right@i)) top bottom
// ```
//
// This is nothing but `PathP`'s own type former applied one dimension up (see
// [`square_ty`]) — no new primitive, matching this module's "everything is
// `Path`/`PathP` plus already-proven-sound combinators" discipline.
//
// Builders landed here:
//   * [`square_ty`]      — the type former itself.
//   * [`const_square`]   — the totally-degenerate `refl`-square (all four sides
//     `refl a`, filled by `refl (refl a)`; needs no reduction beyond what
//     `idHAE`'s `tau` field already relies on).
//   * [`conn_and`]/[`conn_or`] — the two **connection squares** built from a
//     single path `p : Path ty a b` (`⟨i j⟩ p@(i∧j)` / `p@(i∨j)`), each with
//     two degenerate (`refl`) corners and two copies of `p` itself — the
//     squares `J`/homotopy-naturality arguments (HoTT §6.2/Lemma 2.4.3's own
//     textbook proof) build on.
//   * [`hcomp_square`]   — a square built from `Term::HComp` typed directly at
//     a `square_ty` goal. **Caveat, stated plainly**: `crate::kan`'s own module
//     doc ("Phase 3.8: the `PathP`-case `hcomp` filling rule — INVESTIGATED AND
//     DECLINED") records that only `hcomp`'s *trivial* (`φ = ⊤`) rule computes
//     at a `PathP` type — there is no general box-filling reduction rule for
//     `hcomp` at `PathP` in this kernel yet. [`hcomp_square`] therefore only
//     ever supplies `φ = ⊥` (so it reduces straight to the supplied total
//     filler `u0`, exactly like [`transport`]'s own `φ = ⊥` convention) — it is
//     useful for *typing* a fully-known square term at the `Square` goal via
//     the `HComp` primitive (rather than a bare `PathP`/`PLam`), not for
//     deriving new boundary data via genuine composition. A future pass wiring
//     up `crate::kan`'s declined `PathP`-case rule would let this combinator
//     (or a sibling) do real box-filling.
//   * [`nat_sq`]          — the **naturality square for a homotopy** (HoTT book
//     Lemma 2.4.3): given `H : Πx:A. Path B (f x) (g x)` and `p : Path A x y`,
//     `natSq H p : Square B (H x) (H y) (ap f p) (ap g p)`. This is the
//     keystone this whole phase exists for (see `crate::equiv_hae`'s module
//     doc, "Deferred: biInvToHAE" — `τ'` needs exactly two instances of this).
//     Built by a **single `J`-elimination on `p`** (exactly [`trans`]/
//     [`trans3`]'s own pattern) — **no `hcomp` needed**: when `p = refl x`,
//     `ap f (refl x)`/`ap g (refl x)` reduce (by [`ap`]'s own definition, PLam
//     applied to a constant path) to `refl (f x)`/`refl (g x)` *on the nose*,
//     collapsing the family `λi. Path B (ap f p @ i) (ap g p @ i)` at `y = x`,
//     `p = refl x` down to the **constant** type `Path B (f x) (g x)` — so the
//     base case is simply `refl (H x) : Path (Path B (f x) (g x)) (H x) (H
//     x)`, no square-combinator needed for the base case itself. This mirrors
//     `idHAE`'s own `tau := λa. refl (refl a)` trick (see `crate::equiv_hae`),
//     one `J`-step more general.
// ============================================================================

/// `square_ty ty top bottom left right : Type` — the type of a **square**
/// (see this section's module doc above for the picture/orientation):
/// `PathP (λi. Path ty (left@i) (right@i)) top bottom`. Exactly `PathP`'s own
/// type former, applied to a family built from `left`/`right`'s boundaries —
/// no new primitive.
pub fn square_ty(ty: &Term, top: &Term, bottom: &Term, left: &Term, right: &Term) -> Term {
    let family = Term::path(
        ty.lift(1, 0),
        Term::papp(left.lift(1, 0), Term::Var(0)),
        Term::papp(right.lift(1, 0), Term::Var(0)),
    );
    Term::pathp(family, top.clone(), bottom.clone())
}

/// `const_square a : Square ty (refl a) (refl a) (refl a) (refl a)` — the
/// totally degenerate square: `refl (refl a)`, i.e. `⟨i⟩⟨j⟩ a` (constant in
/// both dimensions). Checks purely by conversion/reduction: `square_ty`'s
/// family, instantiated with `left = right = refl a`, reduces (both `(refl
/// a)@i` boundaries are the constant `a`) to the constant type `Path ty a a`,
/// which `refl (refl a) : Path (Path ty a a) (refl a) (refl a)` inhabits
/// directly. Exactly `crate::equiv_hae::declare_id_hae`'s `tau_fn` pattern,
/// factored out as a standalone, reusable combinator.
pub fn const_square(a: &Term) -> Term {
    refl(&refl(a))
}

/// `conn_and ty a b p : Square ty (refl a) p (refl a) p`, given `p : Path ty a
/// b` — the "and"/`∧` **connection square** `⟨i⟩⟨j⟩ p @ (i ∧ j)`. Tracing the
/// four boundaries (see this section's module doc for the `top`/`bottom`/
/// `left`/`right` convention): at `i=i0`, `p@(i0∧j) ≡ p@i0 ≡ a` (constant) —
/// `top = refl a`; at `i=i1`, `p@(i1∧j) ≡ p@j` — `bottom = p`; at `j=i0`,
/// `p@(i∧i0) ≡ p@i0 ≡ a` — `left = refl a`; at `j=i1`, `p@(i∧i1) ≡ p@i` —
/// `right = p`. This is exactly the connection square [`j`]'s own `connect`
/// helper builds inline (see that function's body/doc) for `J`'s "payoff of
/// path-η" argument, exposed here as a standalone, independently-typeable
/// combinator so other constructions (e.g. [`nat_sq`]'s eventual callers) can
/// reuse it without re-deriving it.
pub fn conn_and(_ty: &Term, a: &Term, b: &Term, p: &Term) -> Term {
    let _ = (a, b); // endpoints are read off `p`'s own checked type by the caller;
    // kept as named parameters purely to document the intended `a`/`b`
    // boundary shape at the call site, matching this module's other
    // combinators' calling convention (e.g. `trans`'s `a`/`c`).
    Term::plam(Term::plam(Term::papp(p.lift(2, 0), Term::imeet(Term::Var(1), Term::Var(0)))))
}

/// `conn_or ty a b p : Square ty p (refl b) p (refl b)`, given `p : Path ty a
/// b` — the "or"/`∨` connection square `⟨i⟩⟨j⟩ p @ (i ∨ j)`, [`conn_and`]'s
/// dual: at `i=i0`, `p@(i0∨j) ≡ p@j` — `top = p`; at `i=i1`, `p@(i1∨j) ≡ p@i1
/// ≡ b` — `bottom = refl b`; at `j=i0`, `p@(i∨i0) ≡ p@i` — `left = p`; at
/// `j=i1`, `p@(i∨i1) ≡ p@i1 ≡ b` — `right = refl b`.
pub fn conn_or(_ty: &Term, a: &Term, b: &Term, p: &Term) -> Term {
    let _ = (a, b); // see `conn_and`'s identical note.
    Term::plam(Term::plam(Term::papp(p.lift(2, 0), Term::ijoin(Term::Var(1), Term::Var(0)))))
}

/// `hcomp_square ty top bottom left right filler : Square ty top bottom left
/// right`, given a fully-known `filler` already inhabiting exactly that
/// `Square` type — typed via `Term::HComp` (`φ = ⊥`, so it reduces straight to
/// `filler` itself) rather than a bare `PathP`/`PLam`. See this section's
/// module doc, [`hcomp_square`]'s own bullet, for the honest caveat: this is
/// **not** genuine box-filling (`crate::kan`'s `PathP`-case `hcomp` rule is
/// declined/unimplemented), just a way to route a square goal through the
/// `HComp` primitive.
pub fn hcomp_square(ty: &Term, top: &Term, bottom: &Term, left: &Term, right: &Term, filler: &Term) -> Term {
    let goal = square_ty(ty, top, bottom, left, right);
    Term::hcomp(goal, Cof::bot(), filler.lift(1, 0), filler.clone())
}

/// `nat_sq a_ty b_ty f g h x p : Square b_ty (h x) (h y) (ap f p) (ap g p)`,
/// given `h : Πz:a_ty. Path b_ty (f z) (g z)` (a homotopy `f ~ g`), `x : a_ty`,
/// and `p : Path a_ty x y` (`y` is inferred from `p`'s own checked type,
/// exactly like [`j`]/[`trans`]'s own trailing endpoint arguments) — the
/// **naturality square for a homotopy**, HoTT book Lemma 2.4.3. See this
/// section's module doc for the full derivation; in short: `J`-eliminate `p`
/// with motive `C := λ (y:a_ty) (q:Path a_ty x y). Square b_ty (h x) (h y) (ap
/// f q) (ap g q)`; at the base case `y=x`, `q=refl x`, `ap f (refl x)`/`ap g
/// (refl x)` reduce to `refl (f x)`/`refl (g x)`, collapsing `C x (refl x)`
/// down (by the constant-family/regularity route `crate::kan`'s
/// `family_is_constant` already provides, the same mechanism [`j`]'s own
/// "computation on `refl`" section documents) to the plain 1-path type `Path
/// (Path b_ty (f x) (g x)) (h x) (h x)`, which `refl (h x)` inhabits directly
/// — **no `hcomp`, no connection square, needed for `nat_sq` itself.**
pub fn nat_sq(a_ty: &Term, b_ty: &Term, f: &Term, g: &Term, h: &Term, x: &Term, p: &Term) -> Term {
    // motive, ctx []: λ (y:a_ty) (q:Path a_ty x y). Square b_ty (h x) (h y) (ap f q) (ap g q)
    let motive = Term::lam(
        a_ty.clone(),
        Term::lam(
            // ctx [y]: Path a_ty x y
            Term::path(a_ty.lift(1, 0), x.lift(1, 0), Term::Var(0)),
            {
                // ctx [y,q]: a_ty=+2, b_ty=+2, f=+2, g=+2, h=+2, x=+2; y=Var(1), q=Var(0)
                let hx = Term::app(h.lift(2, 0), x.lift(2, 0));
                let hy = Term::app(h.lift(2, 0), Term::Var(1));
                let ap_f_q = ap(&f.lift(2, 0), &Term::Var(0));
                let ap_g_q = ap(&g.lift(2, 0), &Term::Var(0));
                square_ty(&b_ty.lift(2, 0), &hx, &hy, &ap_f_q, &ap_g_q)
            },
        ),
    );
    // base case, ctx []: refl (h x) : Path (Path b_ty (f x) (g x)) (h x) (h x) —
    // matches `motive x (refl x)` up to the reductions this doc explains.
    let d = refl(&Term::app(h.clone(), x.clone()));
    j(&motive, &d, p)
}

// ============================================================================
// Phase 4.5 (groupoid laws): the standard ∞-groupoid coherences for [`trans`] —
// left/right unit and the two inverse laws — as `J`-derived 2-paths (HoTT book
// §2.1, Lemma 2.1.4). These are exactly the building blocks
// `crate::equiv_hae`'s `τ'` needs (see that module's doc, "Update -- the
// naturality-square keystone is now landed").
//
// # Left unit is *definitional*, not just propositional
//
// `trans ty a b (refl a) q` is, by [`trans`]'s own construction, `j(motive, d,
// refl a)` applied to `q`, where `d := λr. r`. `j` on a literal `refl a`
// subject is exactly the "computation on `refl`" case documented in [`j`]'s own
// module doc (Phase 3.9, "Computation on `refl`") — `crate::kan::
// family_is_constant`'s normalization-aware extension recognizes the family as
// constant at `i = i0`/`i1` alike and the whole `transp` collapses straight to
// `d`, no stuck neutral left over. So `trans ty a b (refl a) q` reduces, on the
// nose, to `(λr. r) q ≡ q` — meaning [`trans_left_unit`]'s statement holds by
// plain `refl`, no `J`-elimination needed at all.
//
// # Right unit, and the two inverse laws: CLOSED (a later pass fixed the
// underlying conversion-completeness gap)
//
// `trans` only ever eliminates its *first* path argument (`p`, not `q`), so
// `trans ty a b p (refl b)` does **not** reduce definitionally for opaque `p` —
// proving `trans p (refl b) ≡ p` needs its own `J`-elimination on `p`, with a
// motive that *itself* states the unit law, generalizing `b` to `p`'s own
// (variable) right endpoint `y` — exactly mirroring [`nat_sq`]'s own "eliminate
// the hypothesis path, let the *target* type vary with it" pattern. At the base
// case (`y = a`, `p = refl a`), the goal *should* collapse — by the
// *definitional* left-unit law above — to `Path (Path ty a a) (refl a) (refl
// a)`, provable by `refl (refl a)`. This used to get stuck: the required
// reduction needed the *outer* `j`-call's own `connect` term (see [`j`]'s doc)
// to reduce to `refl a` *underneath* an additional layer of `trans`/`transp`
// nesting these motives introduce, one layer deeper than [`nat_sq`]'s own
// "computation on `refl`" section alone accounts for. The root cause (see
// `crate::nbe::Nbe::family_is_constant_value`'s doc for the full diagnosis and
// fix): the *inner* nested `Transp`'s own regularity probe (`crate::kan::
// family_is_constant`, as invoked from `crate::nbe::Nbe::eval`) decided
// constancy by re-deriving its family from scratch against brand-new, mutually
// unrelated fresh neutrals for *every* free variable it mentioned — discarding
// the fact that, in the surrounding (lazy, closure-based) evaluation, those
// free variables were already bound by the *real* environment to concrete,
// related values (e.g. `y := p @ i0`, `q := refl y`) threaded down from the
// *outer* `J`. A family that only collapses given *those* particular
// substitutions — not for arbitrary unrelated ones — was invisible to the old,
// disconnected probe. `Nbe::family_is_constant_value` fixes this by reusing the
// real environment (`venv`) itself, adding only one fresh marker for the
// binder actually being tested. Once that fires, the nested `Transp` collapses,
// and (together with the De Morgan interval lattice's identity/absorption laws
// — `i0 ∧ r ≡ i0`, `i1 ∧ r ≡ r`, etc. — now also folded eagerly during
// evaluation, see [`crate::nbe::Value::INeg`]'s doc) the whole base case
// reduces to `refl (refl a)` on the nose, exactly as this doc always claimed it
// *should*. [`trans_right_unit`]/[`trans_inv_right`]/[`trans_inv_left`] all now
// type-check — see `tests::right_unit_closes`/`inv_right_closes`/
// `inv_left_closes`.
//
// This is a *completeness*-only fix: no new equation is introduced (see
// `Nbe::family_is_constant_value`'s own soundness argument), it only lets the
// pre-existing, already-sound regularity/interval-lattice judgements fire in
// more (legitimate) contexts. This is the *same class* of completeness gap as
// [`trans3`]'s documented nested-`trans` obstruction and `crate::equiv_hae`'s
// `sec_prime`-on-literal-`PLam`-data gap — both of those remain OPEN after this
// fix (confirmed by re-running `crate::equiv_hae::tests::
// debug_nested_trans_hits_the_documented_completeness_gap`/
// `sec_prime_on_literal_plam_identity_data_is_a_known_gap_not_yet_closed`,
// still asserting failure): they hit a *different* obstruction (feeding a
// `trans`-built — as opposed to a bound-variable — term back in as a further
// `J` *subject*, not a base-case reduction depth issue), which this pass's
// fix does not address.
//
// # Associativity: known, precisely-diagnosed gap (still open)
//
// The literal statement `Path (trans (trans p q) r) (trans p (trans q r))`
// cannot even be *written* as a well-typed `Term` in this kernel: its LHS
// requires applying [`trans`] to `trans ty a b p q` as the *subject* path being
// `J`-eliminated, and doing that is exactly the obstruction [`trans3`]'s own
// module doc records ("nesting `trans`... does not type-check in this kernel"
// — confirmed for three fully abstract axiomatized paths with no `sym`/`ap`
// involved, see `tests::debug_nested_trans_hits_the_documented_completeness_gap`
// in `crate::equiv_hae`, still reproducing after this pass's fix above).
// [`trans3`] itself sidesteps this by only ever `J`-eliminating the *first*,
// genuinely opaque path (`p`), applying the other two (`q`, `r`) as ordinary
// function arguments — which fixes *one* particular association (`p ; (q ;
// r)`) but gives no way to *also* build the other association (`(p ; q) ; r`)
// as a further `J`-subject without hitting the same wall. Not landed here; see
// [`trans3`]'s doc for the isolated repro and `crate::equiv_hae`'s module doc
// for how this bears on `τ'`.
// ============================================================================

/// `trans_left_unit ty a b q : Path (Path ty a b) (trans ty a b (refl a) q) q`
/// — the left-unit groupoid law. Holds by **plain `refl`**: see this section's
/// module doc, "Left unit is definitional, not just propositional" — `trans`'s
/// own `J`-on-`refl` computation collapses `trans ty a b (refl a) q` straight
/// to `q`, so the 2-path witness is simply `refl q`.
pub fn trans_left_unit(ty: &Term, a: &Term, b: &Term, q: &Term) -> Term {
    let _ = (ty, a, b); // endpoints read off `q`'s own checked type by the caller,
    // matching this module's other combinators' documentation convention.
    refl(q)
}

/// `trans_right_unit ty a b p : Path (Path ty a b) (trans ty a b p (refl b)) p`
/// — the right-unit groupoid law, given `p : Path ty a b`. `J`-eliminates `p`
/// with motive `C := λ(y:ty)(q:Path ty a y). Path (Path ty a y) (trans ty a y q
/// (refl y)) q`; base case (`y=a`, `q=refl a`) is `refl (refl a) : Path (Path
/// ty a a) (trans ty a a (refl a) (refl a)) (refl a)`, which type-checks
/// because `trans ty a a (refl a) (refl a)` itself reduces to `refl a` by the
/// *definitional* left-unit law (see [`trans_left_unit`]'s doc) — so the base
/// case's goal collapses to `Path (Path ty a a) (refl a) (refl a)` on the nose.
pub fn trans_right_unit(ty: &Term, a: &Term, b: &Term, p: &Term) -> Term {
    let _ = b; // `p`'s own checked right endpoint, inferred by `j` exactly like
    // `trans`/`nat_sq`'s own trailing endpoint arguments.
    let motive = Term::lam(
        ty.clone(),
        Term::lam(
            // ctx [y]: Path ty a y
            Term::path(ty.lift(1, 0), a.lift(1, 0), Term::Var(0)),
            {
                // ctx [y,q]: ty/a lifted by 2; y=Var(1), q=Var(0)
                let trans_term =
                    trans(&ty.lift(2, 0), &a.lift(2, 0), &Term::Var(1), &Term::Var(0), &refl(&Term::Var(1)));
                Term::path(Term::path(ty.lift(2, 0), a.lift(2, 0), Term::Var(1)), trans_term, Term::Var(0))
            },
        ),
    );
    let d = refl(&refl(a));
    j(&motive, &d, p)
}

/// `trans_inv_right ty a b p : Path (Path ty a a) (trans ty a a p (sym p))
/// (refl a)` — the right inverse law, given `p : Path ty a b` (`sym p : Path ty
/// b a`, so `trans p (sym p) : Path ty a a`). `J`-eliminates `p` with motive
/// `C := λ(y:ty)(q:Path ty a y). Path (Path ty a a) (trans ty a a q (sym q))
/// (refl a)`; base case (`y=a`, `q=refl a`) needs `trans ty a a (refl a) (sym
/// (refl a)) ≡ refl a`: `sym (refl a)` reduces to `refl a` definitionally
/// ([`crate::contr::sym`]'s own one-line fact — `⟨i⟩ (refl a)@(~i)` β-reduces
/// the constant body to `a` regardless of the interval argument), and then
/// `trans ty a a (refl a) (refl a) ≡ refl a` by the definitional left-unit law
/// — so the base case is again `refl (refl a)`.
pub fn trans_inv_right(ty: &Term, a: &Term, b: &Term, p: &Term) -> Term {
    let _ = b;
    let motive = Term::lam(
        ty.clone(),
        Term::lam(
            Term::path(ty.lift(1, 0), a.lift(1, 0), Term::Var(0)),
            {
                let trans_term = trans(
                    &ty.lift(2, 0),
                    &a.lift(2, 0),
                    &a.lift(2, 0),
                    &Term::Var(0),
                    &crate::contr::sym(&Term::Var(0)),
                );
                Term::path(Term::path(ty.lift(2, 0), a.lift(2, 0), a.lift(2, 0)), trans_term, refl(&a.lift(2, 0)))
            },
        ),
    );
    let d = refl(&refl(a));
    j(&motive, &d, p)
}

/// `trans_inv_left ty a b p : Path (Path ty b b) (trans ty b b (sym p) p)
/// (refl b)` — the left inverse law, given `p : Path ty a b` (`sym p : Path ty
/// b a`, so `trans (sym p) p : Path ty b b`). Mirrors [`trans_inv_right`]
/// exactly, but eliminates `p` with the *first* leg being `sym p` rather than
/// `p` itself: motive `C := λ(y:ty)(q:Path ty a y). Path (Path ty y y) (trans
/// ty y y (sym q) q) (refl y)`; base case (`y=a`, `q=refl a`) again reduces —
/// `sym (refl a) ≡ refl a`, then left-unit — to `refl (refl a)`.
pub fn trans_inv_left(ty: &Term, a: &Term, b: &Term, p: &Term) -> Term {
    let _ = b;
    let motive = Term::lam(
        ty.clone(),
        Term::lam(
            Term::path(ty.lift(1, 0), a.lift(1, 0), Term::Var(0)),
            {
                // ctx [y,q]: y=Var(1), q=Var(0)
                let trans_term = trans(
                    &ty.lift(2, 0),
                    &Term::Var(1),
                    &Term::Var(1),
                    &crate::contr::sym(&Term::Var(0)),
                    &Term::Var(0),
                );
                Term::path(Term::path(ty.lift(2, 0), Term::Var(1), Term::Var(1)), trans_term, refl(&Term::Var(1)))
            },
        ),
    );
    let d = refl(&refl(a));
    j(&motive, &d, p)
}

// ============================================================================
// Phase 4.6: `trans_assoc` — STILL OPEN, but with a substantially more precise
// diagnosis than any prior pass reached. Four strategies were tried in total:
//
// 1. (Three *prior* passes) composing the closed `trans_right_unit`/`ap` lemmas
//    through a *third*, outer `trans`, in the `J`-on-`r` base case — always hit a
//    connect-square boundary misalignment (see the "Associativity" section
//    immediately below).
// 2. (*This* pass, first attempt) a **single** `J`-elimination on `p` alone, with
//    a motive whose base case needs *two* independent trans-of-`refl` collapses
//    (one on each side of the goal `Path`) simultaneously, both reached through
//    an *outer* `App(App(motive, y), p'))` beta-redex (`family(i0)`, `j`'s own
//    construction). This type-checked as a *term*, but **failed to check** —
//    even with `p'` substituted by a *literal* `refl a` (no `connect`-square
//    indirection at all), `check`/`def_eq` could not see through *two* nested
//    `Transp` collapses reached via that beta-redex, although the *exact same*
//    pair of terms, built by direct substitution (`.lift`, no `App`/`Lam` redex)
//    rather than through `j`'s own motive-application, compared equal instantly.
//    This is a **new, more precise diagnosis** than strategies 1-3's
//    "connect-square misalignment": a genuine `nbe`-level completeness gap in
//    reducing *two* nested `Transp` regularity collapses when reached through an
//    *ordinary* (non-`J`) beta application rather than directly through the
//    enclosing `J`'s own substitution — a strictly deeper case than
//    `crate::nbe::Nbe::family_is_constant_value`'s existing fix handles (that
//    fix's precedent, `right_unit_closes`, only ever needs *one* side of the
//    goal `Path` to reduce; this naive motive needs *both* sides to reduce
//    simultaneously). Fixing this needs an `nbe.rs` edit, off-limits for this
//    pass — so strategy 2 was abandoned in favor of:
// 4. **(Furthest reached, but ALSO does not close)** `J`-eliminate `q` instead
//    of `p`. The key asymmetry: of `trans_assoc`'s two `trans` applications,
//    `trans (trans p q) r`'s *outer* `trans` eliminates the compound `trans p q`
//    (not `q` directly), while `trans p (trans q r)`'s *inner* `trans q r`
//    eliminates `q` directly. So `J`-eliminating `q` (generalizing its own
//    target, reproving the statement for every abstract `r'`) puts a literal
//    `refl b` in `trans q r`'s eliminated slot at the base case, giving the
//    *inner* side a **free, single-layer** definitional collapse — `trans
//    (refl b) r' ≡ r'` — exactly `right_unit_closes`'s already-working depth
//    (only *one* side of the goal `Path` needs to reduce this way, not both, so
//    strategy 2's obstruction does not apply here). The *other* side, `trans
//    (trans p q) r`, still needs the already-closed, propositional
//    [`trans_right_unit`] lemma, whiskered through a single `ap` (`ap (λx. trans
//    ty a dd x r') (trans_right_unit ty a b p)`) rather than composed through a
//    further `J` (the shape that sank strategies 1-3). This construction *does*
//    avoid both the connect-square misalignment (1-3) and the
//    double-simultaneous-collapse gap (2) — but hits a **third, independently
//    isolated** `nbe` completeness gap instead: `ap`'s own output has the shape
//    `PLam(App(f, PApp(subject, i)))`, and when `subject` is itself a
//    `Transp`-built term (as `trans_right_unit`'s output always is, not a
//    literal `PLam`), comparing the resulting `App(f, PApp(subject, i0/i1))`
//    against an independently-already-reduced target *fails* — even though
//    `PApp(subject, i0)` *alone* (outside the enclosing `App`) is confirmed,
//    standalone, to reduce correctly to its declared boundary endpoint via the
//    type-directed `path_boundary` rule, and even though substituting that
//    *already-reduced* endpoint in *by hand* before wrapping in `App(f, ·)` also
//    compares correctly. So the gap is specifically: `path_boundary` resolution
//    of a `Transp` subject, nested *inside* an enclosing `App`'s argument
//    position, is not being forced before comparison. This, too, needs an
//    `nbe.rs` edit — off-limits for this pass.
//
// **Net result**: `trans_assoc` is *stated* correctly (see [`trans_assoc`]'s own
// doc for the exact target type) and *constructed* via strategy 4 (the
// furthest-reached, most surgical approach — avoiding two of the three
// previously/newly diagnosed obstructions), but does not yet `check`. Landed as
// documentation of the precise remaining boundary plus a real (if
// non-typechecking-to-completion) construction, per this task's own explicit
// fallback instruction — see `groupoid_law_tests::trans_assoc_closes` (kept
// `#[ignore]`d, with the exact diagnosis in its own doc) and
// `trans_assoc_does_not_yet_typecheck_confirming_the_documented_gap` (a
// standing, *positive* assertion that the gap still reproduces, so a future
// `nbe.rs` fix closing it will be caught immediately by this test flipping to a
// spurious "gap closed, `#[ignore]`d test now passes" signal).
//
// # Associativity: earlier diagnosis (kept as history; refined above)
//
// The literal statement `Path (trans (trans p q) r) (trans p (trans q r))`
// cannot even be *written* as a well-typed `Term` in this kernel: its LHS
// requires applying [`trans`] to `trans ty a b p q` as the *subject* path being
// `J`-eliminated, and doing that is exactly the obstruction [`trans3`]'s own
// module doc records ("nesting `trans`... does not type-check in this kernel"
// — confirmed for three fully abstract axiomatized paths with no `sym`/`ap`
// involved, see `tests::debug_nested_trans_hits_the_documented_completeness_gap`
// in `crate::equiv_hae`, still reproducing after this pass's fix above).
// **UPDATE (this pass): this specific claim is now STALE** — re-running that
// exact test (`crate::equiv_hae::tests::
// debug_nested_trans_hits_the_documented_completeness_gap`) confirms nested
// `trans` (using one `trans`-built term as the *subject* of a further `trans`)
// now type-checks fine (the test's own docstring already says so: "the
// completeness gap is closed"). What *remains* hard is not that basic
// nesting-as-subject shape, but the *harder* shapes diagnosed under strategies
// 2 and 4 above — three genuinely distinct `nbe`-level completeness gaps have
// now been isolated across this module's history, all requiring `nbe.rs` edits
// this pass is not permitted to make.
// ============================================================================

/// `trans_assoc ty a b target_d p q r : Path (Path ty a target_d) (trans ty a
/// target_d (trans ty a b p q) r) (trans ty a target_d p (trans ty b target_d q
/// r))` — see the doc block above this function for the exact
/// strategy/diagnosis (strategy 4: `J`-eliminate `q`, combine the inner side's
/// free definitional left-unit collapse with the outer side's *single*
/// `ap`-whiskered [`trans_right_unit`] composition). `b` is `p`'s own target
/// (needed explicitly here, unlike [`trans`]'s own elimination subject, because
/// it is *not* itself being eliminated — it is [`trans_right_unit`]'s own
/// fixed endpoint); `target_d` is `r`'s final target, exactly like [`trans`]'s
/// own trailing target argument. `q`'s own target (`c`, `r`'s source) is
/// inferred by `j`, exactly like [`trans`]'s own elimination subject.
pub fn trans_assoc(ty: &Term, a: &Term, b: &Term, target_d: &Term, p: &Term, q: &Term, r: &Term) -> Term {
    // motive, ctx []: λ (z:ty) (q':Path ty b z).
    //   Π (dd:ty) (r':Path ty z dd). Path (...) lhs rhs
    let motive = Term::lam(
        ty.clone(),
        Term::lam(
            // ctx [z]: Path ty b z
            Term::path(ty.lift(1, 0), b.lift(1, 0), Term::Var(0)),
            {
                // ctx [z,q']: z=Var(1), q'=Var(0)
                let pi_dd = ty.lift(2, 0);
                let pi_r = {
                    // ctx [z,q',dd]: z=Var(2), dd=Var(0)
                    Term::path(ty.lift(3, 0), Term::Var(2), Term::Var(0))
                };
                let body = {
                    // ctx [z,q',dd,r']: z=Var(3), q'=Var(2), dd=Var(1), r'=Var(0)
                    let ty4 = ty.lift(4, 0);
                    let a4 = a.lift(4, 0);
                    let b4 = b.lift(4, 0);
                    let p4 = p.lift(4, 0);
                    let z = Term::Var(3);
                    let q_ = Term::Var(2);
                    let dd = Term::Var(1);
                    let r_ = Term::Var(0);
                    let trans_pq = trans(&ty4, &a4, &z, &p4, &q_); // Path ty a z
                    let lhs = trans(&ty4, &a4, &dd, &trans_pq, &r_);
                    let trans_qr = trans(&ty4, &b4, &dd, &q_, &r_); // Path ty b dd
                    let rhs = trans(&ty4, &a4, &dd, &p4, &trans_qr);
                    Term::path(Term::path(ty4, a4, dd), lhs, rhs)
                };
                Term::pi(pi_dd, Term::pi(pi_r, body))
            },
        ),
    );
    // d, ctx []: λ dd r'. ap (λx. trans ty a dd x r') (trans_right_unit ty a b p)
    //   : Path (Path ty a dd) (trans ty a dd (trans ty a b p (refl b)) r')
    //          (trans ty a dd p r')
    // — exactly `C b (refl b)`'s LHS-vs-(collapsed)-RHS statement: the checker
    // only needs the goal's *other* side (`trans p (trans (refl b) r')`) to
    // collapse via the free, single-layer left-unit rule to `trans p r'`,
    // matching `right_unit_closes`'s already-working depth.
    let d = Term::lam(
        ty.clone(),
        Term::lam(
            // ctx [dd]: Path ty b dd
            Term::path(ty.lift(1, 0), b.lift(1, 0), Term::Var(0)),
            {
                // ctx [dd,r']: dd=Var(1), r'=Var(0)
                let ty2 = ty.lift(2, 0);
                let a2 = a.lift(2, 0);
                let b2 = b.lift(2, 0);
                let p2 = p.lift(2, 0);
                let dd = Term::Var(1);
                let r_ = Term::Var(0);
                // f := λ (x:Path ty a b). trans ty a dd x r'
                let f = Term::lam(
                    Term::path(ty2.clone(), a2.clone(), b2.clone()),
                    trans(&ty2.lift(1, 0), &a2.lift(1, 0), &dd.lift(1, 0), &Term::Var(0), &r_.lift(1, 0)),
                );
                ap(&f, &trans_right_unit(&ty2, &a2, &b2, &p2))
            },
        ),
    );
    let elim = j(&motive, &d, q);
    Term::apps(elim, [target_d.clone(), r.clone()])
}

#[cfg(test)]
mod groupoid_law_tests {
    use super::*;
    use crate::kernel::Kernel;
    use crate::term::name;

    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    /// `A : Type 0`; `a b : A`; `p : Path A a b`.
    fn groupoid_env() -> Kernel {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        k.add_axiom("b", 0, cn("A")).unwrap();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        k
    }

    #[test]
    fn left_unit_typechecks() {
        let k = groupoid_env();
        let term = trans_left_unit(&cn("A"), &cn("a"), &cn("b"), &cn("p"));
        let expected = Term::path(
            Term::path(cn("A"), cn("a"), cn("b")),
            trans(&cn("A"), &cn("a"), &cn("b"), &refl(&cn("a")), &cn("p")),
            cn("p"),
        );
        let ty = k.infer(&term).expect("trans_left_unit should typecheck");
        assert!(k.def_eq(&ty, &expected), "trans_left_unit has type {ty:?}, expected {expected:?}");
        k.check(&term, &expected).unwrap();
    }

    /// **Closed** (previously a documented nested-reduction gap — see
    /// `crate::nbe::Nbe::family_is_constant_value`'s doc for the conversion-
    /// completeness fix that closes it): [`trans_right_unit`]'s base case relies on
    /// `trans ty a a (refl a) (refl a)` reducing (via the *definitional* left-unit
    /// fact, see [`trans_left_unit`]'s doc) once the *inner* `J`'s own `connect`
    /// term (itself built by the *outer* `j` call inside [`trans_right_unit`])
    /// reduces to `refl a` at `i0`. That reduction needs to fire *underneath* an
    /// additional layer of `transp`/`J` nesting beyond what [`nat_sq`]/[`j`]'s own
    /// "computation on `refl`" sections confirm alone — closed by making
    /// `crate::kan::family_is_constant`'s NbE-side regularity probe reuse the
    /// *real* evaluation environment (rather than fabricating unrelated fresh
    /// neutrals for the family's other free variables), so the inner `Transp`
    /// collapses using the values its enclosing `J` already substituted in.
    #[test]
    fn right_unit_closes() {
        let k = groupoid_env();
        let term = trans_right_unit(&cn("A"), &cn("a"), &cn("b"), &cn("p"));
        let expected = Term::path(
            Term::path(cn("A"), cn("a"), cn("b")),
            trans(&cn("A"), &cn("a"), &cn("b"), &cn("p"), &refl(&cn("b"))),
            cn("p"),
        );
        let ty = k.infer(&term).expect("trans_right_unit should now typecheck");
        assert!(k.def_eq(&ty, &expected), "trans_right_unit has type {ty:?}, expected {expected:?}");
        k.check(&term, &expected).unwrap();
    }

    /// **Closed**, same fix as [`right_unit_closes`] — the right inverse law
    /// (`trans p (sym p) ≡ refl`).
    #[test]
    fn inv_right_closes() {
        let k = groupoid_env();
        let term = trans_inv_right(&cn("A"), &cn("a"), &cn("b"), &cn("p"));
        let expected = Term::path(
            Term::path(cn("A"), cn("a"), cn("a")),
            trans(&cn("A"), &cn("a"), &cn("a"), &cn("p"), &crate::contr::sym(&cn("p"))),
            refl(&cn("a")),
        );
        let ty = k.infer(&term).expect("trans_inv_right should now typecheck");
        assert!(k.def_eq(&ty, &expected), "trans_inv_right has type {ty:?}, expected {expected:?}");
        k.check(&term, &expected).unwrap();
    }

    /// **Closed**, same fix — the left inverse law (`trans (sym p) p ≡ refl`).
    #[test]
    fn inv_left_closes() {
        let k = groupoid_env();
        let term = trans_inv_left(&cn("A"), &cn("a"), &cn("b"), &cn("p"));
        let expected = Term::path(
            Term::path(cn("A"), cn("b"), cn("b")),
            trans(&cn("A"), &cn("b"), &cn("b"), &crate::contr::sym(&cn("p")), &cn("p")),
            refl(&cn("b")),
        );
        let ty = k.infer(&term).expect("trans_inv_left should now typecheck");
        assert!(k.def_eq(&ty, &expected), "trans_inv_left has type {ty:?}, expected {expected:?}");
        k.check(&term, &expected).unwrap();
    }

    /// Dimensionality guard (mirrors `crate::equiv_hae::tests::
    /// tau_type_is_genuinely_two_dimensional`) for the one law that *does*
    /// close: [`trans_left_unit`]'s inferred type is a `PathP` whose own family
    /// argument is itself a `PathP` — a genuine 2-path, not a plain 1-path
    /// silently accepted at a too-shallow type.
    #[test]
    fn left_unit_type_is_genuinely_two_dimensional() {
        let k = groupoid_env();
        let term = trans_left_unit(&cn("A"), &cn("a"), &cn("b"), &cn("p"));
        let ty = k.infer(&term).unwrap();
        match &ty {
            Term::PathP(family, _, _) => assert!(
                matches!(family.as_ref(), Term::PathP(..)),
                "expected a genuine 2-path, got family {family:?}"
            ),
            other => panic!("expected PathP, got {other:?}"),
        }
    }

    /// `A B C D : Type 0`; `a b c d0 : A`; `p : Path A a b`; `q : Path A b c`;
    /// `r : Path A c d0` — the general (fully abstract, opaque) setting
    /// `trans_assoc` is stated over.
    fn assoc_env() -> Kernel {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        k.add_axiom("b", 0, cn("A")).unwrap();
        k.add_axiom("c", 0, cn("A")).unwrap();
        k.add_axiom("d0", 0, cn("A")).unwrap();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        k.add_axiom("q", 0, Term::path(cn("A"), cn("b"), cn("c"))).unwrap();
        k.add_axiom("r", 0, Term::path(cn("A"), cn("c"), cn("d0"))).unwrap();
        k
    }

    /// **Known gap, not yet closed** (documented, not silently swept under the
    /// rug — see `trans_assoc`'s own module doc, "Phase 4.6", strategy 4, for the
    /// full diagnosis): `trans_assoc`'s witness type-checks as a `Term` (no panic,
    /// well-scoped, `j`-derived) but does **not** yet `check`/`def_eq` against the
    /// full associativity statement. Isolated root cause (confirmed via a
    /// standalone repro kept out of this file per the pass's own scoping
    /// discipline — see the doc's strategy-4 paragraph): `ap`'s own construction
    /// produces an endpoint of the shape `App(f, PApp(subject, i0/i1))`; when
    /// `subject` is itself a `Transp`-built (not literal-`PLam`) term — exactly
    /// [`trans_right_unit`]'s own shape — comparing that `App(f, PApp(...))` node
    /// against an independently-*already-reduced* target fails, even though the
    /// **same** two terms compare equal instantly when the `PApp`'s own boundary
    /// is resolved *first*, outside the enclosing application. This is a
    /// *different*, more precisely isolated `nbe`-level completeness gap than the
    /// double-nested-`Transp`-collapse gap the naive (superseded) single-`J`-on-`p`
    /// attempt hit — see the module doc for both. Fixing either requires editing
    /// `nbe.rs`, off-limits for this pass. Kept `#[ignore]`d as a precise,
    /// reproducing record rather than deleted, matching this module's
    /// "known gap" convention elsewhere (see `crate::equiv_hae::tests::
    /// sec_prime_on_literal_plam_identity_data_is_a_known_gap_not_yet_closed`).
    #[test]
    #[ignore = "known gap: ap-of-a-Transp-subject inside a beta-redex does not reduce far enough to compare — needs an nbe.rs fix, off-limits for this pass; see trans_assoc's module doc"]
    fn trans_assoc_closes() {
        let k = assoc_env();
        let term = trans_assoc(&cn("A"), &cn("a"), &cn("b"), &cn("d0"), &cn("p"), &cn("q"), &cn("r"));
        let trans_pq = trans(&cn("A"), &cn("a"), &cn("c"), &cn("p"), &cn("q"));
        let lhs = trans(&cn("A"), &cn("a"), &cn("d0"), &trans_pq, &cn("r"));
        let trans_qr = trans(&cn("A"), &cn("b"), &cn("d0"), &cn("q"), &cn("r"));
        let rhs = trans(&cn("A"), &cn("a"), &cn("d0"), &cn("p"), &trans_qr);
        let expected = Term::path(Term::path(cn("A"), cn("a"), cn("d0")), lhs, rhs);
        let ty = k.infer(&term).expect("trans_assoc should typecheck");
        assert!(k.def_eq(&ty, &expected), "trans_assoc has type {ty:?}, expected {expected:?}");
        k.check(&term, &expected).unwrap();
    }

    /// Confirms the gap [`trans_assoc_closes`] documents is real and precisely
    /// where claimed: `trans_assoc`'s own witness genuinely fails `k.infer`
    /// (the base-case check inside its own `J`-elimination does not go through),
    /// so this is not a downstream/adversarial-test artifact.
    #[test]
    fn trans_assoc_does_not_yet_typecheck_confirming_the_documented_gap() {
        let k = assoc_env();
        let term = trans_assoc(&cn("A"), &cn("a"), &cn("b"), &cn("d0"), &cn("p"), &cn("q"), &cn("r"));
        assert!(k.infer(&term).is_err(), "expected the documented gap to still reproduce");
    }

    /// Adversarial: `trans_assoc`'s witness does not check against an unrelated
    /// (swapped-endpoint) 2-path goal — same discipline as
    /// [`groupoid_laws_do_not_check_against_a_wrong_goal`], now for associativity.
    #[test]
    fn trans_assoc_does_not_check_against_a_wrong_goal() {
        let mut k = assoc_env();
        k.add_axiom("e", 0, cn("A")).unwrap();
        let term = trans_assoc(&cn("A"), &cn("a"), &cn("b"), &cn("d0"), &cn("p"), &cn("q"), &cn("r"));
        let trans_pq = trans(&cn("A"), &cn("a"), &cn("c"), &cn("p"), &cn("q"));
        let lhs = trans(&cn("A"), &cn("a"), &cn("d0"), &trans_pq, &cn("r"));
        // Swap the RHS's target endpoint to an unrelated point `e` instead of `d0`.
        let wrong = Term::path(Term::path(cn("A"), cn("a"), cn("d0")), lhs, cn("e"));
        assert!(k.check(&term, &wrong).is_err());
    }

    /// Adversarial: `trans_assoc` cannot manufacture a proof for a *non*-anti-`False`
    /// instance either — swapping in a wrong middle point on the RHS's inner `trans
    /// q r` (using an unrelated `q2 : Path A b e` instead of the real `q`) is a
    /// distinct, non-defeq statement that the same witness must not satisfy.
    #[test]
    fn trans_assoc_does_not_check_with_a_mismatched_middle_path() {
        let mut k = assoc_env();
        k.add_axiom("e", 0, cn("A")).unwrap();
        k.add_axiom("q2", 0, Term::path(cn("A"), cn("b"), cn("e"))).unwrap();
        let term = trans_assoc(&cn("A"), &cn("a"), &cn("b"), &cn("d0"), &cn("p"), &cn("q"), &cn("r"));
        let trans_pq = trans(&cn("A"), &cn("a"), &cn("c"), &cn("p"), &cn("q"));
        let lhs = trans(&cn("A"), &cn("a"), &cn("d0"), &trans_pq, &cn("r"));
        // rhs built from q2 instead of q — ill-typed to even compose with r (target
        // mismatch: q2 lands at e, r starts at c), so this must fail to check.
        let bogus_rhs = trans(&cn("A"), &cn("a"), &cn("d0"), &cn("p"), &cn("q2"));
        let wrong = Term::path(Term::path(cn("A"), cn("a"), cn("d0")), lhs, bogus_rhs);
        assert!(k.check(&term, &wrong).is_err());
    }

    /// Adversarial: none of the four laws' witnesses check against an unrelated
    /// (non-reflexive-in-the-right-place) 2-path goal — a totally bogus swap of
    /// which side is `p`/`refl` would be a distinct, non-defeq statement.
    #[test]
    fn groupoid_laws_do_not_check_against_a_wrong_goal() {
        let mut k = groupoid_env();
        k.add_axiom("c", 0, cn("A")).unwrap();
        let term = trans_right_unit(&cn("A"), &cn("a"), &cn("b"), &cn("p"));
        // Same `trans` application as the real right-unit goal, but with the
        // right-hand endpoint swapped to an unrelated point `c` instead of `p`.
        let unrelated = Term::path(
            Term::path(cn("A"), cn("a"), cn("b")),
            trans(&cn("A"), &cn("a"), &cn("b"), &cn("p"), &refl(&cn("b"))),
            cn("c"),
        );
        assert!(k.check(&term, &unrelated).is_err());
    }
}

#[cfg(test)]
mod square_tests {
    use super::*;
    use crate::kernel::Kernel;
    use crate::term::name;

    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    /// `A B : Type 0`; `f g : A -> B`; `h : Πx. Path B (f x) (g x)`; `x y : A`;
    /// `p : Path A x y`.
    fn nat_sq_env() -> Kernel {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("B", 0, Term::typ(0)).unwrap();
        k.add_axiom("f", 0, Term::arrow(cn("A"), cn("B"))).unwrap();
        k.add_axiom("g", 0, Term::arrow(cn("A"), cn("B"))).unwrap();
        let h_ty = Term::pi(
            cn("A"),
            Term::path(cn("B"), Term::app(cn("f"), Term::Var(0)), Term::app(cn("g"), Term::Var(0))),
        );
        k.add_axiom("h", 0, h_ty).unwrap();
        k.add_axiom("x", 0, cn("A")).unwrap();
        k.add_axiom("y", 0, cn("A")).unwrap();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("x"), cn("y"))).unwrap();
        k
    }

    /// `const_square a` checks at exactly `Square ty (refl a) (refl a) (refl a)
    /// (refl a)`, for an abstract/axiomatized `a`.
    #[test]
    fn const_square_typechecks() {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        let a = cn("a");
        let term = const_square(&a);
        let expected = square_ty(&cn("A"), &refl(&a), &refl(&a), &refl(&a), &refl(&a));
        k.check(&term, &expected).unwrap();
        let ty = k.infer(&term).unwrap();
        assert!(k.def_eq(&ty, &expected));
    }

    /// `conn_and`/`conn_or` each check at their documented `Square` types, for a
    /// genuine (axiomatized, non-`refl`) path `p : Path A a b`.
    #[test]
    fn connection_squares_typecheck() {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        k.add_axiom("b", 0, cn("A")).unwrap();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        let (a, b, p) = (cn("a"), cn("b"), cn("p"));

        let and_term = conn_and(&cn("A"), &a, &b, &p);
        let and_expected = square_ty(&cn("A"), &refl(&a), &p, &refl(&a), &p);
        k.check(&and_term, &and_expected).unwrap();

        let or_term = conn_or(&cn("A"), &a, &b, &p);
        let or_expected = square_ty(&cn("A"), &p, &refl(&b), &p, &refl(&b));
        k.check(&or_term, &or_expected).unwrap();
    }

    /// `nat_sq` checks at exactly the documented naturality-square type `Square B
    /// (h x) (h y) (ap f p) (ap g p)`, for a fully abstract/axiomatized homotopy
    /// `h : f ~ g` and path `p : Path A x y` — the keystone lemma HoTT Lemma
    /// 2.4.3, and the obstruction `crate::equiv_hae`'s `τ'` doc names directly.
    #[test]
    fn nat_sq_typechecks_for_an_abstract_homotopy() {
        let k = nat_sq_env();
        let term = nat_sq(&cn("A"), &cn("B"), &cn("f"), &cn("g"), &cn("h"), &cn("x"), &cn("p"));
        let expected = square_ty(
            &cn("B"),
            &Term::app(cn("h"), cn("x")),
            &Term::app(cn("h"), cn("y")),
            &ap(&cn("f"), &cn("p")),
            &ap(&cn("g"), &cn("p")),
        );
        let ty = k.infer(&term).expect("nat_sq should typecheck");
        assert!(k.def_eq(&ty, &expected), "nat_sq has type {ty:?}, expected {expected:?}");
        k.check(&term, &expected).unwrap();
    }

    /// `nat_sq h x (refl x)` still infers a well-formed type (`J`'s own
    /// unconditional guarantee — see [`j`]'s soundness doc), instantiated at the
    /// reflexivity case. At `p = refl x`, `ap f (refl x)`/`ap g (refl x)` are
    /// individually *known* (by [`ap`]'s own definition) to reduce to `refl (f
    /// x)`/`refl (g x)`, so this square's boundary degenerates to the constant
    /// one at the level of what each side computes to — a full literal-term
    /// `check` against `const_square`'s exact goal type is a further conversion-
    /// depth question this pass does not chase (nested-application reduction
    /// under two `PathP`/`Lam` layers is exactly the kind of friction point
    /// `crate::equiv_hae`'s module doc documents elsewhere for `trans`/`sec_prime`
    /// — not attempted here to avoid a second undiagnosed conversion gap).
    #[test]
    fn nat_sq_on_refl_still_infers_a_type() {
        let k = nat_sq_env();
        let term = nat_sq(&cn("A"), &cn("B"), &cn("f"), &cn("g"), &cn("h"), &cn("x"), &refl(&cn("x")));
        k.infer(&term).expect("nat_sq on refl should still infer a type (J's unconditional guarantee)");
    }

    /// Dimensionality guard (mirroring `crate::equiv_hae::tests::
    /// tau_type_is_genuinely_two_dimensional`): `nat_sq`'s inferred type is
    /// definitionally equal to `square_ty`'s output — a `PathP` whose *own*
    /// type-family argument is itself a `PathP` — i.e. genuinely a square, not a
    /// plain 1-path silently accepted at a too-shallow type. (`square_ty`'s own
    /// construction, checked directly here, is manifestly `PathP`-of-`PathP` by
    /// inspection; `nat_sq`'s inferred type is confirmed *def-eq* to it, matching
    /// this module's other soundness tests' discipline of comparing via
    /// conversion rather than literal `infer`-output matching, since `infer`
    /// does not itself beta-reduce the motive application.)
    #[test]
    fn nat_sq_type_is_genuinely_two_dimensional() {
        let k = nat_sq_env();
        let term = nat_sq(&cn("A"), &cn("B"), &cn("f"), &cn("g"), &cn("h"), &cn("x"), &cn("p"));
        let expected = square_ty(
            &cn("B"),
            &Term::app(cn("h"), cn("x")),
            &Term::app(cn("h"), cn("y")),
            &ap(&cn("f"), &cn("p")),
            &ap(&cn("g"), &cn("p")),
        );
        // `expected` is manifestly `PathP(PathP(..), _, _)` by construction.
        match &expected {
            Term::PathP(family, _, _) => assert!(matches!(family.as_ref(), Term::PathP(..))),
            _ => unreachable!("square_ty always builds a PathP"),
        }
        let ty = k.infer(&term).expect("nat_sq should typecheck");
        assert!(k.def_eq(&ty, &expected), "nat_sq's type is not def-eq to the genuine square type");
    }

    /// Adversarial: `nat_sq`'s output must not check against an unrelated
    /// `Square` goal (e.g. with `left`/`right` swapped) — confirms the square is
    /// pinned to its exact, documented orientation, not accidentally symmetric.
    #[test]
    fn nat_sq_does_not_check_against_a_swapped_square() {
        let k = nat_sq_env();
        let term = nat_sq(&cn("A"), &cn("B"), &cn("f"), &cn("g"), &cn("h"), &cn("x"), &cn("p"));
        // Swap `left`/`right` — a distinct (in general) Square goal.
        let wrong = square_ty(
            &cn("B"),
            &Term::app(cn("h"), cn("x")),
            &Term::app(cn("h"), cn("y")),
            &ap(&cn("g"), &cn("p")), // swapped
            &ap(&cn("f"), &cn("p")), // swapped
        );
        let ty = k.infer(&term).unwrap();
        assert!(!k.def_eq(&ty, &wrong), "nat_sq's square must not also satisfy the swapped orientation");
        assert!(k.check(&term, &wrong).is_err());
    }

    /// Adversarial: a bogus 1-dimensional term (`refl` of one side) must not
    /// check against the genuinely 2-dimensional `Square` goal.
    #[test]
    fn bogus_one_path_does_not_satisfy_square_type() {
        let k = nat_sq_env();
        let expected = square_ty(
            &cn("B"),
            &Term::app(cn("h"), cn("x")),
            &Term::app(cn("h"), cn("y")),
            &ap(&cn("f"), &cn("p")),
            &ap(&cn("g"), &cn("p")),
        );
        let bogus = refl(&Term::app(cn("h"), cn("x")));
        assert!(k.check(&bogus, &expected).is_err());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Kernel;
    use crate::term::name;

    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    /// A small environment: `A B : Type 0`, `a b c : A`, `f g : A -> A`.
    fn base_env() -> Kernel {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("B", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        k.add_axiom("b", 0, cn("A")).unwrap();
        k.add_axiom("c", 0, cn("A")).unwrap();
        k.add_axiom("f", 0, Term::arrow(cn("A"), cn("A"))).unwrap();
        k.add_axiom("g", 0, Term::arrow(cn("A"), cn("A"))).unwrap();
        k
    }

    // ---- Basic Path/PathP typing ----

    #[test]
    fn refl_typechecks() {
        let k = base_env();
        let a = cn("a");
        let p = refl(&a);
        let ty = k.infer(&p).unwrap();
        assert!(k.def_eq(&ty, &Term::path(cn("A"), a.clone(), a)));
    }

    #[test]
    fn refl_check_against_path_type() {
        let k = base_env();
        let a = cn("a");
        k.check(&refl(&a), &Term::path(cn("A"), a.clone(), a)).unwrap();
    }

    #[test]
    fn non_dependent_path_is_pathp_with_constant_family() {
        // `Path A a b` unfolds (structurally) to `PathP (A lifted) a b`; both spellings
        // check the same closed proof.
        let k = base_env();
        let a = cn("a");
        k.check(&refl(&a), &Term::pathp(cn("A").lift(1, 0), a.clone(), a)).unwrap();
    }

    // ---- Boundary computation (definitional) ----

    #[test]
    fn boundary_i0_computes_via_kernel_def_eq() {
        let k = base_env();
        // (refl a) @ i0  ≡  a
        let app0 = Term::papp(refl(&cn("a")), Term::IZero);
        assert!(k.def_eq(&app0, &cn("a")));
    }

    #[test]
    fn boundary_i1_computes_via_kernel_def_eq() {
        let k = base_env();
        let app1 = Term::papp(refl(&cn("a")), Term::IOne);
        assert!(k.def_eq(&app1, &cn("a")));
    }

    /// Differential check (matching this crate's standing convention): the trusted
    /// reducer and NbE agree on the boundary reduction.
    #[test]
    fn boundary_reduction_agrees_between_reducer_and_nbe() {
        let k = base_env();
        let app0 = Term::papp(refl(&cn("a")), Term::IZero);
        let app1 = Term::papp(refl(&cn("a")), Term::IOne);
        let reducer = crate::reduce::Reducer::new(k.env());
        let nbe = crate::nbe::Nbe::new(k.env());
        assert!(reducer.is_def_eq(&app0, &cn("a")));
        assert!(reducer.is_def_eq(&app1, &cn("a")));
        assert!(nbe.conv(&app0, &cn("a")));
        assert!(nbe.conv(&app1, &cn("a")));
    }

    /// A non-constant path: `⟨i⟩ (if-you-squint) …` — here just an interval variable
    /// applied through a Π (built directly): `PLam(Var(0))` has type `PathP (λi. I)
    /// …`? No — `Var(0)` inside a `PLam` body, applied to itself, is ill-typed at
    /// the outer level. Instead exercise a *non-trivial* body: `⟨i⟩ f (p @ i)`-shaped
    /// (i.e. `ap`), and check both boundaries against `f a`/`f b` for a genuine
    /// (non-refl) path `p : Path A a b` assumed as an axiom.
    #[test]
    fn ap_boundaries_compute() {
        let mut k = base_env();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        let term = ap(&cn("f"), &cn("p"));
        let ty = k.infer(&term).unwrap();
        let expected =
            Term::path(cn("A"), Term::app(cn("f"), cn("a")), Term::app(cn("f"), cn("b")));
        assert!(k.def_eq(&ty, &expected));
    }

    // ---- funext ----

    #[test]
    fn funext_typechecks() {
        let mut k = base_env();
        // h : Π x:A. Path A (f x) (g x)
        let h_ty = Term::pi(
            cn("A"),
            Term::path(cn("A"), Term::app(cn("f"), Term::Var(0)), Term::app(cn("g"), Term::Var(0))),
        );
        k.add_axiom("h", 0, h_ty).unwrap();
        let fe = funext(&cn("A"), &cn("h"));
        let ty = k.infer(&fe).unwrap();
        let expected = Term::path(Term::arrow(cn("A"), cn("A")), cn("f"), cn("g"));
        assert!(k.def_eq(&ty, &expected));
        k.check(&fe, &expected).unwrap();
    }

    // ---- Adversarial: no way to derive `False`/lie about endpoints ----

    /// A `PLam` cannot be checked against a `Path` type whose declared endpoints
    /// don't match what the body actually computes to at `i0`/`i1` — the endpoints
    /// are *read off the body*, not asserted, so this must be rejected.
    #[test]
    fn plam_cannot_lie_about_its_endpoints() {
        let k = base_env();
        // refl a : Path A a a, NOT Path A a b (a and b are distinct axioms — no
        // conversion between them).
        let claimed = Term::path(cn("A"), cn("a"), cn("b"));
        let err = k.check(&refl(&cn("a")), &claimed).unwrap_err();
        assert!(err.contains("type mismatch") || err.contains("does not match"), "got: {err}");
    }

    /// Two distinct closed axioms are never definitionally equal — a `Path` between
    /// them cannot be conjured out of nothing (matches the pre-existing kernel's
    /// treatment of any two distinct axioms/constructors, e.g. `Eq`; Phase-1 `Path`
    /// adds no new source of equations between unrelated closed terms).
    #[test]
    fn distinct_closed_values_have_no_path_between_them() {
        let k = base_env();
        assert!(!k.def_eq(&cn("a"), &cn("b")));
        // And indeed: no closed term of type `Path A a b` can be built from `a`/`b`
        // alone (`refl` only ever proves reflexivity).
        assert!(k.check(&refl(&cn("a")), &Term::path(cn("A"), cn("a"), cn("b"))).is_err());
    }

    /// `I` is not `Type`: it cannot be used as a `Π` domain (nor codomain) — nothing
    /// can quantify a real, fibrant type over the interval yet (no Kan/transport).
    #[test]
    fn interval_is_not_a_type() {
        let mut k = Kernel::new();
        let err = k.add_axiom("bad", 0, Term::pi(Term::I, Term::typ(0))).unwrap_err();
        assert!(err.contains('I'), "expected the error to mention `I`, got: {err}");
    }

    /// `I` cannot be checked as an ordinary *value* either (e.g. handed somewhere a
    /// `Type`-classified term is expected) — `infer(I)` is rejected outright.
    #[test]
    fn interval_is_not_checkable_as_a_value() {
        let k = Kernel::new();
        assert!(k.infer(&Term::I).is_err());
    }

    /// A bound interval variable cannot leak into a position that expects ordinary
    /// data: applying a genuine function to a raw path-abstraction's bound interval
    /// variable is ill-typed (its type is `I`, which is never definitionally equal to
    /// any real domain type).
    #[test]
    fn interval_variable_cannot_be_used_as_data() {
        let k = base_env();
        // `⟨i⟩ f i`  — using the bound interval variable where `f : A -> A` expects an
        // `A`. Must be rejected (the interval variable's type is `I`, not `A`).
        let bad = Term::plam(Term::app(cn("f").lift(1, 0), Term::Var(0)));
        assert!(k.infer(&bad).is_err());
    }

    /// `p @ r` requires `r : I` — applying a path to an ordinary data value (not an
    /// interval term) must be rejected.
    #[test]
    fn path_application_rejects_non_interval_argument() {
        let k = base_env();
        let bad = Term::papp(refl(&cn("a")), cn("a")); // `a : A`, not `: I`
        assert!(k.infer(&bad).is_err());
    }

    /// A **neutral** path's boundary (`h @ i0` for an axiom `h`) is forced *exactly*
    /// to its declared endpoint (`a`, here) by the type-directed boundary rule — and
    /// *only* to that endpoint: it is not conflated with an unrelated closed value
    /// `c` that happens to share `h`'s type. The rule reads the target off `p`'s own
    /// checked type; it doesn't equate `p @ i0` with anything else.
    #[test]
    fn neutral_path_application_resolves_to_its_declared_endpoint_only() {
        let mut k = base_env();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        let p_at_i0 = Term::papp(cn("p"), Term::IZero);
        assert!(k.def_eq(&p_at_i0, &cn("a"))); // the declared left endpoint
        assert!(!k.def_eq(&p_at_i0, &cn("c"))); // not an unrelated value
        assert!(!k.def_eq(&p_at_i0, &cn("b"))); // not the *other* endpoint either
    }

    /// Applying two axiomatized, unrelated paths at the same interval endpoint
    /// resolves each to its *own* declared endpoint, and those aren't conflated with
    /// each other merely because both applications are "at `i0`".
    #[test]
    fn distinct_neutral_paths_stay_distinct_at_shared_boundary() {
        let mut k = base_env();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        k.add_axiom("q", 0, Term::path(cn("A"), cn("b"), cn("c"))).unwrap();
        let p0 = Term::papp(cn("p"), Term::IZero);
        let q0 = Term::papp(cn("q"), Term::IZero);
        assert!(!k.def_eq(&p0, &q0));
    }

    /// Sanity: an environment with `Path`/`PathP` axioms and proofs re-checks cleanly
    /// under the independent re-check harness (mirrors `kernel::recheck_all_definitions`'s
    /// existing coverage, extended to Phase-1 terms).
    #[test]
    fn cubical_definitions_survive_independent_recheck() {
        let mut k = base_env();
        k.add_definition(
            "refl_a",
            0,
            Term::path(cn("A"), cn("a"), cn("a")),
            refl(&cn("a")),
        )
        .unwrap();
        k.add_definition(
            "ap_f_refl_a",
            0,
            Term::path(cn("A"), Term::app(cn("f"), cn("a")), Term::app(cn("f"), cn("a"))),
            ap(&cn("f"), &cn("refl_a")),
        )
        .unwrap();
        assert_eq!(crate::kernel::recheck_all_definitions(k.env()).unwrap(), 2);
    }

    /// Polymorphic sanity: `refl`/`Path` also work at `Type 1` (universe-generic use),
    /// not just `Prop`/`Type 0` — nothing here is hard-wired to a specific level.
    #[test]
    fn path_at_higher_universe() {
        let mut k = Kernel::new();
        k.add_axiom("T", 0, Term::typ(1)).unwrap(); // T : Type 1
        let t = cn("T");
        k.add_axiom("x", 0, t.clone()).unwrap();
        let p = refl(&cn("x"));
        let ty = k.infer(&p).unwrap();
        assert!(k.def_eq(&ty, &Term::path(t, cn("x"), cn("x"))));
    }
}

/// **Phase 3.5**: the De Morgan interval — connections (`~`/`∧`/`∨`), definitional
/// normalization, and the corresponding face-lattice/boundary extensions. See this
/// module's "Phase 3.5" doc section above for the laws and the soundness argument
/// (conservative extension: no new fibrant elimination, no box-filling).
#[cfg(test)]
mod phase_3_5_tests {
    use super::*;
    use crate::face::{entails, is_false, is_true, Cof};
    use crate::kernel::Kernel;
    use crate::term::name;

    fn v(i: usize) -> Term {
        Term::Var(i)
    }
    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    // ---- normalize_interval: every De Morgan law, decided definitionally ----

    #[test]
    fn neg_i0_is_i1_and_vice_versa() {
        assert_eq!(normalize_interval(&Term::ineg(Term::IZero)), normalize_interval(&Term::IOne));
        assert!(interval_eq(&Term::ineg(Term::IZero), &Term::IOne));
        assert_eq!(normalize_interval(&Term::ineg(Term::IOne)), normalize_interval(&Term::IZero));
        assert!(interval_eq(&Term::ineg(Term::IOne), &Term::IZero));
    }

    #[test]
    fn double_negation() {
        let r = v(0);
        assert!(interval_eq(&Term::ineg(Term::ineg(r.clone())), &r));
    }

    #[test]
    fn de_morgan_duality_neg_meet() {
        // ~(r∧s) = ~r ∨ ~s
        let (r, s) = (v(0), v(1));
        let lhs = Term::ineg(Term::imeet(r.clone(), s.clone()));
        let rhs = Term::ijoin(Term::ineg(r), Term::ineg(s));
        assert!(interval_eq(&lhs, &rhs));
    }

    #[test]
    fn de_morgan_duality_neg_join() {
        // ~(r∨s) = ~r ∧ ~s
        let (r, s) = (v(0), v(1));
        let lhs = Term::ineg(Term::ijoin(r.clone(), s.clone()));
        let rhs = Term::imeet(Term::ineg(r), Term::ineg(s));
        assert!(interval_eq(&lhs, &rhs));
    }

    #[test]
    fn idempotence() {
        let r = v(0);
        assert!(interval_eq(&Term::imeet(r.clone(), r.clone()), &r));
        assert!(interval_eq(&Term::ijoin(r.clone(), r.clone()), &r));
    }

    #[test]
    fn commutativity() {
        let (r, s) = (v(0), v(1));
        assert!(interval_eq(&Term::imeet(r.clone(), s.clone()), &Term::imeet(s.clone(), r.clone())));
        assert!(interval_eq(&Term::ijoin(r.clone(), s.clone()), &Term::ijoin(s, r)));
    }

    #[test]
    fn associativity() {
        let (r, s, t) = (v(0), v(1), v(2));
        let lhs = Term::imeet(Term::imeet(r.clone(), s.clone()), t.clone());
        let rhs = Term::imeet(r.clone(), Term::imeet(s.clone(), t.clone()));
        assert!(interval_eq(&lhs, &rhs));
        let lhs = Term::ijoin(Term::ijoin(r.clone(), s.clone()), t.clone());
        let rhs = Term::ijoin(r, Term::ijoin(s, t));
        assert!(interval_eq(&lhs, &rhs));
    }

    #[test]
    fn absorption() {
        let (r, s) = (v(0), v(1));
        // r ∧ (r ∨ s) = r
        assert!(interval_eq(&Term::imeet(r.clone(), Term::ijoin(r.clone(), s.clone())), &r));
        // r ∨ (r ∧ s) = r
        assert!(interval_eq(&Term::ijoin(r.clone(), Term::imeet(r.clone(), s)), &r));
    }

    #[test]
    fn bounded_lattice_laws() {
        let r = v(0);
        assert!(interval_eq(&Term::imeet(r.clone(), Term::IZero), &Term::IZero)); // r∧i0=i0
        assert!(interval_eq(&Term::ijoin(r.clone(), Term::IOne), &Term::IOne)); // r∨i1=i1
        assert!(interval_eq(&Term::imeet(r.clone(), Term::IOne), &r)); // r∧i1=r
        assert!(interval_eq(&Term::ijoin(r.clone(), Term::IZero), &r)); // r∨i0=r
    }

    /// **Adversarial**: the Boolean complement law `r ∧ ~r = i0` must NOT hold —
    /// assuming it would be unsound (see the module doc). `i ∧ ~i` must stay a
    /// distinct, *stuck* interval term from the literal `i0`, not collapse to it.
    #[test]
    fn the_boolean_law_does_not_hold() {
        let r = v(0);
        let meet_with_neg = Term::imeet(r.clone(), Term::ineg(r.clone()));
        assert!(!interval_eq(&meet_with_neg, &Term::IZero), "r ∧ ~r must NOT normalize to i0");
        let join_with_neg = Term::ijoin(r.clone(), Term::ineg(r));
        assert!(!interval_eq(&join_with_neg, &Term::IOne), "r ∨ ~r must NOT normalize to i1");
    }

    /// Distinct variables are never conflated by normalization.
    #[test]
    fn distinct_variables_stay_distinct() {
        assert!(!interval_eq(&v(0), &v(1)));
        assert!(!interval_eq(&Term::ineg(v(0)), &v(0)));
    }

    /// `normalize_interval` is idempotent (already-normal terms are a fixed point) —
    /// a basic sanity check that the canonical form is actually canonical.
    #[test]
    fn normalize_is_idempotent() {
        let t = Term::ijoin(Term::imeet(v(0), v(1)), Term::ineg(v(2)));
        let n1 = normalize_interval(&t);
        let n2 = normalize_interval(&n1);
        assert_eq!(n1, n2);
    }

    // ---- Face-lattice extension: entailment decides connections ----

    #[test]
    fn meet_eq_1_entails_each_conjunct_eq_1() {
        // (i∧j=1) ⊢ (i=1)
        let phi = Cof::eq1(Term::imeet(v(0), v(1)));
        assert!(entails(&phi, &Cof::eq1(v(0))));
        assert!(entails(&phi, &Cof::eq1(v(1))));
    }

    #[test]
    fn eq_1_entails_join_eq_1() {
        // (i=1) ⊢ (i∨j=1)
        let phi = Cof::eq1(v(0));
        let psi = Cof::eq1(Term::ijoin(v(0), v(1)));
        assert!(entails(&phi, &psi));
    }

    #[test]
    fn neg_eq_1_iff_eq_0() {
        // ~i=1 ⊣⊢ i=0
        let neg_eq1 = Cof::eq1(Term::ineg(v(0)));
        let eq0 = Cof::eq0(v(0));
        assert!(entails(&neg_eq1, &eq0));
        assert!(entails(&eq0, &neg_eq1));
    }

    #[test]
    fn neg_eq_0_iff_eq_1() {
        let neg_eq0 = Cof::eq0(Term::ineg(v(0)));
        let eq1 = Cof::eq1(v(0));
        assert!(entails(&neg_eq0, &eq1));
        assert!(entails(&eq1, &neg_eq0));
    }

    #[test]
    fn join_eq_0_iff_both_eq_0() {
        // (i∨j=0) ⊣⊢ (i=0)∧(j=0)
        let phi = Cof::eq0(Term::ijoin(v(0), v(1)));
        let psi = Cof::and(Cof::eq0(v(0)), Cof::eq0(v(1)));
        assert!(entails(&phi, &psi));
        assert!(entails(&psi, &phi));
    }

    /// The `i0 ≠ i1` clash, reached *through* a connection: `(~i=1) ∧ (i=1)` forces
    /// `i=0` and `i=1` simultaneously ⇒ `⊥`.
    #[test]
    fn clash_through_negation_is_false() {
        let phi = Cof::and(Cof::eq1(Term::ineg(v(0))), Cof::eq1(v(0)));
        assert!(is_false(&phi));
    }

    /// `(i∧j = 1)` is genuinely satisfiable (not `⊥`) — decomposition must not
    /// over-collapse a satisfiable conjunction.
    #[test]
    fn meet_eq_1_is_satisfiable() {
        let phi = Cof::eq1(Term::imeet(v(0), v(1)));
        assert!(!is_false(&phi));
    }

    /// `~i0 = 1` is literally `i1 = 1`, hence unconditionally true — decided through
    /// the connection decomposition, not just literal-endpoint matching.
    #[test]
    fn neg_of_literal_endpoint_decides() {
        assert!(is_true(&Cof::eq1(Term::ineg(Term::IZero))));
        assert!(is_false(&Cof::eq0(Term::ineg(Term::IZero))));
    }

    // ---- Boundary computation with connection substitution ----

    /// `A B : Type 0`, `a b : A`.
    fn base_env() -> Kernel {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        k.add_axiom("b", 0, cn("A")).unwrap();
        k
    }

    /// `(refl a) @ (i ∧ ~i)` still computes to `a` for *any* interval expression
    /// substituted for `r` in `(⟨i⟩ a) @ r ↦ a` — connections included, since the
    /// body doesn't mention the bound variable at all. Exercises that connection
    /// terms flow correctly through `PApp`'s substitution.
    #[test]
    fn boundary_computes_under_a_connection_argument() {
        let k = base_env();
        let arg = Term::imeet(Term::Var(0), Term::ineg(Term::Var(0)));
        // Build inside a context with one bound interval variable in scope.
        let mut ctx = crate::check::LocalCtx::new();
        ctx.push(Term::I);
        let app = Term::papp(refl(&cn("a")).lift(1, 0), arg);
        assert!(k.checker().is_def_eq(&mut ctx, &app, &cn("a").lift(1, 0)));
    }

    /// `(⟨i⟩ f (p @ i)) @ (~i0)` — substituting the *literal* `~i0` (which normalizes
    /// to `i1`) into a genuinely `i`-dependent body must compute to the `i1` boundary,
    /// exactly as substituting `i1` directly would.
    #[test]
    fn connection_argument_hits_the_right_boundary() {
        let mut k = base_env();
        k.add_axiom("f", 0, Term::arrow(cn("A"), cn("A"))).unwrap();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        let term = ap(&cn("f"), &cn("p"));
        // `term @ (~i0)` should equal `term @ i1` should equal `f b`.
        let at_neg_i0 = Term::papp(term.clone(), Term::ineg(Term::IZero));
        let expected = Term::app(cn("f"), cn("b"));
        assert!(k.def_eq(&at_neg_i0, &expected));
    }

    // ---- `I` remains non-fibrant with connections in scope ----

    #[test]
    fn interval_still_not_a_pi_domain_with_connections_in_scope() {
        let mut k = Kernel::new();
        let err = k.add_axiom("bad", 0, Term::pi(Term::I, Term::typ(0))).unwrap_err();
        assert!(err.contains('I'), "got: {err}");
    }

    /// A connection expression itself is `I`-typed, never a genuine `Type`/value —
    /// `infer` on a bare `INeg`/`IMeet`/`IJoin` at top level (no interval context)
    /// still fails exactly as `Term::IZero` bare-checked-as-a-domain would.
    #[test]
    fn connection_cannot_smuggle_data_into_a_pi_domain() {
        let mut k = Kernel::new();
        // `Π (_ : ~i0). Type 0` — `~i0 : I`, not a `Sort`, so this must be rejected
        // for the same reason `Π (_ : I). Type 0` is.
        let err = k.add_axiom("bad", 0, Term::pi(Term::ineg(Term::IZero), Term::typ(0))).unwrap_err();
        assert!(!err.is_empty());
    }

    /// A malformed connection (operand not `: I`) is rejected by `infer`, mirroring
    /// `Term::PApp`'s existing check that its argument is interval-classified.
    #[test]
    fn ill_typed_connection_operand_is_rejected() {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        // `~a` where `a : A`, not `: I`.
        assert!(k.infer(&Term::ineg(cn("a"))).is_err());
    }

    /// `normalize_interval` is total (never panics) even on a deeply nested,
    /// non-trivial expression mixing all three connectives and several variables.
    #[test]
    fn normalize_interval_is_total_on_deep_nesting() {
        // Deliberately modest depth: the DNF-based normal form is (as documented)
        // worst-case exponential in the number of distinct variables — same as
        // `crate::face`'s pre-existing `to_dnf` for cofibrations — so this checks
        // *totality* (terminates, doesn't panic), not asymptotic performance.
        let mut t = v(0);
        for i in 1..7 {
            t = Term::ijoin(Term::imeet(t.clone(), v(i)), Term::ineg(t));
        }
        let _ = normalize_interval(&t); // must not panic
    }
}

/// Phase 3.7: [`transport`]/[`subst`] and the `Path ↔ Eq` bridge (see the module
/// doc section above, "Phase 3.7").
#[cfg(test)]
mod bridge_tests {
    use super::*;
    use crate::inductive::declare_eq;
    use crate::kernel::Kernel;
    use crate::level::Level;
    use crate::term::name;

    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    /// `A B : Type 0` (i.e. `Sort 1`), `a b c : A`, `f : A -> A`, plus `Eq`
    /// declared in the environment (needed for the bridge functions).
    fn base_env() -> Kernel {
        let mut k = Kernel::new();
        declare_eq(k.env_mut()).unwrap();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("B", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        k.add_axiom("b", 0, cn("A")).unwrap();
        k.add_axiom("c", 0, cn("A")).unwrap();
        k.add_axiom("f", 0, Term::arrow(cn("A"), cn("A"))).unwrap();
        k
    }

    // ---- transport ----

    /// `transport (refl A) a : A` — type-checks at exactly `A` (the trivial case).
    #[test]
    fn transport_along_refl_typechecks_at_the_same_type() {
        let k = base_env();
        let p = refl(&cn("A")); // Path Type A A
        let t = transport(&p, &cn("a"));
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &cn("A")));
    }

    /// **Completeness gap, now closed** (see `crate::kan::family_is_constant`'s doc):
    /// `transport (refl A) a` does *not* collapse to `a` via the *purely syntactic*
    /// `!mentions_var` check alone, because `(refl A) @ i` is `PApp(PLam(..), Var(0))`
    /// — a term that *does* mention `Var(0)` structurally — even though its value
    /// never varies. But `crate::kan::family_is_constant`'s normalization-aware
    /// extension *computes* the family under a fresh neutral standing in for `Var(0)`
    /// and finds the result genuinely constant, so the `Transp` now reduces, via both
    /// `Reducer::whnf` and `Nbe::eval`, to exactly `a` — no longer a stuck normal
    /// form. Also checked via `Nbe::normalize` for the reducer/NbE agreement this
    /// module's other tests hold to.
    #[test]
    fn transport_along_refl_now_computes_to_its_input() {
        let k = base_env();
        let p = refl(&cn("A"));
        let t = transport(&p, &cn("a"));
        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&t);
        assert_eq!(whnf, cn("a"), "expected transport(refl A, a) to reduce to a, got {}", whnf.pretty());
        let nbe = crate::nbe::Nbe::new(k.env());
        assert_eq!(nbe.normalize(&t), cn("a"));
    }

    /// **The real payoff**: transport along a genuine (axiomatized) path between two
    /// *distinct* closed types moves `a : A` to a well-typed value of `B`.
    #[test]
    fn transport_along_a_real_path_moves_between_distinct_types() {
        let mut k = base_env();
        k.add_axiom("p", 0, Term::path(Term::typ(0), cn("A"), cn("B"))).unwrap();
        let t = transport(&cn("p"), &cn("a"));
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &cn("B")));
    }

    /// **Adversarial (anti-`False`)**: `transport` cannot be used to manufacture a
    /// value of an *unrelated*, path-free axiom type `C` — the underlying `Transp`
    /// still requires `a`'s checked type to match the family's `i0` boundary.
    #[test]
    fn transport_cannot_smuggle_a_value_into_an_unrelated_type_without_a_path() {
        let mut k = base_env();
        k.add_axiom("C", 0, Term::typ(0)).unwrap();
        // No path A -> C: build a fake "path" shape (refl C, wrong endpoint story)
        // applied to `a : A` — must fail to type-check.
        let fake_p = refl(&cn("C"));
        let t = transport(&fake_p, &cn("a"));
        assert!(k.infer(&t).is_err());
    }

    /// **Adversarial**: `transport` along a real `A`↔`B` path never produces a value
    /// definitionally equal to some *other*, unrelated closed term of `B` — it stays
    /// tied to (only) `a`, never conjuring `False`-style equations between `A`'s and
    /// `B`'s distinct inhabitants.
    #[test]
    fn transport_result_is_not_confused_with_an_unrelated_b_value() {
        let mut k = base_env();
        k.add_axiom("p", 0, Term::path(Term::typ(0), cn("A"), cn("B"))).unwrap();
        k.add_axiom("bb", 0, cn("B")).unwrap();
        let t = transport(&cn("p"), &cn("a"));
        // `t` stays a stuck, opaque `Transp` (family genuinely varies through the
        // axiom `p`) — it must not be equated with an unrelated `B`-typed axiom.
        assert!(!k.def_eq(&t, &cn("bb")));
    }

    // ---- subst ----

    /// `subst (λ_. A) (refl A) a` — trivial motive, type-checks at `A`.
    #[test]
    fn subst_with_constant_motive_typechecks() {
        let k = base_env();
        let motive = Term::lam(cn("A"), cn("A").lift(1, 0));
        let p = refl(&cn("a"));
        let t = subst(&motive, &p, &cn("a"));
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &cn("A")));
    }

    /// The real use: `motive := λ x. Eq A a x` isn't needed here (that's
    /// `path_to_eq`'s job) — instead exercise a genuinely *varying* predicate:
    /// `motive := λ x. Path A a x`, transporting `refl a : motive a` along a real
    /// path `p : Path A a b` to land at `motive b = Path A a b`.
    #[test]
    fn subst_transports_a_varying_predicate() {
        let mut k = base_env();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        let motive = Term::lam(cn("A"), Term::path(cn("A").lift(1, 0), cn("a").lift(1, 0), Term::Var(0)));
        let pa = refl(&cn("a")); // : motive a = Path A a a
        let t = subst(&motive, &cn("p"), &pa);
        let ty = k.infer(&t).unwrap();
        let expected = Term::path(cn("A"), cn("a"), cn("b"));
        assert!(k.def_eq(&ty, &expected));
    }

    /// **Adversarial**: `subst` requires the supplied `pa` to actually inhabit
    /// `motive a` (the family's `i0` boundary) — a mismatched `pa` is rejected.
    #[test]
    fn subst_rejects_a_mismatched_starting_proof() {
        let mut k = base_env();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        let motive = Term::lam(cn("A"), Term::path(cn("A").lift(1, 0), cn("a").lift(1, 0), Term::Var(0)));
        // Wrong starting proof: `refl c : Path A c c`, not `Path A a a`.
        let bad_pa = refl(&cn("c"));
        let t = subst(&motive, &cn("p"), &bad_pa);
        assert!(k.infer(&t).is_err());
    }

    // ---- Path ↔ Eq bridge ----

    /// `path_to_eq (refl a) : Eq A a a` — the round-trip's base case: reflexivity in,
    /// reflexivity out.
    #[test]
    fn path_to_eq_of_refl_lands_at_refl() {
        let k = base_env();
        let p = refl(&cn("a"));
        let e = path_to_eq(Level::of_nat(1), &cn("A"), &cn("a"), &p);
        let ty = k.infer(&e).unwrap();
        let expected_ty = Term::apps(
            Term::cnst(name("Eq"), vec![Level::of_nat(1)]),
            [cn("A"), cn("a"), cn("a")],
        );
        assert!(k.def_eq(&ty, &expected_ty));
    }

    /// `path_to_eq p : Eq A a b` for a genuine (axiomatized) non-reflexive path.
    #[test]
    fn path_to_eq_of_a_real_path_lands_at_the_right_endpoints() {
        let mut k = base_env();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        let e = path_to_eq(Level::of_nat(1), &cn("A"), &cn("a"), &cn("p"));
        let ty = k.infer(&e).unwrap();
        let expected_ty = Term::apps(
            Term::cnst(name("Eq"), vec![Level::of_nat(1)]),
            [cn("A"), cn("a"), cn("b")],
        );
        assert!(k.def_eq(&ty, &expected_ty));
    }

    /// `eq_to_path (Eq.refl a) : Path A a a` — the converse round-trip's base case.
    #[test]
    fn eq_to_path_of_refl_lands_at_refl() {
        let k = base_env();
        let refl_a =
            Term::apps(Term::cnst(name("Eq.refl"), vec![Level::of_nat(1)]), [cn("A"), cn("a")]);
        let p = eq_to_path(Level::of_nat(1), &cn("A"), &cn("a"), &cn("a"), &refl_a);
        let ty = k.infer(&p).unwrap();
        let expected_ty = Term::path(cn("A"), cn("a"), cn("a"));
        assert!(k.def_eq(&ty, &expected_ty));
        // And it genuinely reduces to the *literal* `refl a` (Eq.rec's ι-rule fires
        // on the literal `Eq.refl` constructor, exactly as `Nat.rec` does on
        // `Nat.zero`/`Nat.succ` — see `crate::inductive`).
        assert!(k.def_eq(&p, &refl(&cn("a"))));
    }

    /// `eq_to_path h : Path A a b` for a genuine (axiomatized, non-refl) `Eq`
    /// witness `h : Eq A a b`.
    #[test]
    fn eq_to_path_of_a_real_eq_witness_lands_at_the_right_endpoints() {
        let mut k = base_env();
        let eq_a_b = Term::apps(Term::cnst(name("Eq"), vec![Level::of_nat(1)]), [cn("A"), cn("a"), cn("b")]);
        k.add_axiom("h", 0, eq_a_b).unwrap();
        let p = eq_to_path(Level::of_nat(1), &cn("A"), &cn("a"), &cn("b"), &cn("h"));
        let ty = k.infer(&p).unwrap();
        let expected_ty = Term::path(cn("A"), cn("a"), cn("b"));
        assert!(k.def_eq(&ty, &expected_ty));
    }

    /// **Round-trip**: `path_to_eq (eq_to_path h)` type-checks back at `Eq A a b`
    /// (the same type `h` itself has) for a genuine, non-reflexive `h`.
    #[test]
    fn eq_path_eq_round_trip_typechecks() {
        let mut k = base_env();
        let eq_a_b = Term::apps(Term::cnst(name("Eq"), vec![Level::of_nat(1)]), [cn("A"), cn("a"), cn("b")]);
        k.add_axiom("h", 0, eq_a_b.clone()).unwrap();
        let p = eq_to_path(Level::of_nat(1), &cn("A"), &cn("a"), &cn("b"), &cn("h"));
        let e = path_to_eq(Level::of_nat(1), &cn("A"), &cn("a"), &p);
        let ty = k.infer(&e).unwrap();
        assert!(k.def_eq(&ty, &eq_a_b));
    }

    /// **Round-trip**: `path_to_eq (refl a)` then `eq_to_path` of that lands back at
    /// `Path A a a`. Note: with `crate::kan::family_is_constant`'s
    /// normalization-aware regularity extension, `path_to_eq (refl a)`'s underlying
    /// `subst`/`Transp` family (`Eq A a ((refl a) @ i)`) now computes to the constant
    /// `Eq A a a`, so it reduces straight to the literal `Eq.refl A a` constructor —
    /// only the type is asserted here (not the further definitional-equality
    /// consequence), to keep this test focused on the round-trip's typing, but the
    /// underlying computation is no longer stuck.
    #[test]
    fn path_eq_path_round_trip_on_refl_typechecks() {
        let k = base_env();
        let p = refl(&cn("a"));
        let e = path_to_eq(Level::of_nat(1), &cn("A"), &cn("a"), &p);
        let p2 = eq_to_path(Level::of_nat(1), &cn("A"), &cn("a"), &cn("a"), &e);
        let ty = k.infer(&p2).unwrap();
        assert!(k.def_eq(&ty, &Term::path(cn("A"), cn("a"), cn("a"))));
    }

    /// **Adversarial (anti-`False`)**: `path_to_eq`/`eq_to_path` cannot manufacture
    /// a witness connecting two *unrelated* closed values absent an actual
    /// path/`Eq` proof — `path_to_eq` applied to a bogus "path" (built from `refl`
    /// at the wrong point) is rejected by the underlying `subst`/`transp` check.
    #[test]
    fn bridge_cannot_manufacture_a_witness_between_unrelated_values() {
        let k = base_env();
        // `refl b : Path A b b`, not `Path A a b` — using it where `path_to_eq`
        // expects a path *starting* at `a` must fail to type-check.
        let bogus_p = refl(&cn("b"));
        let e = path_to_eq(Level::of_nat(1), &cn("A"), &cn("a"), &bogus_p);
        assert!(k.infer(&e).is_err());
    }

    /// **Adversarial**: distinct closed axioms `a`/`b`/`c` are never conflated by
    /// the bridge — `eq_to_path` of a genuine `h : Eq A a b` never type-checks as
    /// `Path A a c` (a different, unrelated target).
    #[test]
    fn eq_to_path_result_is_not_confused_with_an_unrelated_endpoint() {
        let mut k = base_env();
        let eq_a_b = Term::apps(Term::cnst(name("Eq"), vec![Level::of_nat(1)]), [cn("A"), cn("a"), cn("b")]);
        k.add_axiom("h", 0, eq_a_b).unwrap();
        let p = eq_to_path(Level::of_nat(1), &cn("A"), &cn("a"), &cn("b"), &cn("h"));
        let ty = k.infer(&p).unwrap();
        assert!(!k.def_eq(&ty, &Term::path(cn("A"), cn("a"), cn("c"))));
    }

    /// Sanity: definitions built through the bridge survive the independent recheck
    /// harness (mirrors this crate's standing discipline for every phase).
    #[test]
    fn bridge_definitions_survive_independent_recheck() {
        let mut k = base_env();
        let refl_a =
            Term::apps(Term::cnst(name("Eq.refl"), vec![Level::of_nat(1)]), [cn("A"), cn("a")]);
        let expected_ty = Term::apps(
            Term::cnst(name("Eq"), vec![Level::of_nat(1)]),
            [cn("A"), cn("a"), cn("a")],
        );
        let e = path_to_eq(Level::of_nat(1), &cn("A"), &cn("a"), &refl(&cn("a")));
        k.add_definition("e", 0, expected_ty, e).unwrap();
        let p = eq_to_path(Level::of_nat(1), &cn("A"), &cn("a"), &cn("a"), &refl_a);
        k.add_definition("p", 0, Term::path(cn("A"), cn("a"), cn("a")), p).unwrap();
        assert_eq!(crate::kernel::recheck_all_definitions(k.env()).unwrap(), 2);
    }

    // ---- worked demonstration: cubical funext -> Eq-level function equality ----

    /// `funext h : Path (A -> A) f g` (Phase 1's cubical `funext`, given pointwise
    /// paths `h`), turned into an `Eq`-level function equality via [`path_to_eq`] —
    /// the demonstration the task calls for: cubical `funext`/`ap`/`transport`
    /// feeding an `Eq`-based goal, exactly the shape the existing `Eq`-based proof
    /// corpus (`examples/proofs/*.rv`) is written against.
    #[test]
    fn funext_bridges_into_an_eq_level_function_equality() {
        let mut k = base_env();
        k.add_axiom("g", 0, Term::arrow(cn("A"), cn("A"))).unwrap();
        // h : Π x:A. Path A (f x) (g x)
        let h_ty = Term::pi(
            cn("A"),
            Term::path(cn("A"), Term::app(cn("f"), Term::Var(0)), Term::app(cn("g"), Term::Var(0))),
        );
        k.add_axiom("h", 0, h_ty).unwrap();
        let fe = funext(&cn("A"), &cn("h")); // : Path (A -> A) f g
        let arrow_ty = Term::arrow(cn("A"), cn("A"));
        k.check(&fe, &Term::path(arrow_ty.clone(), cn("f"), cn("g"))).unwrap();

        // Bridge it: Eq (A -> A) f g.
        let e = path_to_eq(Level::of_nat(1), &arrow_ty, &cn("f"), &fe);
        let ty = k.infer(&e).unwrap();
        let expected = Term::apps(
            Term::cnst(name("Eq"), vec![Level::of_nat(1)]),
            [arrow_ty, cn("f"), cn("g")],
        );
        assert!(k.def_eq(&ty, &expected));
    }
}

/// Phase 3.9: [`j`] (path induction) — see the module doc section above.
#[cfg(test)]
mod j_tests {
    use super::*;
    use crate::kernel::Kernel;
    use crate::term::name;

    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    /// `A B : Type 0`, `a b c : A`, `f : A -> A`.
    fn base_env() -> Kernel {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        k.add_axiom("b", 0, cn("A")).unwrap();
        k.add_axiom("c", 0, cn("A")).unwrap();
        k.add_axiom("f", 0, Term::arrow(cn("A"), cn("A"))).unwrap();
        k
    }

    /// `C := λ (x:A) (_: Path A base x). Path A base x` — the "identity" motive
    /// (varies in `x`, ignores the path witness itself): `C base p` is `Path A base
    /// base`/`Path A base x` respectively. A minimal but genuinely `x`-dependent
    /// motive, used throughout this module's tests.
    fn identity_motive(base: &Term) -> Term {
        Term::lam(
            cn("A"),
            Term::lam(
                Term::path(cn("A"), base.lift(1, 0), Term::Var(0)),
                Term::path(cn("A"), base.lift(2, 0), Term::Var(1)),
            ),
        )
    }

    // ---- (1) `J` type-checks at its full stated type, on concrete instances ----

    /// The base (reflexivity) case: `J A a C d a (refl a) : C a (refl a)`, checked
    /// against the literal motive application.
    #[test]
    fn j_typechecks_on_refl() {
        let k = base_env();
        let a = cn("a");
        let c = identity_motive(&a);
        let d = refl(&a); // : C a (refl a) = Path A a a
        let term = j(&c, &d, &refl(&a));
        let ty = k.infer(&term).unwrap();
        let expected = Term::apps(c.clone(), [a.clone(), refl(&a)]);
        assert!(k.def_eq(&ty, &expected));
        k.check(&term, &expected).unwrap();
    }

    /// A genuinely non-reflexive, but still **concrete** (literal `PLam`-built, not
    /// axiomatized) path: `p := ap f q` for an axiomatized `q : Path A a b`, so `p :
    /// Path A (f a) (f b)`. `J` is instantiated with base point `f a` and endpoint
    /// `f b`, and must type-check at the literal `C (f b) p`. This is the "full
    /// generality" case the module doc above explains: `p` being a literal `PLam`
    /// (built by [`ap`]) is what lets `⟨j⟩ p @ (i1 ∧ j)` normalize back to `p`
    /// itself (general β on a literal `PLam`, plus the De Morgan-normal-form
    /// comparison of `i1 ∧ j` against `j`) without needing a general Path-η rule.
    #[test]
    fn j_typechecks_on_a_composite_path() {
        let mut k = base_env();
        k.add_axiom("q", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        let base = Term::app(cn("f"), cn("a")); // f a
        let p = ap(&cn("f"), &cn("q")); // : Path A (f a) (f b)
        let c = identity_motive(&base);
        let d = refl(&base); // : C (f a) (refl (f a))
        let term = j(&c, &d, &p);
        let ty = k.infer(&term).unwrap();
        let target = Term::app(cn("f"), cn("b")); // f b
        let expected = Term::apps(c.clone(), [target, p.clone()]);
        assert!(k.def_eq(&ty, &expected));
        k.check(&term, &expected).unwrap();
    }

    // ---- (2) Computation on `refl`: propositional, not definitional ----

    /// `J A a C d a (refl a)` type-checks at `C a (refl a)` (same type as `d`), and
    /// — now that `crate::kan::family_is_constant`'s normalization-aware regularity
    /// closes the completeness gap documented above ("Computation on `refl`") — it
    /// also *definitionally* reduces to `d` itself, via both `Reducer::whnf` and
    /// `Nbe::normalize`.
    #[test]
    fn j_on_refl_now_computes_to_d() {
        let k = base_env();
        let a = cn("a");
        let c = identity_motive(&a);
        let d = refl(&a);
        let term = j(&c, &d, &refl(&a));
        // It type-checks at exactly `d`'s type (propositional equality holds: both
        // inhabit `C a (refl a)`).
        let ty = k.infer(&term).unwrap();
        assert!(k.def_eq(&ty, &k.infer(&d).unwrap()));
        // And it is now syntactically `d` after whnf — no longer a stuck `Transp`.
        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&term);
        assert_eq!(whnf, d, "expected J(refl) to reduce to d, got {}", whnf.pretty());
        let nbe = crate::nbe::Nbe::new(k.env());
        assert_eq!(nbe.normalize(&term), nbe.normalize(&d));
    }

    // ---- (3) Worked lemma: transitivity of `Path`, derived via `J` ----
    //
    // `trans : Path A a b -> Path A b c -> Path A a c`, the standard `J`-based
    // construction: eliminate the *first* path `p : Path A a b` with motive
    // `C := λ (y:A) (_:Path A a y). Path A y c -> Path A a c`, base case `d :=
    // λ (q : Path A a c). q` (at `y = a`, `C a (refl a) = Path A a c -> Path A a
    // c`, and the identity function inhabits exactly that), giving `J A a C d b p
    // : Path A b c -> Path A a c`; apply that to `q : Path A b c`.

    /// `motive := λ (y:A) (_:Path A a y). Path A y c -> Path A a c`.
    fn trans_motive(a: &Term, c: &Term) -> Term {
        Term::lam(
            cn("A"),
            Term::lam(
                Term::path(cn("A"), a.lift(1, 0), Term::Var(0)),
                Term::arrow(
                    Term::path(cn("A"), Term::Var(1), c.lift(2, 0)),
                    Term::path(cn("A"), a.lift(2, 0), c.lift(2, 0)),
                ),
            ),
        )
    }

    /// `trans p q : Path A a c`, given `p : Path A a b`, `q : Path A b c` — built
    /// as `(J A a motive d b p) q` (see the module-doc-style comment above).
    fn trans(a: &Term, c: &Term, p: &Term, q: &Term) -> Term {
        let motive = trans_motive(a, c);
        // d : Path A a c -> Path A a c, the identity function.
        let d = Term::lam(Term::path(cn("A"), a.clone(), c.clone()), Term::Var(0));
        Term::app(j(&motive, &d, p), q.clone())
    }

    /// `trans` type-checks at `Path A a c` for concrete, literal-`PLam` `p`/`q`
    /// (`p := refl a`-composed-with-`ap`, mirroring `j_typechecks_on_a_composite_path`
    /// above), and — the demo's actual point — it type-checks at the *general*
    /// stated `trans` signature.
    #[test]
    fn trans_typechecks_on_concrete_paths() {
        let mut k = base_env();
        k.add_axiom("q1", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        k.add_axiom("q2", 0, Term::path(cn("A"), cn("b"), cn("c"))).unwrap();
        let a = cn("a");
        let c = cn("c");
        let term = trans(&a, &c, &cn("q1"), &cn("q2"));
        let ty = k.infer(&term).unwrap();
        let expected = Term::path(cn("A"), a, c);
        assert!(k.def_eq(&ty, &expected));
        k.check(&term, &expected).unwrap();
    }

    /// `trans (refl a) q : Path A a c` — the base-case shape, checked at the level
    /// of types (see [`j_on_refl_now_computes_to_d`] for the definitional-computation
    /// side of this same `J`-on-`refl` case).
    #[test]
    fn trans_of_refl_typechecks() {
        let mut k = base_env();
        k.add_axiom("q2", 0, Term::path(cn("A"), cn("a"), cn("c"))).unwrap();
        let a = cn("a");
        let c = cn("c");
        let term = trans(&a, &c, &refl(&a), &cn("q2"));
        let ty = k.infer(&term).unwrap();
        let expected = Term::path(cn("A"), a, c);
        assert!(k.def_eq(&ty, &expected));
    }

    // ---- (3.5) Payoff of path-η (`check.rs`/`nbe.rs`): `J` now type-checks on an
    // ---- **opaque** (axiomatized, non-`PLam`) path, not just literal `PLam`-built
    // ---- ones like `refl`/`ap` above. ----

    /// `J` on a genuinely opaque path `q : Path A a b` (an *axiom*, not built from
    /// `refl`/`ap`/any `Term::plam`). Before path-η this was exactly the
    /// documented gap in the module doc above ("A fully *opaque*/axiomatized `p`
    /// would additionally need a genuine, unconditional Path-η law, which Phase 1
    /// does not add"): the family's `i1` boundary `⟨j⟩ q @ (i1 ∧ j)` reduces (via
    /// `i1 ∧ j ⇝ j`, De Morgan) to `⟨j⟩ q @ j`, which needs to be recognized as
    /// equal to the neutral `q` itself — impossible by pure structural comparison
    /// when `q` has no `PLam` shape to reduce against. `check::Checker::compare`'s
    /// new `(Term::PLam(_), _)`/`(_, Term::PLam(_))` arms are exactly the missing
    /// piece: `⟨j⟩ q @ j` is a literal `PLam`, so it now compares against the
    /// neutral `q` via path-η, unconditionally. This confirms the payoff: `J`
    /// type-checks at its fully general stated type `C b q` for an opaque `q`.
    #[test]
    fn j_typechecks_on_an_opaque_axiomatized_path() {
        let mut k = base_env();
        k.add_axiom("q", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        let a = cn("a");
        let q = cn("q"); // opaque: an axiom, not a literal PLam-built path
        let c = identity_motive(&a);
        let d = refl(&a); // : C a (refl a)
        let term = j(&c, &d, &q);
        let ty = k.infer(&term).unwrap();
        let b = cn("b");
        let expected = Term::apps(c.clone(), [b, q.clone()]);
        assert!(k.def_eq(&ty, &expected), "J on an opaque path must now check at C b q");
        k.check(&term, &expected).unwrap();
    }

    /// Same payoff, exercised through the `trans` demo: `trans` now type-checks
    /// on two fully opaque axiomatized paths (previously only literal/`PLam`-built
    /// ones like `j_typechecks_on_a_composite_path` were guaranteed to work at the
    /// general signature without path-η).
    #[test]
    fn trans_typechecks_on_opaque_axiomatized_paths() {
        let mut k = base_env();
        k.add_axiom("q1", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        k.add_axiom("q2", 0, Term::path(cn("A"), cn("b"), cn("c"))).unwrap();
        let a = cn("a");
        let c = cn("c");
        let term = trans(&a, &c, &cn("q1"), &cn("q2"));
        let ty = k.infer(&term).unwrap();
        let expected = Term::path(cn("A"), a, c);
        assert!(k.def_eq(&ty, &expected));
        k.check(&term, &expected).unwrap();
    }

    // ---- (4) Adversarial: `J` cannot manufacture `C x p` (or `False`) from nothing ----

    /// `J` requires a real `d : C a (refl a)`: a mismatched `d` is rejected.
    #[test]
    fn j_rejects_a_mismatched_base_case() {
        let mut k = base_env();
        k.add_axiom("q", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        let a = cn("a");
        let c = identity_motive(&a);
        let bad_d = refl(&cn("b")); // : Path A b b, NOT `C a (refl a) = Path A a a`
        let term = j(&c, &bad_d, &cn("q"));
        assert!(k.infer(&term).is_err());
    }

    /// `J` cannot be used to conjure a `Path` between two *unrelated* closed axioms
    /// out of nothing: there is no way to supply a well-typed `p : Path A a c`
    /// (`a`/`c` distinct, unrelated axioms) without already having one, so no
    /// instantiation of `J` here type-checks into a `Path A a c` proof from thin
    /// air — attempting to use `refl a` where a genuine `Path A a c` witness is
    /// required is rejected.
    #[test]
    fn j_cannot_manufacture_a_path_between_unrelated_axioms_from_nothing() {
        let k = base_env();
        let a = cn("a");
        let c_val = cn("c");
        let c = identity_motive(&a);
        let d = refl(&a);
        // Using `refl a : Path A a a` where `p : Path A a c` is required (`c` a
        // distinct, unrelated axiom) must fail to type-check as `j(.., .., refl a)`
        // checked against `C c (refl a)` — `refl a`'s own type (`Path A a a`) is not
        // `Path A a c`.
        let bogus_p = refl(&a);
        let term = j(&c, &d, &bogus_p);
        let ty = k.infer(&term).unwrap();
        // Its *actual* inferred type is `C a (refl a)`, not `C c (something)` —
        // confirm it is not confused with the unrelated endpoint `c`.
        let bogus_target = Term::apps(c, [c_val, bogus_p]);
        assert!(!k.def_eq(&ty, &bogus_target));
    }

    /// Anti-`False`: no closed instantiation of `J` derives `Path Nat 0 1` (or
    /// anything at an inconsistent, `Empty`-like type) — this environment doesn't
    /// even have `Nat`/`Empty` in scope, so the only way to attempt it is via `A`'s
    /// two distinct axioms `a`/`b`, and (as above) that requires an actual `p :
    /// Path A a b` witness to begin with; `J` itself adds no way to fabricate one.
    #[test]
    fn j_adds_no_new_way_to_equate_distinct_axioms() {
        let k = base_env();
        assert!(!k.def_eq(&cn("a"), &cn("b")));
    }

    /// Sanity: `J`-built definitions (base case and the `trans` demo) survive the
    /// independent recheck harness.
    #[test]
    fn j_definitions_survive_independent_recheck() {
        let mut k = base_env();
        let a = cn("a");
        let c = identity_motive(&a);
        let d = refl(&a);
        let term = j(&c, &d, &refl(&a));
        let expected = Term::apps(c, [a.clone(), refl(&a)]);
        k.add_definition("j_refl", 0, expected, term).unwrap();

        k.add_axiom("q1", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        k.add_axiom("q2", 0, Term::path(cn("A"), cn("b"), cn("c"))).unwrap();
        let cc = cn("c");
        let trans_term = trans(&a, &cc, &cn("q1"), &cn("q2"));
        k.add_definition("trans_q1_q2", 0, Term::path(cn("A"), a, cc), trans_term).unwrap();

        assert_eq!(crate::kernel::recheck_all_definitions(k.env()).unwrap(), 2);
    }
}
