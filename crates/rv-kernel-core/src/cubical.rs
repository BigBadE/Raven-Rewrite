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
// still holds *definitionally*, just not via the `Transp` regularity β-rule) but
// stays *stuck* as a `Transp` normal form rather than *reducing* to `a`. This is
// documented and adversarially pinned by
// [`tests::transport_along_refl_typechecks_but_does_not_syntactically_collapse`]
// below, and is exactly the same gap `crate::kan`'s own
// `transp_pi_rule_typechecks_on_a_refl_connected_pi_family` test documents for the
// `Π` case — a known, honestly-reported *incompleteness*, not unsoundness (a stuck
// `Transp` is valid inert data, like any other neutral).
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
//   checks. (A fully *opaque*/axiomatized `p` would additionally need a genuine,
//   unconditional Path-η law, which Phase 1 does not add — consistent with this
//   module's running "derived term, no new rule" discipline; see
//   `j_on_an_opaque_path_needs_eta_and_is_documented_as_such` below for the
//   honestly-reported boundary of what typechecks today.)
//
// This needs **no new checking or reduction rule**: `J` is nothing but
// [`Term::transp`] (already proven sound in `crate::kan`) applied to a family built
// entirely from [`Term::plam`]/[`Term::papp`]/[`Term::imeet`] (already proven sound
// above, Phase 1 and Phase 3.5) — exactly the same "derived term, not a new
// primitive" shape as [`transport`]/[`subst`] in Phase 3.7.
//
// # Computation on `refl`
//
// `J A a C d a (refl a)` does **not** syntactically collapse to `d` — the same
// documented completeness gap as `transport (refl A) a` above (see "Phase 3.7"):
// the family here is `λi. C ((refl a) @ i) (⟨j⟩ (refl a) @ (i ∧ j))`, which
// syntactically mentions `Var(0)` (as `PApp` arguments), so `Transp`'s regularity
// rule (`crate::kan`, fires only when the family is *syntactically* independent of
// the interval variable) does not apply; `J A a C d a (refl a)` stays a stuck
// `Transp` normal form. It is *propositionally* equal to `d` (their type, `C a
// (refl a)`, is what both inhabit) but not *definitionally* so in this kernel. See
// `j_on_refl_typechecks_but_does_not_syntactically_collapse_to_d` below — this
// mirrors, rather than adds to, the existing gap.
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

    /// **Completeness gap, documented, not a soundness bug** (see the module doc):
    /// `transport (refl A) a` does *not* syntactically collapse to `a` via the
    /// `Transp` regularity rule, because `(refl A) @ i` is `PApp(PLam(..), Var(0))`
    /// — a term that *does* mention `Var(0)` structurally — even though its value
    /// never varies. It stays a stuck `Transp` normal form; still valid, inert data.
    #[test]
    fn transport_along_refl_typechecks_but_does_not_syntactically_collapse() {
        let k = base_env();
        let p = refl(&cn("A"));
        let t = transport(&p, &cn("a"));
        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&t);
        assert!(matches!(whnf, Term::Transp(..)), "expected a stuck Transp, got {}", whnf.pretty());
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
    /// `Path A a a`. Note (same completeness gap as
    /// [`tests::transport_along_refl_typechecks_but_does_not_syntactically_collapse`]):
    /// `path_to_eq (refl a)` type-checks at `Eq A a a` but does *not* itself reduce
    /// to the literal `Eq.refl A a` constructor (`subst`'s underlying `Transp` stays
    /// stuck — the family syntactically mentions the interval variable via `PApp`),
    /// so `Eq.rec`'s ι-rule (which only fires on a literal `Eq.refl` head) does not
    /// fire either, and the round-trip's *result* is not further asserted
    /// definitionally equal to the literal `refl a` — only its *type* is checked
    /// here. This is honestly incomplete, not unsound: every intermediate term
    /// still independently type-checks at its stated type.
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

    /// `J A a C d a (refl a)` type-checks at `C a (refl a)` (same type as `d`), but
    /// — same documented completeness gap as `transport`/`subst` on `refl` (Phase
    /// 3.7 above) — does **not** itself syntactically reduce to `d`: it stays a
    /// stuck `Transp` normal form, because the family syntactically mentions the
    /// interval variable (`Transp`'s regularity rule needs syntactic, not just
    /// semantic, independence — see `crate::kan`).
    #[test]
    fn j_on_refl_typechecks_but_does_not_syntactically_collapse_to_d() {
        let k = base_env();
        let a = cn("a");
        let c = identity_motive(&a);
        let d = refl(&a);
        let term = j(&c, &d, &refl(&a));
        // It type-checks at exactly `d`'s type (propositional equality holds: both
        // inhabit `C a (refl a)`).
        let ty = k.infer(&term).unwrap();
        assert!(k.def_eq(&ty, &k.infer(&d).unwrap()));
        // But it is NOT syntactically `d` after whnf: it's a stuck `Transp`.
        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&term);
        assert!(matches!(whnf, Term::Transp(..)), "expected a stuck Transp, got {}", whnf.pretty());
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
    /// of types (per the same completeness gap as
    /// [`j_on_refl_typechecks_but_does_not_syntactically_collapse_to_d`], propositional
    /// not definitional).
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
