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

use crate::term::Term;

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
