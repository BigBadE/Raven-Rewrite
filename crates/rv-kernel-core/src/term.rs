//! The core term language: a dependently-typed λ-calculus with universes.
//!
//! This is the *entire* expression language of the kernel — across all phases.
//! There are **no** special nodes for datatypes, constructors, recursors, or logic
//! connectives. Those all live in the [environment](crate::env) as declarations and
//! are referred to by [`Term::Const`]; their computational behaviour is supplied by
//! ι-reduction in the [reducer](crate::reduce). Keeping the term grammar this small
//! is what bounds the trust base.
//!
//! Bound variables use **de Bruijn indices** (`Var(0)` is the nearest enclosing
//! binder), so α-equivalence is syntactic identity and substitution needs no
//! freshening. The two primitive operations are [`Term::lift`] (re-index free
//! variables when moving a term under binders) and [`Term::instantiate`] (replace the
//! outermost bound variable — the engine of β/ζ/ι reduction).

use crate::face::Cof;
use crate::level::Level;
use std::rc::Rc;

/// A declaration name (type former, constructor, recursor, def, axiom). Interned as
/// a reference-counted string so the kernel stays dependency-free and names compare
/// by value.
pub type Name = Rc<str>;

/// Build a [`Name`] from a string slice.
pub fn name(s: &str) -> Name {
    Rc::from(s)
}

/// A **usage grade** (the `{0, 1, ω}` semiring of Quantitative Type Theory). It
/// annotates a `Π` binder with how much its argument is consumed *at runtime*:
///
/// * `Zero` — erased / ghost: free to use in types, specs, and proofs, but gone from
///   the compiled program (this is what makes spec/proof code vanish — no keyword);
/// * `One`  — linear: used exactly once;
/// * `Many` — unrestricted (the default; ordinary runtime values).
///
/// The trusted type-checker treats grades as *annotations* (ignoring them keeps it
/// identical to the ungraded system, hence sound); the separate `rv_kernel::erase`
/// analysis is what *uses* them, to erase ghosts and to check the grade discipline.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Grade {
    Zero,
    One,
    Many,
}

impl Grade {
    /// Semiring addition (combine two usages of the same variable).
    pub fn add(self, other: Grade) -> Grade {
        match (self, other) {
            (Grade::Zero, g) | (g, Grade::Zero) => g,
            _ => Grade::Many, // 1+1, 1+ω, ω+ω all saturate to ω
        }
    }
    /// Semiring multiplication (scale a usage by a binder's grade).
    pub fn mul(self, other: Grade) -> Grade {
        match (self, other) {
            (Grade::Zero, _) | (_, Grade::Zero) => Grade::Zero,
            (Grade::One, g) | (g, Grade::One) => g,
            (Grade::Many, Grade::Many) => Grade::Many,
        }
    }
    /// Is a usage of `self` permitted where the binder allows at most `bound`?
    /// (`0 ⊑ {0,1,ω}`, `1 ⊑ {1,ω}`, `ω ⊑ {ω}`.)
    pub fn fits(self, bound: Grade) -> bool {
        matches!(
            (self, bound),
            (Grade::Zero, _) | (Grade::One, Grade::One | Grade::Many) | (Grade::Many, Grade::Many)
        )
    }
}

/// A core term.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term {
    /// A universe: `Sort(0)` is `Type 0`, `Sort(1)` is `Type 1`, … (`Prop` enters
    /// with the Phase-2 sort decision).
    Sort(Level),
    /// A bound variable, by de Bruijn index.
    Var(usize),
    /// A reference to an environment declaration, with universe arguments
    /// instantiating that declaration's level parameters.
    Const(Name, Vec<Level>),
    /// Application `f a`.
    App(Rc<Term>, Rc<Term>),
    /// `λ (_ : domain). body` — `body` is in a context extended by one binder.
    Lam(Rc<Term>, Rc<Term>),
    /// `Π (_ :ᵍ domain). codomain` — the dependent function type, with a usage
    /// [`Grade`] on the binder; `codomain` is under one binder. A non-dependent arrow
    /// `A → B` is `Pi(Many, A, lift(B))`.
    Pi(Grade, Rc<Term>, Rc<Term>),
    /// `let (_ :ᵍ ty) := value in body` — `body` is under one binder, with a usage
    /// [`Grade`] on the let-bound variable (mirrors [`Term::Pi`]'s binder grade). The
    /// default constructor [`Term::let_`] grades it `Many` (unrestricted), so every
    /// pre-existing `let` — hand-built or elaborator-produced — is unaffected by the
    /// QTT usage pass in `rv_kernel::graded`.
    Let(Grade, Rc<Term>, Rc<Term>, Rc<Term>),
    /// An **elaboration-only** metavariable (a hole to be solved by unification). The
    /// trusted type-checker *rejects* any term still containing one; the elaborator
    /// solves and zonks all metas away before a term reaches the kernel. Atomic (its
    /// solution lives in the metacontext, not as subterms here).
    Meta(u32),

    // ---- Phase-1 cubical: the interval and Path types (see `crate::cubical`) ----
    /// The **interval sort**, `I` — a phantom classifier, never itself a `Sort n` and
    /// never a valid `Π`/`λ` domain. It only ever appears as the type [`LocalCtx`]
    /// (`crate::check`) hands back for a variable bound by [`Term::PLam`]; `infer`
    /// rejects `I` everywhere else, which is exactly what makes `I` "not fibrant" —
    /// nothing can quantify a real type over it (`Π (i : I). A` fails to type-check
    /// because `infer(I)` is an error, not a sort).
    I,
    /// The left interval endpoint, `i0 : I`.
    IZero,
    /// The right interval endpoint, `i1 : I`.
    IOne,
    /// **Phase 3.5** (De Morgan interval, see `crate::cubical`): reversal `~ r`.
    /// `r` must itself be interval-classified. Definitional laws (decided by
    /// [`crate::cubical::normalize_interval`], not by ad-hoc reduction rules):
    /// `~i0 = i1`, `~i1 = i0`, `~~r = r`, `~(r∧s) = ~r ∨ ~s`, `~(r∨s) = ~r ∧ ~s`.
    INeg(Rc<Term>),
    /// **Phase 3.5**: the interval meet (connection) `r ∧ s`. Idempotent, commutative,
    /// associative, absorbing (`r∧(r∨s)=r`), with `r∧i0=i0`, `r∧i1=r` — the meet of
    /// the (bounded, distributive, **De Morgan — not Boolean**) interval lattice. See
    /// `crate::cubical` for why `r∧~r=i0` is deliberately *not* a law here.
    IMeet(Rc<Term>, Rc<Term>),
    /// **Phase 3.5**: the interval join (connection) `r ∨ s`, dual to [`Term::IMeet`]:
    /// `r∨i1=i1`, `r∨i0=r`, plus idempotence/commutativity/associativity/absorption.
    IJoin(Rc<Term>, Rc<Term>),
    /// Path abstraction `⟨i⟩ t` (aka `λ i. t`, `i : I`). Deliberately reuses the
    /// *ordinary* de Bruijn `Var`/binder machinery — `body` is under one extra `Var`
    /// binder exactly like [`Term::Lam`], just with no domain subterm (the domain is
    /// always `I`, so there is nothing to store or re-check). This is what lets every
    /// existing `lift`/`subst`/NbE `Var` case keep working unmodified for interval
    /// binders; only [`crate::check`]'s context has to remember a binder is
    /// interval-typed (by recording [`Term::I`] as its type) rather than a real sort.
    PLam(Rc<Term>),
    /// Path application `p @ r` — eliminates a `Path`/`PathP`. `r` must check against
    /// `I` (so, in a well-typed term, only ever `IZero`, `IOne`, or a bound interval
    /// variable — Phase 1 is a **Cartesian** interval: no `∧`/`∨`/`~` connections, see
    /// `crate::cubical`). Definitional computation: `(PLam t) @ r ↦ t[i := r]`.
    PApp(Rc<Term>, Rc<Term>),
    /// `PathP (λ i. A) a0 a1` — the type of interval-abstractions whose family of
    /// types is `A` (a term under one interval binder, exactly like `PLam`'s body) and
    /// whose endpoints are (definitionally, not just propositionally) `a0` at `i0` and
    /// `a1` at `i1`. The non-dependent `Path A a b` is the special case where the
    /// family doesn't mention the bound interval variable: `PathP (A lifted) a b`.
    PathP(Rc<Term>, Rc<Term>, Rc<Term>),

    // ---- Phase-2 cubical: cofibrations and partial elements (see `crate::face`) ----
    /// A **system** `[φ_1 ↦ t_1, …, φ_n ↦ t_n]` — a partial element defined on
    /// `φ_1 ∨ … ∨ φ_n`. Check-only (see [`crate::check::Checker::infer`]'s
    /// `Term::Sys` arm): it has no inferred type on its own, only a type it can be
    /// *checked* against (`Partial ψ A`, with the compatibility condition enforced
    /// at that point — see `crate::face`). No binder: each `φ_i`/`t_i` lives in the
    /// very same context as the `Sys` node itself.
    Sys(Vec<(Rc<Cof>, Rc<Term>)>),
    /// `Partial φ A` — the type of partial elements of `A`, available only when `φ`
    /// holds. A genuine type (its `infer` result is `A`'s own sort), but never
    /// itself inhabited by anything except a compatibility-checked [`Term::Sys`].
    Partial(Rc<Cof>, Rc<Term>),

    // ---- Phase-3 cubical: the minimal SOUND Kan core (see `crate::kan`) ----
    /// `transp (λ i. family) φ a` — transport `a : family[i:=i0]` to `family[i:=i1]`
    /// along the line of types `family` (a term under one interval binder, exactly
    /// like [`Term::PLam`]'s body). `φ` is carried as well-formedness-checked
    /// metadata (the conventional cubical "extra face" argument) but is **never**
    /// consulted by the reduction rule — see `crate::kan`'s module doc for why a
    /// `φ`-driven shortcut would be unsound here (`φ` says nothing about whether
    /// `family` actually depends on the interval variable). The only reduction
    /// rule is the structurally-checked regularity rule
    /// (`!mentions_var(family, 0)`). This is the **minimal sound core**: no
    /// per-type-former Π/Σ/PathP filling — see `crate::kan` for why those are
    /// deferred rather than shipped half-sound.
    Transp(Rc<Term>, Rc<Cof>, Rc<Term>),
    /// `hcomp A φ u u0` — homogeneous composition: given a cap `u0 : A` and a system
    /// `u` (a term under one interval binder, of type `Partial φ A` at every point of
    /// the line), produces the composite at `i1`. The trivial (`φ = ⊤`) rule is
    /// always implemented; when `A` is syntactically a `Π` and `u` is syntactically a
    /// `Sys`, the `Π`-case filling rule additionally fires (pushing the composition
    /// pointwise into the codomain) — see `crate::kan`.
    HComp(Rc<Term>, Rc<Cof>, Rc<Term>, Rc<Term>),

    // ---- Step 1 of univalence: equivalences + the `Glue` former (see `crate::cubical`
    // module doc / `crate::equiv` / this file's `Glue` doc below) ----
    /// `Glue A [φ_1 ↦ (T_1,e_1), …, φ_n ↦ (T_n,e_n)]` (CCHM, *Cubical Type Theory*,
    /// §6): a type that is `T_k` wherever `φ_k` holds, and `A` off every face,
    /// glued together by the equivalences `e_k : Equiv T_k A`. Fields, in order:
    /// the base type `A` and the (non-empty) branch list, each branch a
    /// `(cofibration φ_k, outer partial type T_k, equivalence e_k : Equiv T_k A)`
    /// triple.
    ///
    /// **Multi-face generalization**: unlike an earlier single-face increment, this
    /// carries a genuine `n`-branch system — `n = 1` recovers exactly the old
    /// shape verbatim (so every previous single-face law is literally the `n=1`
    /// case of what follows). Branches must be **pairwise compatible on their
    /// overlap**: wherever `φ_i ∧ φ_j` is satisfiable, `T_i ≡ T_j` and `e_i ≡ e_j`
    /// after restricting to the overlap (reusing `crate::face`'s
    /// restriction-aware `overlap_clauses`/`restrict_clause_term`, exactly as
    /// `Term::Sys`'s `check_sys` already does for plain systems) — checked in
    /// `crate::check::Checker::infer`'s `Term::Glue` arm.
    ///
    /// `e_k` is still required to be a **total** (not merely `φ_k`-partial) proof
    /// of `Equiv T_k A` — strictly stronger than CCHM's most general formation
    /// rule, kept because it is sufficient for `ua` and keeps the checker/
    /// reducer/NbE trio tractable.
    ///
    /// **Strictness** (the defining CCHM property, generalized to `n` branches):
    ///   * `Glue A […, φ_k ↦ (T_k,e_k), …] ↦ T_k`  when `φ_k` is decided `⊤` (the
    ///     *first* such `k` in branch order — soundly arbitrary, since compatible
    ///     branches agree wherever more than one is simultaneously decided `⊤`)
    ///   * `Glue A [φ_1 ↦ …, …, φ_n ↦ …] ↦ A`  when *every* `φ_k` is decided `⊥`
    ///
    /// `glue`/`unglue` (the introduction/elimination forms): `unglue` is
    /// implemented (see `Term::Unglue`) with its β-rule and `⊤`-strictness;
    /// `glue` (the introduction form) and the Kan structure (`comp`/`hcomp` for
    /// `Glue`) remain deferred — see `crate::glue`'s module doc for the precise
    /// scope and the soundness argument for why deferring `glue` still leaves the
    /// type theory coherent (nothing can inhabit an *undecided* multi-face `Glue`
    /// either, for the same reason as the `n=1` case).
    Glue(Rc<Term>, Rc<Vec<(Rc<Cof>, Rc<Term>, Rc<Term>)>>),

    /// `unglue A [φ_1↦(T_1,e_1),…] u` — the elimination form for [`Term::Glue`]:
    /// given `u : Glue A […]`, produces a value of `A`. Fields, in order: the
    /// base type `A`, the same branch list as the `Glue` type this eliminates,
    /// and the scrutinee `u`.
    ///
    /// **Semantics** (CCHM §6.2): off every face (`u : A` already, since the type
    /// collapsed to `A`), `unglue` is the identity; on a decided face `φ_k`
    /// (where the type collapsed to `T_k`), `unglue` is `e_k.f` (the
    /// equivalence's forward map `T_k → A`). Concretely:
    ///   * `unglue A […] u ↦ u`               when every `φ_k` is decided `⊥`
    ///   * `unglue A […] u ↦ e_k.f u`          when `φ_k` is decided `⊤` (first
    ///     such `k`), i.e. `Equiv.f T_k A e_k u`
    ///   * otherwise stuck (a valid neutral, exactly like `PApp`/`HComp` when
    ///     their guard is undecided)
    ///
    /// No `Term::GlueIntro`/`glue` former is added this pass, so there is no
    /// `unglue (glue …) ↦ …` β-rule to state for a literal introduction — the
    /// `⊤`-strictness rule above already **is** the intended computational
    /// content on the one face where a `Glue`-typed term is forced to literally
    /// be a `T_k`-typed term running through `e_k.f` (see `crate::glue`'s module
    /// doc for the precise "what's deferred" scope).
    Unglue(Rc<Term>, Rc<Vec<(Rc<Cof>, Rc<Term>, Rc<Term>)>>, Rc<Term>),

    /// `glue [φ_1 ↦ t_1, …, φ_n ↦ t_n] a` — the **introduction** form for
    /// [`Term::Glue`] (CCHM, *Cubical Type Theory*, §6.2's `glue`), deferred by
    /// the earlier `Glue`/`unglue` pass (see `Term::Glue`'s doc) and added here.
    /// Fields: the branch list `[φ_k ↦ t_k]` (each `t_k` a partial element,
    /// defined — and required to type-check — on its own `φ_k`), and the base
    /// element `a : A`.
    ///
    /// **Typing** (checked, not inferred — see `crate::check::Checker::check`'s
    /// special case, mirroring [`Term::Sys`]'s check-only status): against an
    /// expected `Glue A [φ_1↦(T_1,e_1), …, φ_n↦(T_n,e_n)]`,
    ///   * the branch lists must line up index-for-index: `φ_k` here must be
    ///     semantically the *same* cofibration as the Glue type's own `φ_k`
    ///     (`crate::face::cof_equiv`), and `t_k : T_k`;
    ///   * the `t_k` must be mutually compatible on their overlaps (the same
    ///     restriction-aware condition [`crate::check::Checker::check_glue_branches_compatible`]
    ///     already imposes on `Glue`'s own `(T,e)` pairs, applied here to the
    ///     `t_k` payloads);
    ///   * `a : A`;
    ///   * and, the one genuinely new obligation, **agreement**: on each `φ_k`,
    ///     `Equiv.f T_k A e_k t_k ≡ a` (restriction-aware, exactly like the
    ///     compatibility check above) — the glued partial data must map to the
    ///     base under the equivalence, wherever it's defined.
    ///
    /// **Reduction** (`crate::reduce::Reducer::whnf`/`crate::nbe::Nbe`,
    /// differentially checked):
    ///   * `unglue A […] (glue […] a) ↦ a` — the defining β-rule connecting this
    ///     introduction form to [`Term::Unglue`]'s elimination.
    ///   * **Strictness**, mirroring `Glue`'s own two laws: `glue […, φ_k↦t_k, …]
    ///     a ↦ t_k` when `φ_k` is decided `⊤` (first such `k`); `glue […] a ↦ a`
    ///     when *every* `φ_k` is decided `⊥` (matching `Glue A […] ↦ A` at that
    ///     same face — a `Glue`-typed value there really is just an `A`-value).
    ///
    /// **Soundness**: `glue [φ↦t] a` type-checks only when the agreement
    /// condition genuinely holds (checked via `is_def_eq`, which can only
    /// *reject*, never fabricate an equation — see `crate::check`'s module doc),
    /// so this adds no way to inhabit an *undecided* `Glue` with data that
    /// disagrees with its own base under `unglue`; on a *decided* face the
    /// strictness law collapses `Glue` to plain `T_k`/`A` exactly as before, so
    /// `glue` there is just ordinary `T_k`/`A`-typed data the caller already had
    /// to produce (no new axiom). **Deferred**: `glue`-η (`glue [φ↦unglue g] (unglue
    /// g) ≡ g`) and the Kan structure (`hcomp`/`comp` for `Glue`, `transp^Glue`) —
    /// see `crate::kan`'s "Phase 3.12" doc for why the latter needed exactly this
    /// introduction form as a prerequisite, now unblocked for a future pass.
    GlueIntro(Rc<Vec<(Rc<Cof>, Rc<Term>)>>, Rc<Term>),
}

impl Term {
    pub fn sort(l: Level) -> Term {
        Term::Sort(l)
    }
    /// `Prop`, the impredicative sort of propositions: `Sort 0`.
    pub fn prop() -> Term {
        Term::Sort(Level::Zero)
    }
    /// `Type n`. We follow Lean's convention `Type n ≡ Sort (n+1)`, so `Type 0` is
    /// `Sort 1` (the first sort above `Prop`).
    pub fn typ(n: u32) -> Term {
        Term::Sort(Level::of_nat(n + 1))
    }
    pub fn var(i: usize) -> Term {
        Term::Var(i)
    }
    pub fn cnst(n: Name, ls: Vec<Level>) -> Term {
        Term::Const(n, ls)
    }
    pub fn app(f: Term, a: Term) -> Term {
        Term::App(Rc::new(f), Rc::new(a))
    }
    /// `f a0 a1 …` — left-associated application spine.
    pub fn apps(f: Term, args: impl IntoIterator<Item = Term>) -> Term {
        args.into_iter().fold(f, Term::app)
    }
    pub fn lam(domain: Term, body: Term) -> Term {
        Term::Lam(Rc::new(domain), Rc::new(body))
    }
    /// A `Π` binder at the default (unrestricted) grade.
    pub fn pi(domain: Term, codomain: Term) -> Term {
        Term::Pi(Grade::Many, Rc::new(domain), Rc::new(codomain))
    }
    /// A `Π` binder at an explicit usage grade.
    pub fn pi_graded(grade: Grade, domain: Term, codomain: Term) -> Term {
        Term::Pi(grade, Rc::new(domain), Rc::new(codomain))
    }
    /// A non-dependent arrow `A → B` (the codomain doesn't mention the argument, so
    /// `B` is lifted past the new binder).
    pub fn arrow(a: Term, b: Term) -> Term {
        Term::pi(a, b.lift(1, 0))
    }
    /// A `let` binder at the default (unrestricted) grade.
    pub fn let_(ty: Term, value: Term, body: Term) -> Term {
        Term::Let(Grade::Many, Rc::new(ty), Rc::new(value), Rc::new(body))
    }
    /// A `let` binder at an explicit usage grade.
    pub fn let_graded(grade: Grade, ty: Term, value: Term, body: Term) -> Term {
        Term::Let(grade, Rc::new(ty), Rc::new(value), Rc::new(body))
    }
    /// Interval reversal `~ r` (see [`Term::INeg`]).
    pub fn ineg(r: Term) -> Term {
        Term::INeg(Rc::new(r))
    }
    /// Interval meet `r ∧ s` (see [`Term::IMeet`]).
    pub fn imeet(r: Term, s: Term) -> Term {
        Term::IMeet(Rc::new(r), Rc::new(s))
    }
    /// Interval join `r ∨ s` (see [`Term::IJoin`]).
    pub fn ijoin(r: Term, s: Term) -> Term {
        Term::IJoin(Rc::new(r), Rc::new(s))
    }
    /// Path abstraction `⟨i⟩ body` (`body` under one interval binder).
    pub fn plam(body: Term) -> Term {
        Term::PLam(Rc::new(body))
    }
    /// Path application `p @ r`.
    pub fn papp(p: Term, r: Term) -> Term {
        Term::PApp(Rc::new(p), Rc::new(r))
    }
    /// The dependent path type `PathP (λ i. family) a0 a1`.
    pub fn pathp(family: Term, a0: Term, a1: Term) -> Term {
        Term::PathP(Rc::new(family), Rc::new(a0), Rc::new(a1))
    }
    /// The non-dependent path type `Path ty a b` — sugar for `PathP` with a constant
    /// family (`ty` lifted past the implicit interval binder, since it doesn't mention it).
    pub fn path(ty: Term, a: Term, b: Term) -> Term {
        Term::pathp(ty.lift(1, 0), a, b)
    }
    /// A system `[φ_1 ↦ t_1, …]` (see [`Term::Sys`]).
    pub fn sys(branches: Vec<(Cof, Term)>) -> Term {
        Term::Sys(branches.into_iter().map(|(p, t)| (Rc::new(p), Rc::new(t))).collect())
    }
    /// `Partial φ A` (see [`Term::Partial`]).
    pub fn partial(phi: Cof, ty: Term) -> Term {
        Term::Partial(Rc::new(phi), Rc::new(ty))
    }
    /// `transp (λ i. family) φ a` (see [`Term::Transp`]).
    pub fn transp(family: Term, phi: Cof, a: Term) -> Term {
        Term::Transp(Rc::new(family), Rc::new(phi), Rc::new(a))
    }
    /// Single-face `Glue A [φ ↦ (T,e)]` — the `n=1` case of [`Term::Glue`].
    pub fn glue_ty(a: Term, phi: Cof, t: Term, e: Term) -> Term {
        Term::glue_ty_multi(a, vec![(phi, t, e)])
    }
    /// General `n`-branch `Glue A [φ_1 ↦ (T_1,e_1), …]` (see [`Term::Glue`]). Does
    /// **not** itself check overlap-compatibility — that's
    /// `crate::check::Checker::infer`'s job (see `Term::Glue`'s doc); this is a
    /// bare term-former, just like `Term::sys` doesn't check `Sys` coverage.
    pub fn glue_ty_multi(a: Term, branches: Vec<(Cof, Term, Term)>) -> Term {
        Term::Glue(
            Rc::new(a),
            Rc::new(branches.into_iter().map(|(p, t, e)| (Rc::new(p), Rc::new(t), Rc::new(e))).collect()),
        )
    }
    /// `unglue A [φ_1 ↦ (T_1,e_1), …] u` (see [`Term::Unglue`]).
    pub fn unglue(a: Term, branches: Vec<(Cof, Term, Term)>, u: Term) -> Term {
        Term::Unglue(
            Rc::new(a),
            Rc::new(branches.into_iter().map(|(p, t, e)| (Rc::new(p), Rc::new(t), Rc::new(e))).collect()),
            Rc::new(u),
        )
    }
    /// `hcomp A φ u u0` (see [`Term::HComp`]).
    pub fn hcomp(ty: Term, phi: Cof, u: Term, u0: Term) -> Term {
        Term::HComp(Rc::new(ty), Rc::new(phi), Rc::new(u), Rc::new(u0))
    }
    /// `glue [φ_1 ↦ t_1, …] a` (see [`Term::GlueIntro`]). Does **not** itself check
    /// the agreement/compatibility obligations — that's `crate::check::Checker::check`'s
    /// job (a bare term-former, just like `Term::sys`/`Term::glue_ty_multi`).
    pub fn glue_intro(branches: Vec<(Cof, Term)>, a: Term) -> Term {
        Term::GlueIntro(
            Rc::new(branches.into_iter().map(|(p, t)| (Rc::new(p), Rc::new(t))).collect()),
            Rc::new(a),
        )
    }

    /// Re-index free variables: add `amount` to every `Var(i)` with `i >= cutoff`.
    /// Used to move a term under `amount` new binders (`cutoff` counts the binders
    /// already crossed). `amount` may be negative to *remove* binders, valid only
    /// when no free variable in range `[cutoff, cutoff)` would underflow.
    pub fn lift(&self, amount: isize, cutoff: usize) -> Term {
        match self {
            Term::Sort(_) | Term::Const(..) | Term::Meta(_) | Term::I | Term::IZero | Term::IOne => {
                self.clone()
            }
            Term::Var(i) => {
                if *i >= cutoff {
                    Term::Var((*i as isize + amount) as usize)
                } else {
                    Term::Var(*i)
                }
            }
            Term::App(f, a) => Term::app(f.lift(amount, cutoff), a.lift(amount, cutoff)),
            Term::Lam(d, b) => Term::lam(d.lift(amount, cutoff), b.lift(amount, cutoff + 1)),
            Term::Pi(g, d, b) => {
                Term::pi_graded(*g, d.lift(amount, cutoff), b.lift(amount, cutoff + 1))
            }
            Term::Let(g, t, v, b) => {
                Term::let_graded(*g, t.lift(amount, cutoff), v.lift(amount, cutoff), b.lift(amount, cutoff + 1))
            }
            Term::INeg(r) => Term::ineg(r.lift(amount, cutoff)),
            Term::IMeet(r, s) => Term::imeet(r.lift(amount, cutoff), s.lift(amount, cutoff)),
            Term::IJoin(r, s) => Term::ijoin(r.lift(amount, cutoff), s.lift(amount, cutoff)),
            // `PLam`/`PathP`'s family live under one extra (interval) `Var` binder,
            // exactly like `Lam`'s body — same cutoff bump.
            Term::PLam(b) => Term::plam(b.lift(amount, cutoff + 1)),
            Term::PApp(p, r) => Term::papp(p.lift(amount, cutoff), r.lift(amount, cutoff)),
            Term::PathP(fam, a0, a1) => Term::pathp(
                fam.lift(amount, cutoff + 1),
                a0.lift(amount, cutoff),
                a1.lift(amount, cutoff),
            ),
            Term::Sys(branches) => Term::Sys(
                branches
                    .iter()
                    .map(|(p, t)| (Rc::new(p.lift(amount, cutoff)), Rc::new(t.lift(amount, cutoff))))
                    .collect(),
            ),
            Term::Partial(p, a) => {
                Term::Partial(Rc::new(p.lift(amount, cutoff)), Rc::new(a.lift(amount, cutoff)))
            }
            Term::Transp(fam, phi, a) => Term::transp(
                fam.lift(amount, cutoff + 1),
                phi.lift(amount, cutoff),
                a.lift(amount, cutoff),
            ),
            Term::HComp(ty, phi, u, u0) => Term::hcomp(
                ty.lift(amount, cutoff),
                phi.lift(amount, cutoff),
                u.lift(amount, cutoff + 1),
                u0.lift(amount, cutoff),
            ),
            Term::Glue(a, branches) => Term::Glue(
                Rc::new(a.lift(amount, cutoff)),
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t, e)| {
                            (Rc::new(p.lift(amount, cutoff)), Rc::new(t.lift(amount, cutoff)), Rc::new(e.lift(amount, cutoff)))
                        })
                        .collect(),
                ),
            ),
            Term::Unglue(a, branches, u) => Term::Unglue(
                Rc::new(a.lift(amount, cutoff)),
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t, e)| {
                            (Rc::new(p.lift(amount, cutoff)), Rc::new(t.lift(amount, cutoff)), Rc::new(e.lift(amount, cutoff)))
                        })
                        .collect(),
                ),
                Rc::new(u.lift(amount, cutoff)),
            ),
            Term::GlueIntro(branches, a) => Term::GlueIntro(
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t)| (Rc::new(p.lift(amount, cutoff)), Rc::new(t.lift(amount, cutoff))))
                        .collect(),
                ),
                Rc::new(a.lift(amount, cutoff)),
            ),
        }
    }

    /// Substitute `replacement` for the variable at de Bruijn `depth`, decrementing
    /// the free variables above it (they lose the binder being eliminated). The
    /// replacement is lifted by `depth` so its own free variables stay correct under
    /// the binders it now sits beneath.
    fn subst(&self, depth: usize, replacement: &Term) -> Term {
        match self {
            Term::Sort(_) | Term::Const(..) | Term::Meta(_) | Term::I | Term::IZero | Term::IOne => {
                self.clone()
            }
            Term::Var(i) => match (*i).cmp(&depth) {
                std::cmp::Ordering::Equal => replacement.lift(depth as isize, 0),
                std::cmp::Ordering::Greater => Term::Var(i - 1),
                std::cmp::Ordering::Less => Term::Var(*i),
            },
            Term::App(f, a) => Term::app(f.subst(depth, replacement), a.subst(depth, replacement)),
            Term::Lam(d, b) => {
                Term::lam(d.subst(depth, replacement), b.subst(depth + 1, replacement))
            }
            Term::Pi(g, d, b) => {
                Term::pi_graded(*g, d.subst(depth, replacement), b.subst(depth + 1, replacement))
            }
            Term::Let(g, t, v, b) => Term::let_graded(
                *g,
                t.subst(depth, replacement),
                v.subst(depth, replacement),
                b.subst(depth + 1, replacement),
            ),
            Term::INeg(r) => Term::ineg(r.subst(depth, replacement)),
            Term::IMeet(r, s) => {
                Term::imeet(r.subst(depth, replacement), s.subst(depth, replacement))
            }
            Term::IJoin(r, s) => {
                Term::ijoin(r.subst(depth, replacement), s.subst(depth, replacement))
            }
            Term::PLam(b) => Term::plam(b.subst(depth + 1, replacement)),
            Term::PApp(p, r) => Term::papp(p.subst(depth, replacement), r.subst(depth, replacement)),
            Term::PathP(fam, a0, a1) => Term::pathp(
                fam.subst(depth + 1, replacement),
                a0.subst(depth, replacement),
                a1.subst(depth, replacement),
            ),
            Term::Sys(branches) => Term::Sys(
                branches
                    .iter()
                    .map(|(p, t)| (Rc::new(p.subst(depth, replacement)), Rc::new(t.subst(depth, replacement))))
                    .collect(),
            ),
            Term::Partial(p, a) => Term::Partial(
                Rc::new(p.subst(depth, replacement)),
                Rc::new(a.subst(depth, replacement)),
            ),
            Term::Transp(fam, phi, a) => Term::transp(
                fam.subst(depth + 1, replacement),
                phi.subst(depth, replacement),
                a.subst(depth, replacement),
            ),
            Term::HComp(ty, phi, u, u0) => Term::hcomp(
                ty.subst(depth, replacement),
                phi.subst(depth, replacement),
                u.subst(depth + 1, replacement),
                u0.subst(depth, replacement),
            ),
            Term::Glue(a, branches) => Term::Glue(
                Rc::new(a.subst(depth, replacement)),
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t, e)| {
                            (Rc::new(p.subst(depth, replacement)), Rc::new(t.subst(depth, replacement)), Rc::new(e.subst(depth, replacement)))
                        })
                        .collect(),
                ),
            ),
            Term::Unglue(a, branches, u) => Term::Unglue(
                Rc::new(a.subst(depth, replacement)),
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t, e)| {
                            (Rc::new(p.subst(depth, replacement)), Rc::new(t.subst(depth, replacement)), Rc::new(e.subst(depth, replacement)))
                        })
                        .collect(),
                ),
                Rc::new(u.subst(depth, replacement)),
            ),
            Term::GlueIntro(branches, a) => Term::GlueIntro(
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t)| (Rc::new(p.subst(depth, replacement)), Rc::new(t.subst(depth, replacement))))
                        .collect(),
                ),
                Rc::new(a.subst(depth, replacement)),
            ),
        }
    }

    /// β/ζ/ι workhorse: replace the outermost bound variable (`Var(0)`) of a body
    /// with `arg`. `self` is the body living under exactly one binder.
    pub fn instantiate(&self, arg: &Term) -> Term {
        self.subst(0, arg)
    }

    /// **Restriction**, not elimination: replace free occurrences of `Var(depth)`
    /// with `replacement`, but — unlike [`Term::subst`]/[`Term::subst_at`] — leave
    /// every *other* free variable's index exactly as it is (no decrementing the
    /// indices above `depth`). The binder at `depth` is *not* removed from the
    /// ambient context; this just pins one already-bound interval variable to a
    /// literal endpoint for the purposes of a definitional-equality comparison run
    /// in the same context (see `crate::face`'s restriction-aware `check_sys`,
    /// which uses this to compare two system branches "under" a cofibration clause
    /// without disturbing the de Bruijn depth the caller's `LocalCtx` is tracking).
    /// Mirrors `subst`'s structural recursion (each binder still bumps `depth` by
    /// one as it's crossed) but drops the "decrement above `depth`" arm.
    pub(crate) fn replace_free_var(&self, depth: usize, replacement: &Term) -> Term {
        match self {
            Term::Sort(_) | Term::Const(..) | Term::Meta(_) | Term::I | Term::IZero | Term::IOne => {
                self.clone()
            }
            Term::Var(i) => {
                if *i == depth {
                    replacement.lift(depth as isize, 0)
                } else {
                    Term::Var(*i)
                }
            }
            Term::App(f, a) => Term::app(
                f.replace_free_var(depth, replacement),
                a.replace_free_var(depth, replacement),
            ),
            Term::Lam(d, b) => Term::lam(
                d.replace_free_var(depth, replacement),
                b.replace_free_var(depth + 1, replacement),
            ),
            Term::Pi(g, d, b) => Term::pi_graded(
                *g,
                d.replace_free_var(depth, replacement),
                b.replace_free_var(depth + 1, replacement),
            ),
            Term::Let(g, t, v, b) => Term::let_graded(
                *g,
                t.replace_free_var(depth, replacement),
                v.replace_free_var(depth, replacement),
                b.replace_free_var(depth + 1, replacement),
            ),
            Term::INeg(r) => Term::ineg(r.replace_free_var(depth, replacement)),
            Term::IMeet(r, s) => Term::imeet(
                r.replace_free_var(depth, replacement),
                s.replace_free_var(depth, replacement),
            ),
            Term::IJoin(r, s) => Term::ijoin(
                r.replace_free_var(depth, replacement),
                s.replace_free_var(depth, replacement),
            ),
            Term::PLam(b) => Term::plam(b.replace_free_var(depth + 1, replacement)),
            Term::PApp(p, r) => Term::papp(
                p.replace_free_var(depth, replacement),
                r.replace_free_var(depth, replacement),
            ),
            Term::PathP(fam, a0, a1) => Term::pathp(
                fam.replace_free_var(depth + 1, replacement),
                a0.replace_free_var(depth, replacement),
                a1.replace_free_var(depth, replacement),
            ),
            Term::Sys(branches) => Term::Sys(
                branches
                    .iter()
                    .map(|(p, t)| {
                        (
                            Rc::new(p.replace_free_var(depth, replacement)),
                            Rc::new(t.replace_free_var(depth, replacement)),
                        )
                    })
                    .collect(),
            ),
            Term::Partial(p, a) => Term::Partial(
                Rc::new(p.replace_free_var(depth, replacement)),
                Rc::new(a.replace_free_var(depth, replacement)),
            ),
            Term::Transp(fam, phi, a) => Term::transp(
                fam.replace_free_var(depth + 1, replacement),
                phi.replace_free_var(depth, replacement),
                a.replace_free_var(depth, replacement),
            ),
            Term::HComp(ty, phi, u, u0) => Term::hcomp(
                ty.replace_free_var(depth, replacement),
                phi.replace_free_var(depth, replacement),
                u.replace_free_var(depth + 1, replacement),
                u0.replace_free_var(depth, replacement),
            ),
            Term::Glue(a, branches) => Term::Glue(
                Rc::new(a.replace_free_var(depth, replacement)),
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t, e)| {
                            (
                                Rc::new(p.replace_free_var(depth, replacement)),
                                Rc::new(t.replace_free_var(depth, replacement)),
                                Rc::new(e.replace_free_var(depth, replacement)),
                            )
                        })
                        .collect(),
                ),
            ),
            Term::Unglue(a, branches, u) => Term::Unglue(
                Rc::new(a.replace_free_var(depth, replacement)),
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t, e)| {
                            (
                                Rc::new(p.replace_free_var(depth, replacement)),
                                Rc::new(t.replace_free_var(depth, replacement)),
                                Rc::new(e.replace_free_var(depth, replacement)),
                            )
                        })
                        .collect(),
                ),
                Rc::new(u.replace_free_var(depth, replacement)),
            ),
            Term::GlueIntro(branches, a) => Term::GlueIntro(
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t)| {
                            (
                                Rc::new(p.replace_free_var(depth, replacement)),
                                Rc::new(t.replace_free_var(depth, replacement)),
                            )
                        })
                        .collect(),
                ),
                Rc::new(a.replace_free_var(depth, replacement)),
            ),
        }
    }

    /// Substitute `replacement` for the variable at de Bruijn `depth` (general form of
    /// [`Term::instantiate`]). Used by the effect-handler interpreter to plug an
    /// operation's result into a continuation nested under several binders.
    pub fn subst_at(&self, depth: usize, replacement: &Term) -> Term {
        self.subst(depth, replacement)
    }

    /// Parallel substitution of the innermost `images.len()` binders: `Var(i)` for
    /// `i < images.len()` becomes `images[i]`, and free variables above the block
    /// shift down by `images.len()`. Each image is lifted past any of `self`'s own
    /// internal binders it ends up beneath. Used by the inductive elaborator to
    /// re-express an imported telescope (a constructor field type, an index domain)
    /// in the recursor's variable context.
    pub fn subst_ctx(&self, images: &[Term]) -> Term {
        self.subst_ctx_go(images, 0)
    }
    pub(crate) fn subst_ctx_go(&self, images: &[Term], depth: usize) -> Term {
        match self {
            Term::Sort(_) | Term::Const(..) | Term::Meta(_) | Term::I | Term::IZero | Term::IOne => {
                self.clone()
            }
            Term::Var(i) => {
                if *i < depth {
                    Term::Var(*i) // bound by one of self's own binders
                } else if *i - depth < images.len() {
                    images[*i - depth].lift(depth as isize, 0)
                } else {
                    Term::Var(*i - images.len())
                }
            }
            Term::App(f, a) => {
                Term::app(f.subst_ctx_go(images, depth), a.subst_ctx_go(images, depth))
            }
            Term::Lam(d, b) => {
                Term::lam(d.subst_ctx_go(images, depth), b.subst_ctx_go(images, depth + 1))
            }
            Term::Pi(g, d, b) => {
                Term::pi_graded(*g, d.subst_ctx_go(images, depth), b.subst_ctx_go(images, depth + 1))
            }
            Term::Let(g, t, v, b) => Term::let_graded(
                *g,
                t.subst_ctx_go(images, depth),
                v.subst_ctx_go(images, depth),
                b.subst_ctx_go(images, depth + 1),
            ),
            Term::INeg(r) => Term::ineg(r.subst_ctx_go(images, depth)),
            Term::IMeet(r, s) => {
                Term::imeet(r.subst_ctx_go(images, depth), s.subst_ctx_go(images, depth))
            }
            Term::IJoin(r, s) => {
                Term::ijoin(r.subst_ctx_go(images, depth), s.subst_ctx_go(images, depth))
            }
            Term::PLam(b) => Term::plam(b.subst_ctx_go(images, depth + 1)),
            Term::PApp(p, r) => {
                Term::papp(p.subst_ctx_go(images, depth), r.subst_ctx_go(images, depth))
            }
            Term::PathP(fam, a0, a1) => Term::pathp(
                fam.subst_ctx_go(images, depth + 1),
                a0.subst_ctx_go(images, depth),
                a1.subst_ctx_go(images, depth),
            ),
            Term::Sys(branches) => Term::Sys(
                branches
                    .iter()
                    .map(|(p, t)| {
                        (Rc::new(p.subst_ctx_go(images, depth)), Rc::new(t.subst_ctx_go(images, depth)))
                    })
                    .collect(),
            ),
            Term::Partial(p, a) => Term::Partial(
                Rc::new(p.subst_ctx_go(images, depth)),
                Rc::new(a.subst_ctx_go(images, depth)),
            ),
            Term::Transp(fam, phi, a) => Term::transp(
                fam.subst_ctx_go(images, depth + 1),
                phi.subst_ctx_go(images, depth),
                a.subst_ctx_go(images, depth),
            ),
            Term::HComp(ty, phi, u, u0) => Term::hcomp(
                ty.subst_ctx_go(images, depth),
                phi.subst_ctx_go(images, depth),
                u.subst_ctx_go(images, depth + 1),
                u0.subst_ctx_go(images, depth),
            ),
            Term::Glue(a, branches) => Term::Glue(
                Rc::new(a.subst_ctx_go(images, depth)),
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t, e)| {
                            (
                                Rc::new(p.subst_ctx_go(images, depth)),
                                Rc::new(t.subst_ctx_go(images, depth)),
                                Rc::new(e.subst_ctx_go(images, depth)),
                            )
                        })
                        .collect(),
                ),
            ),
            Term::Unglue(a, branches, u) => Term::Unglue(
                Rc::new(a.subst_ctx_go(images, depth)),
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t, e)| {
                            (
                                Rc::new(p.subst_ctx_go(images, depth)),
                                Rc::new(t.subst_ctx_go(images, depth)),
                                Rc::new(e.subst_ctx_go(images, depth)),
                            )
                        })
                        .collect(),
                ),
                Rc::new(u.subst_ctx_go(images, depth)),
            ),
            Term::GlueIntro(branches, a) => Term::GlueIntro(
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t)| {
                            (
                                Rc::new(p.subst_ctx_go(images, depth)),
                                Rc::new(t.subst_ctx_go(images, depth)),
                            )
                        })
                        .collect(),
                ),
                Rc::new(a.subst_ctx_go(images, depth)),
            ),
        }
    }

    /// Parallel substitution of the innermost `images.len()` binders, **without**
    /// shrinking the surrounding frame — a variant of [`Term::subst_ctx`] for
    /// **reparametrization** rather than *elimination* of binders. `subst_ctx`
    /// removes the substituted slots (so any *un*-replaced free variable above the
    /// block shifts *down* by `images.len()`, because that many binders have gone
    /// away). This function instead **replaces the meaning of exactly those slots**
    /// (e.g. swapping an interval binder `i` for a differently-named/derived one
    /// `k`, or swapping a `Π`'s bound `x`/its own interval binder `i` for two fresh
    /// ones in a reparametrized family) while leaving every other free variable's
    /// de Bruijn index **untouched** — the frame stays exactly as large as it was,
    /// with the same variables sitting at the same indices above the substituted
    /// block; only `images.len()` slots' *content* changes.
    ///
    /// Used exclusively by the `Π`-case `transp` Kan rule (see `crate::kan`'s module
    /// doc and [`reduce::Reducer::whnf`]/[`nbe::Nbe::eval`]'s `Term::Transp` arms) to
    /// build the CCHM generalized-`coe` reparametrized family
    /// `dom[i := (r∧~k)∨(r'∧k)]` (one slot swapped for a fresh De Morgan connection
    /// over a new interval binder `k`) and the `B i (x̄ i)` family (two slots — the
    /// `Π`'s bound `x` and its own interval binder `i` — swapped for the outer
    /// `transp`'s fresh binder and the backward-transported argument line). See the
    /// call sites for the exact index bookkeeping; this is deliberately the same
    /// recursive shape as `subst_ctx_go`; it differs in exactly one line (the `Var`,
    /// "above the block" arm).
    pub(crate) fn subst_ctx_keep_frame(&self, images: &[Term]) -> Term {
        self.subst_ctx_keep_frame_go(images, 0)
    }
    pub(crate) fn subst_ctx_keep_frame_go(&self, images: &[Term], depth: usize) -> Term {
        match self {
            Term::Sort(_) | Term::Const(..) | Term::Meta(_) | Term::I | Term::IZero | Term::IOne => {
                self.clone()
            }
            Term::Var(i) => {
                if *i < depth {
                    Term::Var(*i) // bound by one of self's own binders
                } else if *i - depth < images.len() {
                    images[*i - depth].lift(depth as isize, 0)
                } else {
                    // The one difference from `subst_ctx_go`: no shrink — this free
                    // variable refers to the *same* outer slot it always did, since
                    // the surrounding frame's size is unchanged by this operation.
                    Term::Var(*i)
                }
            }
            Term::App(f, a) => Term::app(
                f.subst_ctx_keep_frame_go(images, depth),
                a.subst_ctx_keep_frame_go(images, depth),
            ),
            Term::Lam(d, b) => Term::lam(
                d.subst_ctx_keep_frame_go(images, depth),
                b.subst_ctx_keep_frame_go(images, depth + 1),
            ),
            Term::Pi(g, d, b) => Term::pi_graded(
                *g,
                d.subst_ctx_keep_frame_go(images, depth),
                b.subst_ctx_keep_frame_go(images, depth + 1),
            ),
            Term::Let(g, t, v, b) => Term::let_graded(
                *g,
                t.subst_ctx_keep_frame_go(images, depth),
                v.subst_ctx_keep_frame_go(images, depth),
                b.subst_ctx_keep_frame_go(images, depth + 1),
            ),
            Term::INeg(r) => Term::ineg(r.subst_ctx_keep_frame_go(images, depth)),
            Term::IMeet(r, s) => Term::imeet(
                r.subst_ctx_keep_frame_go(images, depth),
                s.subst_ctx_keep_frame_go(images, depth),
            ),
            Term::IJoin(r, s) => Term::ijoin(
                r.subst_ctx_keep_frame_go(images, depth),
                s.subst_ctx_keep_frame_go(images, depth),
            ),
            Term::PLam(b) => Term::plam(b.subst_ctx_keep_frame_go(images, depth + 1)),
            Term::PApp(p, r) => Term::papp(
                p.subst_ctx_keep_frame_go(images, depth),
                r.subst_ctx_keep_frame_go(images, depth),
            ),
            Term::PathP(fam, a0, a1) => Term::pathp(
                fam.subst_ctx_keep_frame_go(images, depth + 1),
                a0.subst_ctx_keep_frame_go(images, depth),
                a1.subst_ctx_keep_frame_go(images, depth),
            ),
            Term::Sys(branches) => Term::Sys(
                branches
                    .iter()
                    .map(|(p, t)| {
                        (
                            Rc::new(p.subst_ctx_keep_frame_go(images, depth)),
                            Rc::new(t.subst_ctx_keep_frame_go(images, depth)),
                        )
                    })
                    .collect(),
            ),
            Term::Partial(p, a) => Term::Partial(
                Rc::new(p.subst_ctx_keep_frame_go(images, depth)),
                Rc::new(a.subst_ctx_keep_frame_go(images, depth)),
            ),
            Term::Transp(fam, phi, a) => Term::transp(
                fam.subst_ctx_keep_frame_go(images, depth + 1),
                phi.subst_ctx_keep_frame_go(images, depth),
                a.subst_ctx_keep_frame_go(images, depth),
            ),
            Term::HComp(ty, phi, u, u0) => Term::hcomp(
                ty.subst_ctx_keep_frame_go(images, depth),
                phi.subst_ctx_keep_frame_go(images, depth),
                u.subst_ctx_keep_frame_go(images, depth + 1),
                u0.subst_ctx_keep_frame_go(images, depth),
            ),
            Term::Glue(a, branches) => Term::Glue(
                Rc::new(a.subst_ctx_keep_frame_go(images, depth)),
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t, e)| {
                            (
                                Rc::new(p.subst_ctx_keep_frame_go(images, depth)),
                                Rc::new(t.subst_ctx_keep_frame_go(images, depth)),
                                Rc::new(e.subst_ctx_keep_frame_go(images, depth)),
                            )
                        })
                        .collect(),
                ),
            ),
            Term::Unglue(a, branches, u) => Term::Unglue(
                Rc::new(a.subst_ctx_keep_frame_go(images, depth)),
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t, e)| {
                            (
                                Rc::new(p.subst_ctx_keep_frame_go(images, depth)),
                                Rc::new(t.subst_ctx_keep_frame_go(images, depth)),
                                Rc::new(e.subst_ctx_keep_frame_go(images, depth)),
                            )
                        })
                        .collect(),
                ),
                Rc::new(u.subst_ctx_keep_frame_go(images, depth)),
            ),
            Term::GlueIntro(branches, a) => Term::GlueIntro(
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t)| {
                            (
                                Rc::new(p.subst_ctx_keep_frame_go(images, depth)),
                                Rc::new(t.subst_ctx_keep_frame_go(images, depth)),
                            )
                        })
                        .collect(),
                ),
                Rc::new(a.subst_ctx_keep_frame_go(images, depth)),
            ),
        }
    }

    /// Substitute the declaration's universe parameters with `args` everywhere a
    /// `Sort`/`Const` mentions them. Used when a polymorphic `Const` is unfolded or
    /// type-checked at specific levels.
    pub fn instantiate_levels(&self, args: &[Level]) -> Term {
        // No universe arguments ⇒ every `Level::instantiate` is the identity, so the
        // whole rebuild would just deep-copy `self`. Callers that need an owned copy get
        // one via `clone`, but the common hot paths (NbE unfolding) avoid even that.
        if args.is_empty() {
            return self.clone();
        }
        match self {
            Term::Sort(l) => Term::Sort(l.instantiate(args)),
            Term::Var(_) | Term::Meta(_) | Term::I | Term::IZero | Term::IOne => self.clone(),
            Term::Const(n, ls) => {
                Term::Const(n.clone(), ls.iter().map(|l| l.instantiate(args)).collect())
            }
            Term::App(f, a) => Term::app(f.instantiate_levels(args), a.instantiate_levels(args)),
            Term::Lam(d, b) => Term::lam(d.instantiate_levels(args), b.instantiate_levels(args)),
            Term::Pi(g, d, b) => {
                Term::pi_graded(*g, d.instantiate_levels(args), b.instantiate_levels(args))
            }
            Term::Let(g, t, v, b) => Term::let_graded(
                *g,
                t.instantiate_levels(args),
                v.instantiate_levels(args),
                b.instantiate_levels(args),
            ),
            Term::INeg(r) => Term::ineg(r.instantiate_levels(args)),
            Term::IMeet(r, s) => {
                Term::imeet(r.instantiate_levels(args), s.instantiate_levels(args))
            }
            Term::IJoin(r, s) => {
                Term::ijoin(r.instantiate_levels(args), s.instantiate_levels(args))
            }
            Term::PLam(b) => Term::plam(b.instantiate_levels(args)),
            Term::PApp(p, r) => Term::papp(p.instantiate_levels(args), r.instantiate_levels(args)),
            Term::PathP(fam, a0, a1) => Term::pathp(
                fam.instantiate_levels(args),
                a0.instantiate_levels(args),
                a1.instantiate_levels(args),
            ),
            Term::Sys(branches) => Term::Sys(
                branches
                    .iter()
                    .map(|(p, t)| {
                        (Rc::new(p.instantiate_levels(args)), Rc::new(t.instantiate_levels(args)))
                    })
                    .collect(),
            ),
            Term::Partial(p, a) => Term::Partial(
                Rc::new(p.instantiate_levels(args)),
                Rc::new(a.instantiate_levels(args)),
            ),
            Term::Transp(fam, phi, a) => Term::transp(
                fam.instantiate_levels(args),
                phi.instantiate_levels(args),
                a.instantiate_levels(args),
            ),
            Term::HComp(ty, phi, u, u0) => Term::hcomp(
                ty.instantiate_levels(args),
                phi.instantiate_levels(args),
                u.instantiate_levels(args),
                u0.instantiate_levels(args),
            ),
            Term::Glue(a, branches) => Term::Glue(
                Rc::new(a.instantiate_levels(args)),
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t, e)| {
                            (
                                Rc::new(p.instantiate_levels(args)),
                                Rc::new(t.instantiate_levels(args)),
                                Rc::new(e.instantiate_levels(args)),
                            )
                        })
                        .collect(),
                ),
            ),
            Term::Unglue(a, branches, u) => Term::Unglue(
                Rc::new(a.instantiate_levels(args)),
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t, e)| {
                            (
                                Rc::new(p.instantiate_levels(args)),
                                Rc::new(t.instantiate_levels(args)),
                                Rc::new(e.instantiate_levels(args)),
                            )
                        })
                        .collect(),
                ),
                Rc::new(u.instantiate_levels(args)),
            ),
            Term::GlueIntro(branches, a) => Term::GlueIntro(
                Rc::new(
                    branches
                        .iter()
                        .map(|(p, t)| {
                            (Rc::new(p.instantiate_levels(args)), Rc::new(t.instantiate_levels(args)))
                        })
                        .collect(),
                ),
                Rc::new(a.instantiate_levels(args)),
            ),
        }
    }

    /// Does this term contain an (unsolved) metavariable — a [`Term::Meta`], or a
    /// [`Level::Meta`] inside a `Sort`/`Const`? The kernel uses this to reject any term
    /// that still carries elaboration holes, so nothing un-zonked is ever trusted.
    pub fn has_meta(&self) -> bool {
        match self {
            Term::Meta(_) => true,
            Term::Var(_) | Term::I | Term::IZero | Term::IOne => false,
            Term::Sort(l) => l.has_meta(),
            Term::Const(_, ls) => ls.iter().any(|l| l.has_meta()),
            Term::App(f, a) => f.has_meta() || a.has_meta(),
            Term::Lam(d, b) => d.has_meta() || b.has_meta(),
            Term::Pi(_, d, b) => d.has_meta() || b.has_meta(),
            Term::Let(_, t, v, b) => t.has_meta() || v.has_meta() || b.has_meta(),
            Term::INeg(r) => r.has_meta(),
            Term::IMeet(r, s) | Term::IJoin(r, s) => r.has_meta() || s.has_meta(),
            Term::PLam(b) => b.has_meta(),
            Term::PApp(p, r) => p.has_meta() || r.has_meta(),
            Term::PathP(fam, a0, a1) => fam.has_meta() || a0.has_meta() || a1.has_meta(),
            Term::Sys(branches) => branches.iter().any(|(p, t)| p.has_meta() || t.has_meta()),
            Term::Partial(p, a) => p.has_meta() || a.has_meta(),
            Term::Transp(fam, phi, a) => fam.has_meta() || phi.has_meta() || a.has_meta(),
            Term::HComp(ty, phi, u, u0) => {
                ty.has_meta() || phi.has_meta() || u.has_meta() || u0.has_meta()
            }
            Term::Glue(a, branches) => {
                a.has_meta() || branches.iter().any(|(p, t, e)| p.has_meta() || t.has_meta() || e.has_meta())
            }
            Term::Unglue(a, branches, u) => {
                a.has_meta()
                    || branches.iter().any(|(p, t, e)| p.has_meta() || t.has_meta() || e.has_meta())
                    || u.has_meta()
            }
            Term::GlueIntro(branches, a) => {
                a.has_meta() || branches.iter().any(|(p, t)| p.has_meta() || t.has_meta())
            }
        }
    }

    /// Collect an application spine `f a0 a1 … aN` into `(f, [a0,…,aN])`.
    pub fn unfold_apps(&self) -> (Term, Vec<Term>) {
        let mut args = Vec::new();
        let mut head = self.clone();
        while let Term::App(f, a) = head {
            args.push((*a).clone());
            head = (*f).clone();
        }
        args.reverse();
        (head, args)
    }

    /// A readable, surface-like pretty-print for **diagnostics** (type-mismatch and
    /// unification errors). Unlike `rv_kernel::verify::render` — which is for *runtime
    /// values* and collapses functions to `<function>` — this shows the full term:
    /// de Bruijn variables get generated binder names (`a`, `b`, …), declaration and
    /// constructor names print directly, arrows collapse to `A -> B` when non-dependent,
    /// and unsolved metavariables show as `?n`.
    pub fn pretty(&self) -> String {
        self.pp(&mut Vec::new(), 0)
    }

    pub(crate) fn pp(&self, names: &mut Vec<String>, prec: u8) -> String {
        // prec: 0 = top-level, 2 = needs parens if a binder/arrow, 3 = atom (app argument).
        match self {
            Term::Sort(l) => format!("Sort {l:?}"),
            Term::Meta(m) => format!("?{m}"),
            Term::I => "I".to_string(),
            Term::IZero => "i0".to_string(),
            Term::IOne => "i1".to_string(),
            Term::INeg(r) => paren_if(prec >= 3, format!("~{}", r.pp(names, 3))),
            Term::IMeet(r, s) => {
                paren_if(prec >= 3, format!("{} ∧ {}", r.pp(names, 3), s.pp(names, 3)))
            }
            Term::IJoin(r, s) => {
                paren_if(prec >= 3, format!("{} ∨ {}", r.pp(names, 3), s.pp(names, 3)))
            }
            Term::PLam(b) => {
                let nm = fresh_binder_name(names.len());
                names.push(nm.clone());
                let bs = b.pp(names, 0);
                names.pop();
                paren_if(prec >= 2, format!("<{nm}> {bs}"))
            }
            Term::PApp(p, r) => {
                let ps = p.pp(names, 3);
                let rs = r.pp(names, 3);
                paren_if(prec >= 3, format!("{ps} @ {rs}"))
            }
            Term::PathP(fam, a0, a1) => {
                let nm = fresh_binder_name(names.len());
                names.push(nm.clone());
                let fams = fam.pp(names, 0);
                names.pop();
                let a0s = a0.pp(names, 3);
                let a1s = a1.pp(names, 3);
                paren_if(prec >= 3, format!("PathP (<{nm}> {fams}) {a0s} {a1s}"))
            }
            Term::Sys(branches) => {
                let parts: Vec<String> = branches
                    .iter()
                    .map(|(p, t)| format!("{} ↦ {}", p.pp(names), t.pp(names, 0)))
                    .collect();
                format!("[{}]", parts.join(", "))
            }
            Term::Partial(p, a) => {
                let ps = p.pp(names);
                let as_ = a.pp(names, 3);
                paren_if(prec >= 3, format!("Partial {ps} {as_}"))
            }
            Term::Transp(fam, phi, a) => {
                let nm = fresh_binder_name(names.len());
                names.push(nm.clone());
                let fams = fam.pp(names, 0);
                names.pop();
                let phis = phi.pp(names);
                let as_ = a.pp(names, 3);
                paren_if(prec >= 3, format!("transp (<{nm}> {fams}) {phis} {as_}"))
            }
            Term::HComp(ty, phi, u, u0) => {
                let nm = fresh_binder_name(names.len());
                let tys = ty.pp(names, 3);
                let phis = phi.pp(names);
                names.push(nm.clone());
                let us = u.pp(names, 0);
                names.pop();
                let u0s = u0.pp(names, 3);
                paren_if(prec >= 3, format!("hcomp {tys} {phis} (<{nm}> {us}) {u0s}"))
            }
            Term::Glue(a, branches) => {
                let as_ = a.pp(names, 3);
                let bs: Vec<String> = branches
                    .iter()
                    .map(|(p, t, e)| format!("{} ↦ ({}, {})", p.pp(names), t.pp(names, 3), e.pp(names, 3)))
                    .collect();
                paren_if(prec >= 3, format!("Glue {as_} [{}]", bs.join(", ")))
            }
            Term::Unglue(a, branches, u) => {
                let as_ = a.pp(names, 3);
                let bs: Vec<String> = branches
                    .iter()
                    .map(|(p, t, e)| format!("{} ↦ ({}, {})", p.pp(names), t.pp(names, 3), e.pp(names, 3)))
                    .collect();
                let us = u.pp(names, 3);
                paren_if(prec >= 3, format!("unglue {as_} [{}] {us}", bs.join(", ")))
            }
            Term::GlueIntro(branches, a) => {
                let bs: Vec<String> = branches
                    .iter()
                    .map(|(p, t)| format!("{} ↦ {}", p.pp(names), t.pp(names, 0)))
                    .collect();
                let as_ = a.pp(names, 3);
                paren_if(prec >= 3, format!("glue [{}] {as_}", bs.join(", ")))
            }
            Term::Var(i) => {
                let n = names.len();
                if *i < n {
                    names[n - 1 - *i].clone()
                } else {
                    // Free variable (open term): show the raw de Bruijn index.
                    format!("#{i}")
                }
            }
            Term::Const(name, _) => name.to_string(),
            Term::App(..) => {
                let (head, args) = self.unfold_apps();
                let mut s = head.pp(names, 2);
                for a in &args {
                    s.push(' ');
                    s.push_str(&a.pp(names, 3));
                }
                paren_if(prec >= 3, s)
            }
            Term::Lam(d, b) => {
                let nm = fresh_binder_name(names.len());
                let ds = d.pp(names, 0);
                names.push(nm.clone());
                let bs = b.pp(names, 0);
                names.pop();
                paren_if(prec >= 2, format!("fun ({nm} : {ds}) => {bs}"))
            }
            Term::Pi(_, d, b) => {
                let nm = fresh_binder_name(names.len());
                let ds = d.pp(names, 2);
                let dependent = mentions_var(b, 0);
                names.push(nm.clone());
                let bs = b.pp(names, 0);
                names.pop();
                let s = if dependent {
                    format!("({nm} : {ds}) -> {bs}")
                } else {
                    format!("{ds} -> {bs}")
                };
                paren_if(prec >= 2, s)
            }
            Term::Let(g, ty, val, body) => {
                let nm = fresh_binder_name(names.len());
                let tys = ty.pp(names, 0);
                let vs = val.pp(names, 0);
                names.push(nm.clone());
                let bs = body.pp(names, 0);
                names.pop();
                let gs = match g {
                    Grade::Many => String::new(),
                    Grade::Zero => "0".to_string(),
                    Grade::One => "1".to_string(),
                };
                paren_if(prec >= 2, format!("let{gs} {nm} : {tys} := {vs} in {bs}"))
            }
        }
    }
}

/// A short binder name for the de Bruijn depth `d`: `a`, `b`, …, `z`, `a1`, `b1`, ….
fn fresh_binder_name(d: usize) -> String {
    let letter = (b'a' + (d % 26) as u8) as char;
    let cycle = d / 26;
    if cycle == 0 {
        letter.to_string()
    } else {
        format!("{letter}{cycle}")
    }
}

fn paren_if(cond: bool, s: String) -> String {
    if cond {
        format!("({s})")
    } else {
        s
    }
}

/// Does `t` mention the bound variable at de Bruijn index `k` (used to decide whether a
/// `Pi` is a dependent function type or a plain arrow)?
pub(crate) fn mentions_var(t: &Term, k: usize) -> bool {
    match t {
        Term::Var(i) => *i == k,
        Term::App(f, a) => mentions_var(f, k) || mentions_var(a, k),
        Term::Lam(d, b) => mentions_var(d, k) || mentions_var(b, k + 1),
        Term::Pi(_, d, b) => mentions_var(d, k) || mentions_var(b, k + 1),
        Term::Let(_, ty, v, b) => mentions_var(ty, k) || mentions_var(v, k) || mentions_var(b, k + 1),
        Term::Sort(_) | Term::Const(..) | Term::Meta(_) | Term::I | Term::IZero | Term::IOne => false,
        Term::INeg(r) => mentions_var(r, k),
        Term::IMeet(r, s) | Term::IJoin(r, s) => mentions_var(r, k) || mentions_var(s, k),
        Term::PLam(b) => mentions_var(b, k + 1),
        Term::PApp(p, r) => mentions_var(p, k) || mentions_var(r, k),
        Term::PathP(fam, a0, a1) => mentions_var(fam, k + 1) || mentions_var(a0, k) || mentions_var(a1, k),
        Term::Sys(branches) => {
            branches.iter().any(|(p, t)| crate::face::mentions_var(p, k) || mentions_var(t, k))
        }
        Term::Partial(p, a) => crate::face::mentions_var(p, k) || mentions_var(a, k),
        Term::Transp(fam, phi, a) => {
            mentions_var(fam, k + 1) || crate::face::mentions_var(phi, k) || mentions_var(a, k)
        }
        Term::HComp(ty, phi, u, u0) => {
            mentions_var(ty, k)
                || crate::face::mentions_var(phi, k)
                || mentions_var(u, k + 1)
                || mentions_var(u0, k)
        }
        Term::Glue(a, branches) => {
            mentions_var(a, k)
                || branches.iter().any(|(p, t, e)| {
                    crate::face::mentions_var(p, k) || mentions_var(t, k) || mentions_var(e, k)
                })
        }
        Term::Unglue(a, branches, u) => {
            mentions_var(a, k)
                || branches.iter().any(|(p, t, e)| {
                    crate::face::mentions_var(p, k) || mentions_var(t, k) || mentions_var(e, k)
                })
                || mentions_var(u, k)
        }
        Term::GlueIntro(branches, a) => {
            mentions_var(a, k)
                || branches.iter().any(|(p, t)| crate::face::mentions_var(p, k) || mentions_var(t, k))
        }
    }
}

/// The number of free (unbound) de Bruijn variables `t` references: one more than the
/// greatest free index it mentions, or `0` if `t` is closed. Used only to size a
/// fresh-neutral evaluation context when *probing* whether a `Transp` family is
/// genuinely constant in its bound interval variable via full computation (see
/// `crate::kan`'s normalization-aware regularity extension) — i.e. this is the `depth`
/// to pass to [`crate::nbe::Nbe::normalize_open`] so every free variable `t` actually
/// contains gets a binding (an out-of-range index would otherwise panic inside
/// `VEnv::get`). Purely a sizing helper: it does not affect what gets *proven* — that
/// still comes from `mentions_var` on the (fully computed) result — so an
/// over-generous bound is harmless and an exact one is not required for soundness,
/// only for `normalize_open` not to panic.
pub(crate) fn free_var_bound(t: &Term) -> usize {
    free_var_bound_at(t, 0)
}

/// [`free_var_bound`], relative to a nesting `depth` (the number of binders already
/// crossed) — the frame [`crate::face::free_var_bound`] needs to compute the same
/// quantity for a `Cof` atom's subject term without first re-deriving it at depth `0`
/// and subtracting (subtracting after computing at depth 0 would double-floor and lose
/// precision for terms whose own free variables sit at different depths under `Sys`/
/// `Partial`/`Transp`/`HComp`'s own binders — this variant threads `depth` through
/// directly instead, exactly like [`mentions_var`] threads `k`).
pub(crate) fn free_var_bound_at(t: &Term, depth: usize) -> usize {
    fn bump(depth: usize, k: usize) -> usize {
        // A raw index `k` seen at nesting `depth` refers to the free variable
        // `k - depth` in the *outer* frame; contributes `k - depth + 1` to the bound.
        k.saturating_sub(depth).saturating_add(1)
    }
    fn go(t: &Term, depth: usize) -> usize {
        match t {
            Term::Var(i) => {
                if *i >= depth {
                    bump(depth, *i)
                } else {
                    0
                }
            }
            Term::App(f, a) => go(f, depth).max(go(a, depth)),
            Term::Lam(d, b) => go(d, depth).max(go(b, depth + 1)),
            Term::Pi(_, d, b) => go(d, depth).max(go(b, depth + 1)),
            Term::Let(_, ty, v, b) => go(ty, depth).max(go(v, depth)).max(go(b, depth + 1)),
            Term::Sort(_) | Term::Const(..) | Term::Meta(_) | Term::I | Term::IZero | Term::IOne => 0,
            Term::INeg(r) => go(r, depth),
            Term::IMeet(r, s) | Term::IJoin(r, s) => go(r, depth).max(go(s, depth)),
            Term::PLam(b) => go(b, depth + 1),
            Term::PApp(p, r) => go(p, depth).max(go(r, depth)),
            Term::PathP(fam, a0, a1) => go(fam, depth + 1).max(go(a0, depth)).max(go(a1, depth)),
            Term::Sys(branches) => branches
                .iter()
                .map(|(p, t)| crate::face::free_var_bound(p, depth).max(go(t, depth)))
                .max()
                .unwrap_or(0),
            Term::Partial(p, a) => crate::face::free_var_bound(p, depth).max(go(a, depth)),
            Term::Transp(fam, phi, a) => go(fam, depth + 1)
                .max(crate::face::free_var_bound(phi, depth))
                .max(go(a, depth)),
            Term::HComp(ty, phi, u, u0) => go(ty, depth)
                .max(crate::face::free_var_bound(phi, depth))
                .max(go(u, depth + 1))
                .max(go(u0, depth)),
            Term::Glue(a, branches) => go(a, depth).max(
                branches
                    .iter()
                    .map(|(p, t, e)| {
                        crate::face::free_var_bound(p, depth).max(go(t, depth)).max(go(e, depth))
                    })
                    .max()
                    .unwrap_or(0),
            ),
            Term::Unglue(a, branches, u) => go(a, depth)
                .max(
                    branches
                        .iter()
                        .map(|(p, t, e)| {
                            crate::face::free_var_bound(p, depth).max(go(t, depth)).max(go(e, depth))
                        })
                        .max()
                        .unwrap_or(0),
                )
                .max(go(u, depth)),
            Term::GlueIntro(branches, a) => go(a, depth).max(
                branches
                    .iter()
                    .map(|(p, t)| crate::face::free_var_bound(p, depth).max(go(t, depth)))
                    .max()
                    .unwrap_or(0),
            ),
        }
    }
    go(t, depth)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lift_shifts_free_only() {
        // λ. Var(1)  — Var(0) is bound, Var(1) is free.
        let t = Term::lam(Term::typ(0), Term::Var(1));
        let lifted = t.lift(2, 0);
        assert_eq!(lifted, Term::lam(Term::typ(0), Term::Var(3)));
    }

    #[test]
    fn instantiate_beta() {
        // (λx. x) applied to `c` ⇒ `c`.
        let body = Term::Var(0);
        assert_eq!(body.instantiate(&Term::cnst(name("c"), vec![])), Term::cnst(name("c"), vec![]));
    }

    #[test]
    fn instantiate_decrements_outer() {
        // body = Var(1) (a variable from outside the binder); instantiating the
        // binder with `c` must turn Var(1) into Var(0).
        let body = Term::Var(1);
        assert_eq!(body.instantiate(&Term::cnst(name("c"), vec![])), Term::Var(0));
    }

    #[test]
    fn unfold_application_spine() {
        let t = Term::apps(Term::cnst(name("f"), vec![]), [Term::Var(0), Term::Var(1)]);
        let (h, args) = t.unfold_apps();
        assert_eq!(h, Term::cnst(name("f"), vec![]));
        assert_eq!(args, vec![Term::Var(0), Term::Var(1)]);
    }
}
