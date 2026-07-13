//! Normalization by Evaluation — a fast, substitution-free normalizer.
//!
//! The trusted [`reduce`](crate::reduce) is correct but naive: it re-traverses and
//! re-substitutes on every β/ι step, which is quadratic on reduction-heavy terms (and
//! reflection — running a decision procedure *inside* the kernel — is exactly that).
//! NbE instead **evaluates** a term once into a semantic domain of [`Value`]s (with
//! closures capturing environments, and neutral terms for stuck computations), then
//! **reads back** (quotes) the value to a normal-form term. Reduction becomes ordinary
//! evaluation; there is no repeated substitution.
//!
//! This module is built **beside** the trusted reducer, not in place of it: the tests
//! differentially check that `normalize` agrees with the reducer (`is_def_eq(t,
//! normalize t)` holds) and that `conv` agrees with the kernel's conversion. So it can
//! be adopted as the performance path with confidence, while the proven reducer
//! remains the reference.

use crate::env::{CircleRole, CubHitRole, Decl, Env, HitRole, I2Role, QuotRole, S1cRole, TruncRole};
use crate::face::{Atom, Cof};
use crate::level::{self, Level};
use crate::term::{Grade, Name, Term};
use std::rc::Rc;

/// A semantic value (weak-head evaluated, with delayed bodies under closures).
///
/// Children are held behind [`Rc`] so cloning a `Value` — which happens on every
/// variable lookup and every environment extension — is O(1) (a refcount bump) rather
/// than a deep copy of the whole spine. This, with the shared [`VEnv`], is what keeps
/// normalization from quadratically re-copying environments as it descends under binders.
#[derive(Clone)]
pub enum Value {
    Sort(Level),
    Pi(Grade, Rc<Value>, Closure),
    Lam(Rc<Value>, Closure),
    /// A rigid head applied to a spine of argument values (a neutral term, or a
    /// canonical constructor application — both are "head + spine").
    Stuck(Head, Vec<Rc<Value>>),

    // ---- Phase-1 cubical (see `crate::cubical`) ----
    /// The phantom interval-sort marker (never a real value; see [`crate::term::Term::I`]).
    I,
    /// The left interval endpoint.
    IZero,
    /// The right interval endpoint.
    IOne,
    /// **Phase 3.5** (De Morgan interval, see `crate::cubical`): reversal/meet/join.
    /// [`Nbe::eval`] eagerly folds the bounded-lattice **identity/absorption/
    /// double-negation laws** (`~i0=i1`, `~i1=i0`, `~~r=r`, `i0∧r=r0=i0`, `i1∧r=r`,
    /// `i1∨r=i1`, `i0∨r=r` — the smart constructors [`veval_ineg`]/[`veval_imeet`]/
    /// [`veval_ijoin`]) whenever the decisive operand is already a literal `IZero`/
    /// `IOne` value; a genuinely open combination (neither side decided) still stays
    /// wrapped exactly as before. This is *not* the full DNF-based normal form
    /// `crate::cubical::normalize_interval` computes (that remains the one
    /// *comparison-time* authority two interval expressions are checked against, via
    /// [`Nbe::conv`]/`alpha_eta_eq`/`crate::check::Checker::compare` — see those call
    /// sites) — it is a strictly smaller, purely *local* eager simplification that
    /// only ever collapses a connective once one operand is already a decided
    /// endpoint. The point is completeness, not an alternate equality theory: once a
    /// bound interval variable is substituted by a literal `i0`/`i1` (as happens
    /// whenever a `Transp`'s regularity probe or a `PathP` boundary instantiates its
    /// binder), any `∧`/`∨`/`~` built on top of it collapses immediately during
    /// evaluation instead of staying inertly wrapped — which is exactly what lets
    /// [`crate::kan::family_is_constant`]'s already-existing normalization-aware
    /// probe (see that function's doc) see through one more layer of `∧`/`∨` nesting
    /// (e.g. the connection-square shape `i0 ∧ j` that [`crate::cubical::j`]'s
    /// `connect` term builds) and correctly judge more families constant. Soundness:
    /// these are the same, already-accepted bounded De Morgan algebra laws
    /// `crate::cubical::normalize_interval`'s DNF machinery already encodes and every
    /// existing `interval_eq`/`normalize_interval` call site already treats as valid
    /// definitional equalities — applying them a step earlier (during evaluation,
    /// not just at comparison time) proves no new equation, it just lets already-true
    /// equations fire in more contexts. Termination: each smart constructor performs
    /// O(1) work per call (matches on already-fully-evaluated `Value` operands, never
    /// recurses into an unevaluated closure), so this cannot loop or add unbounded
    /// work to `eval`.
    INeg(Rc<Value>),
    IMeet(Rc<Value>, Rc<Value>),
    IJoin(Rc<Value>, Rc<Value>),
    /// A path abstraction `⟨i⟩ body` — the interval-binder analogue of `Value::Lam`.
    PLam(Closure),
    /// `PathP (λi. family) a0 a1`, the semantic form of [`crate::term::Term::PathP`].
    PathP(Rc<Value>, Rc<Value>, Closure),

    // ---- Phase-2 cubical (see `crate::face`) ----
    /// A **stuck** system: no branch's guard is currently decided `⊤` (see
    /// [`Nbe::eval_face`]), so it stays as data — captured environment plus the raw
    /// (unevaluated) branches, exactly like [`Closure`] defers a binder's body. Read
    /// back on demand by [`Nbe::quote`].
    Sys(SysClosure),
    /// `Partial φ A` — `A` evaluated eagerly (it's in the very same context as `φ`,
    /// no extra binder), `φ` kept raw alongside the environment it closes over (same
    /// reason as [`Value::Sys`]).
    Partial(Rc<Value>, FaceClosure),

    // ---- Phase-3 cubical: the minimal sound Kan core (see `crate::kan`) ----
    /// A **stuck** `transp` — the regularity rule (`crate::kan`) didn't fire (the
    /// family genuinely mentions the interval variable, and `φ` isn't decided `⊤`),
    /// so it stays as deferred data, the `Value::Sys`/`Value::Partial` pattern.
    Transp(TranspClosure, Rc<Value>),
    /// A **stuck** `hcomp` — `φ` isn't decided `⊤`, so no reduction rule applies yet.
    HComp(HCompClosure, Rc<Value>),

    // ---- Step 1 of univalence: `Glue` (see `crate::term::Term::Glue`) ----
    /// A **stuck** `Glue A [φ_1 ↦ (T_1,e_1), …]` — no branch's `φ_k` is decided
    /// `⊤`, and not every `φ_k` is decided `⊥` (see [`Nbe::eval_faces`]), so it
    /// stays as deferred data: `A` and every branch's `T_k`/`e_k` evaluated
    /// eagerly (all live in the very same context as the `φ`s, no extra binder —
    /// exactly like [`Value::Partial`]'s `A`), the `φ_k`s kept raw alongside one
    /// shared captured environment (the [`GlueClosure`] pattern, the multi-branch
    /// analogue of [`FaceClosure`]).
    Glue(Rc<Value>, GlueClosure),
    /// A **stuck** `unglue A [φ_1 ↦ (T_1,e_1), …] u` — mirrors [`Value::Glue`]'s
    /// stuck case, plus the scrutinee `u`.
    Unglue(Rc<Value>, GlueClosure, Rc<Value>),
    /// A **stuck** `glue [φ_1 ↦ t_1, …] a` (see
    /// [`crate::term::Term::GlueIntro`]): no branch's `φ_k` is decided `⊤`, and
    /// not every `φ_k` is decided `⊥` (mirrors [`Nbe::eval_glue_branches`]'s
    /// decision, specialized to a `(φ,t)` list with no `e`), so it stays as
    /// deferred data — every branch's `t_k` evaluated eagerly, the `φ_k`s kept
    /// raw alongside one shared captured environment (the [`GlueIntroClosure`]
    /// pattern, the `e`-free analogue of [`GlueClosure`]), plus the base `a`.
    GlueIntro(GlueIntroClosure, Rc<Value>),
}

/// Deferred data for a stuck [`Value::GlueIntro`]: the raw guards `φ_1, …, φ_n`
/// together with their branches' *eagerly evaluated* `t_k` values, sharing one
/// captured environment (the `e`-free analogue of [`GlueClosure`]).
#[derive(Clone)]
pub struct GlueIntroClosure {
    env: Rc<VEnv>,
    branches: Rc<Vec<(Rc<Cof>, Rc<Value>)>>,
}

/// [`GlueDecision`]'s analogue for [`Value::GlueIntro`] (no `e` to carry).
enum GlueIntroDecision {
    Top(Rc<Value>),
    Bot,
    Stuck(Vec<(Rc<Cof>, Rc<Value>)>),
}

/// Deferred data for a stuck [`Value::Glue`]/[`Value::Unglue`]: the raw guards
/// `φ_1, …, φ_n` together with their branches' *eagerly evaluated* `T_k`/`e_k`
/// values, sharing one captured environment (used only to quote each `φ_k` back
/// on demand, the [`FaceClosure`] pattern generalized to `n` branches).
#[derive(Clone)]
pub struct GlueClosure {
    env: Rc<VEnv>,
    branches: Rc<Vec<(Rc<Cof>, Rc<Value>, Rc<Value>)>>,
}

/// Result of scanning a `Glue`/`unglue`'s branch list's guards against a `venv`
/// (see [`Nbe::eval_glue_branches`]): the first decided-`⊤` branch's evaluated
/// `T`, or "every branch is decided `⊥`", or (if still undecided) every branch's
/// evaluated `(φ, T, e)` for building the stuck [`Value::Glue`]/[`Value::Unglue`].
enum GlueDecision {
    Top(Rc<Value>),
    Bot,
    Stuck(Vec<(Rc<Cof>, Rc<Value>, Rc<Value>)>),
}

/// Deferred face-formula data: a raw (unevaluated) [`Cof`]-guarded system's branches
/// together with the environment they close over — the [`Closure`] analogue for
/// [`Value::Sys`], which (unlike `Lam`/`PLam`) introduces no extra binder, so there's
/// no `apply`, only [`Nbe::quote_cof`]/[`Nbe::eval_face`] reading it back or
/// evaluating on demand.
#[derive(Clone)]
pub struct SysClosure {
    env: Rc<VEnv>,
    branches: Rc<Vec<(Rc<Cof>, Rc<Term>)>>,
}

/// Deferred face-formula data for [`Value::Partial`]: a single raw guard `φ`
/// together with the environment it closes over (the one-guard analogue of
/// [`SysClosure`]).
#[derive(Clone)]
pub struct FaceClosure {
    env: Rc<VEnv>,
    phi: Rc<Cof>,
}

/// Deferred data for a stuck [`Value::Transp`]: the raw (unevaluated) family
/// (under one interval binder, like [`Closure`]) plus the raw guard `φ`, sharing
/// one captured environment.
#[derive(Clone)]
pub struct TranspClosure {
    env: Rc<VEnv>,
    fam: Rc<Term>,
    phi: Rc<Cof>,
}

/// Deferred data for a stuck [`Value::HComp`]: the eagerly-evaluated type `A`, the
/// raw guard `φ`, and the raw (unevaluated) system-line `u` (under one interval
/// binder), sharing one captured environment.
#[derive(Clone)]
pub struct HCompClosure {
    env: Rc<VEnv>,
    ty: Rc<Value>,
    phi: Rc<Cof>,
    u: Rc<Term>,
}

/// The rigid head of a neutral/canonical value.
#[derive(Clone)]
pub enum Head {
    /// A free variable, by de Bruijn **level** (stable under going under binders).
    Var(usize),
    /// A constant: an axiom, inductive, constructor, or a recursor stuck on a neutral.
    Const(Name, Vec<Level>),
    /// An unsolved metavariable (elaboration only).
    Meta(u32),
    /// A neutral **path application** `p @ r` where `p` didn't reduce to a `PLam` —
    /// this is an atomic head exactly like `Var`/`Const`/`Meta` (see [`Value::Stuck`]'s
    /// doc comment): further ordinary applications simply extend the spine on top of
    /// it, and quoting rebuilds `Term::PApp(quote p, quote r)`.
    PathApp(Rc<Value>, Rc<Value>),
}

/// A delayed term body together with the environment it closes over.
#[derive(Clone)]
pub struct Closure {
    env: Rc<VEnv>,
    body: Rc<Term>,
}

/// A persistent (immutable, shared) value environment, innermost binding at the head.
/// Extending under a binder is a single `Cons` allocation that *shares* the tail, and
/// cloning is an `Rc` bump — so going under a binder no longer copies the environment.
/// `Var(i)` reads the `i`-th cell from the head.
pub(crate) enum VEnv {
    Nil,
    Cons(Rc<Value>, Rc<VEnv>),
}

impl VEnv {
    /// The value bound to de Bruijn index `i` (0 = innermost = head).
    fn get(&self, i: usize) -> &Rc<Value> {
        let mut env = self;
        let mut k = i;
        loop {
            match env {
                VEnv::Cons(v, rest) => {
                    if k == 0 {
                        return v;
                    }
                    k -= 1;
                    env = rest;
                }
                VEnv::Nil => panic!("nbe: de Bruijn index {i} out of range"),
            }
        }
    }

    /// Push `v` as the new innermost binding, sharing `self` as the tail.
    fn cons(self: &Rc<Self>, v: Rc<Value>) -> Rc<VEnv> {
        Rc::new(VEnv::Cons(v, self.clone()))
    }

    /// The number of bindings currently in scope (0 for `Nil`) — i.e. the de
    /// Bruijn *level* the next `cons`ed value would occupy. Used by both
    /// [`Nbe::family_whnf_pi`] and [`Nbe::family_is_constant_value`] to push
    /// their fresh probe marker at the correct, honest level (so
    /// [`Nbe::quote`]'s level-to-index translation round-trips exactly),
    /// exactly the same discipline [`Nbe::quote`] itself already uses
    /// everywhere it forces a closure body (`Head::Var(level)`, then quotes
    /// the result at `level + 1`) — see those methods' docs for why sharing
    /// this one discipline (rather than each probe inventing its own
    /// freshness scheme) is what makes it safe for one probe to fire nested
    /// inside the other.
    fn depth(&self) -> usize {
        let mut env = self;
        let mut n = 0;
        while let VEnv::Cons(_, rest) = env {
            n += 1;
            env = rest;
        }
        n
    }
}

/// The evaluator, bound to an environment (and optionally a metacontext, for
/// elaboration-time normalization of terms containing solved metavariables).
pub struct Nbe<'a> {
    env: &'a Env,
    metas: Option<&'a [Option<Term>]>,
}

impl<'a> Nbe<'a> {
    pub fn new(env: &'a Env) -> Self {
        Self { env, metas: None }
    }

    /// An evaluator that resolves solved metavariables from `metas` (elaboration).
    pub fn with_metas(env: &'a Env, metas: &'a [Option<Term>]) -> Self {
        Self { env, metas: Some(metas) }
    }

    /// Evaluate `t` under the shared value environment `venv` (innermost at the head).
    fn eval(&self, venv: &Rc<VEnv>, t: &Term) -> Rc<Value> {
        match t {
            Term::Sort(l) => Rc::new(Value::Sort(l.clone())),
            Term::Var(i) => venv.get(*i).clone(),
            Term::App(f, a) => {
                let vf = self.eval(venv, f);
                let va = self.eval(venv, a);
                self.vapp(vf, va)
            }
            Term::Lam(d, b) => Rc::new(Value::Lam(
                self.eval(venv, d),
                Closure { env: venv.clone(), body: b.clone() },
            )),
            Term::Pi(g, d, b) => Rc::new(Value::Pi(
                *g,
                self.eval(venv, d),
                Closure { env: venv.clone(), body: b.clone() },
            )),
            Term::Let(_, _, v, b) => {
                let vv = self.eval(venv, v);
                self.eval(&venv.cons(vv), b)
            }
            Term::Const(n, ls) => match self.env.get(n) {
                // Unfold the definition. When it has no universe parameters (`ls` empty)
                // `instantiate_levels` would be the identity — skip it and evaluate the
                // stored body directly, avoiding a full re-traversal/clone on every use.
                Some(Decl::Def { value, .. }) => {
                    if ls.is_empty() {
                        self.eval(&Rc::new(VEnv::Nil), value)
                    } else {
                        self.eval(&Rc::new(VEnv::Nil), &value.instantiate_levels(ls))
                    }
                }
                _ => Rc::new(Value::Stuck(Head::Const(n.clone(), ls.clone()), Vec::new())),
            },
            Term::Meta(m) => match self.metas.and_then(|ms| ms.get(*m as usize).cloned().flatten()) {
                Some(sol) => self.eval(&Rc::new(VEnv::Nil), &sol), // a solved meta unfolds
                None => Rc::new(Value::Stuck(Head::Meta(*m), Vec::new())),
            },
            Term::I => Rc::new(Value::I),
            Term::IZero => Rc::new(Value::IZero),
            Term::IOne => Rc::new(Value::IOne),
            Term::INeg(r) => veval_ineg(self.eval(venv, r)),
            Term::IMeet(r, s) => veval_imeet(self.eval(venv, r), self.eval(venv, s)),
            Term::IJoin(r, s) => veval_ijoin(self.eval(venv, r), self.eval(venv, s)),
            Term::PLam(b) => {
                Rc::new(Value::PLam(Closure { env: venv.clone(), body: b.clone() }))
            }
            Term::PApp(p, r) => {
                let vp = self.eval(venv, p);
                let vr = self.eval(venv, r);
                self.vpapp(vp, vr)
            }
            Term::PathP(fam, a0, a1) => Rc::new(Value::PathP(
                self.eval(venv, a0),
                self.eval(venv, a1),
                Closure { env: venv.clone(), body: fam.clone() },
            )),
            // System reduction (see `crate::face`, and `crate::reduce::Reducer::whnf`'s
            // matching `Term::Sys` case — differentially tested): fire the first
            // branch whose guard is *currently* decided true; otherwise stay stuck.
            Term::Sys(branches) => {
                match branches.iter().find(|(phi, _)| self.eval_face(venv, phi) == Some(true)) {
                    Some((_, t)) => self.eval(venv, t),
                    None => Rc::new(Value::Sys(SysClosure {
                        env: venv.clone(),
                        branches: Rc::new(branches.clone()),
                    })),
                }
            }
            Term::Partial(phi, a) => Rc::new(Value::Partial(
                self.eval(venv, a),
                FaceClosure { env: venv.clone(), phi: phi.clone() },
            )),
            // `transp` (see `crate::kan`, and `crate::reduce::Reducer::whnf`'s
            // matching `Term::Transp` case — differentially tested): the
            // regularity rule — structural constancy, extended to
            // computed/normalization-aware constancy via
            // `crate::kan::family_is_constant` (never `φ`, see `crate::kan`'s
            // soundness argument) — fires as evaluation of `a`; otherwise stays
            // stuck.
            Term::Transp(fam, phi, a) => {
                if self.family_is_constant_value(venv, fam) {
                    self.eval(venv, a)
                } else if let Term::Pi(_g, dom, cod) = fam.as_ref() {
                    // `Π`-case filling (see `crate::kan`'s "Phase 3.6" doc, and
                    // `crate::reduce::Reducer::whnf`'s matching arm — differentially
                    // tested): the built term introduces no new *free* variable (every
                    // fresh binder it creates is bound within it), so it's evaluated
                    // against the very same `venv`.
                    let built = crate::kan::transp_pi_rule(dom, cod, a);
                    self.eval(venv, &built)
                } else if let Some((wdom, wcod)) = self.family_whnf_pi(venv, fam) {
                    // The completeness fix (see `Self::family_whnf_pi`'s doc): `fam`
                    // is not *syntactically* a `Π`, but genuinely computes to one
                    // against the real `venv` (e.g. a `J`-motive application that
                    // only beta-reduces to an arrow type). Same builder, same
                    // "introduces no new free variable" argument as the syntactic
                    // branch immediately above — `wdom`/`wcod` are `fam`'s own
                    // evaluated-then-quoted dom/cod, in the identical calling
                    // convention.
                    let built = crate::kan::transp_pi_rule(&wdom, &wcod, a);
                    self.eval(venv, &built)
                } else if let Some(built) = crate::kan::transp_inductive_rule(self.env, fam, a) {
                    // Parametrized-inductive filling (see `crate::kan`'s "Phase
                    // 3.10" doc, and `crate::reduce::Reducer::whnf`'s matching
                    // arm — differentially tested): matched *syntactically* (no
                    // evaluation) on both `fam` and `a`; the built term
                    // introduces no new *free* variable, so it's evaluated
                    // against the very same `venv`.
                    self.eval(venv, &built)
                } else {
                    Rc::new(Value::Transp(
                        TranspClosure { env: venv.clone(), fam: fam.clone(), phi: phi.clone() },
                        self.eval(venv, a),
                    ))
                }
            }
            // `hcomp` (see `crate::kan`): the trivial-system rule, `φ` decided `⊤`,
            // evaluates the line `u` at `i1`; otherwise stays stuck.
            Term::HComp(ty, phi, u, u0) => {
                if self.eval_face(venv, phi) == Some(true) {
                    self.eval(&venv.cons(Rc::new(Value::IOne)), u)
                } else if let Term::Pi(_g, dom, cod) = ty.as_ref() {
                    // `Π`-case filling (see `crate::kan`'s "Phase 3.7" doc, and
                    // `crate::reduce::Reducer::whnf`'s matching arm — differentially
                    // tested): only fires when `u` is itself a literal `Sys`; the
                    // built term introduces no new *free* variable, so it's
                    // evaluated against the very same `venv`.
                    match crate::kan::hcomp_pi_rule(dom, cod, phi, u, u0) {
                        Some(built) => self.eval(venv, &built),
                        None => Rc::new(Value::HComp(
                            HCompClosure {
                                env: venv.clone(),
                                ty: self.eval(venv, ty),
                                phi: phi.clone(),
                                u: u.clone(),
                            },
                            self.eval(venv, u0),
                        )),
                    }
                } else if let Term::PathP(fam, a0, a1) = ty.as_ref() {
                    // `PathP`-case filling (see `crate::kan`'s "Phase 3.9" doc, and
                    // `crate::reduce::Reducer::whnf`'s matching arm — differentially
                    // tested): only fires when `u` is itself a literal `Sys`; the
                    // built term introduces no new *free* variable, so it's
                    // evaluated against the very same `venv`.
                    match crate::kan::hcomp_pathp_rule(fam, a0, a1, phi, u, u0) {
                        Some(built) => self.eval(venv, &built),
                        None => Rc::new(Value::HComp(
                            HCompClosure {
                                env: venv.clone(),
                                ty: self.eval(venv, ty),
                                phi: phi.clone(),
                                u: u.clone(),
                            },
                            self.eval(venv, u0),
                        )),
                    }
                } else {
                    // Constructor-compatible `hcomp` for a user inductive (see
                    // `crate::kan`'s "Phase 3.11" doc, and
                    // `crate::reduce::Reducer::whnf`'s matching arm —
                    // differentially tested): matched *syntactically* (no
                    // evaluation) on `ty`/`u`/`u0`; the built term introduces
                    // no new *free* variable, so it's evaluated against the
                    // very same `venv`.
                    match crate::kan::hcomp_inductive_rule(self.env, ty, phi, u, u0) {
                        Some(built) => self.eval(venv, &built),
                        None => Rc::new(Value::HComp(
                            HCompClosure {
                                env: venv.clone(),
                                ty: self.eval(venv, ty),
                                phi: phi.clone(),
                                u: u.clone(),
                            },
                            self.eval(venv, u0),
                        )),
                    }
                }
            }
            // `Glue A [φ_1 ↦ (T_1,e_1), …]` (see `crate::term::Term::Glue`, and
            // `crate::reduce::Reducer::whnf`'s matching arm — differentially
            // tested): the strictness laws, generalized to `n` branches — the
            // first `φ_k` decided `⊤` reduces to `T_k`; every `φ_k` decided `⊥`
            // reduces to `A` — mirror `Value::Sys`'s "fire once decided"
            // convention; otherwise stays stuck.
            Term::Glue(a, branches) => match self.eval_glue_branches(venv, branches) {
                GlueDecision::Top(t) => t,
                GlueDecision::Bot => self.eval(venv, a),
                GlueDecision::Stuck(vbranches) => Rc::new(Value::Glue(
                    self.eval(venv, a),
                    GlueClosure { env: venv.clone(), branches: Rc::new(vbranches) },
                )),
            },
            // `unglue A [φ_1 ↦ (T_1,e_1), …] u` (see `crate::term::Term::Unglue`):
            // on a decided `⊤` branch, `e_k.f u`; off every branch (all `⊥`), the
            // identity; otherwise stays stuck.
            Term::Unglue(a, branches, u) => {
                let uv = self.eval(venv, u);
                // β: `unglue A […] (glue […] a) ↦ a` (see
                // `crate::term::Term::GlueIntro`'s doc, and
                // `crate::reduce::Reducer::whnf`'s matching arm — differentially
                // tested) — checked before the ⊤/⊥ strictness rules below, since
                // it fires unconditionally once the scrutinee is literally a
                // `glue` introduction.
                if let Value::GlueIntro(_, ga) = &*uv {
                    ga.clone()
                } else if let Some((_, t, e)) =
                    branches.iter().find(|(phi, _, _)| self.eval_face(venv, phi) == Some(true))
                {
                    // `Equiv.f T A e u` (see `crate::reduce::Reducer::whnf`'s
                    // `Term::Unglue` arm for why the level argument is an inert
                    // placeholder — `Equiv.f`'s *value* never inspects it). Built
                    // and evaluated as a genuine `Term`, not assembled directly
                    // from a `Value::Stuck` head + `vapp`: `vapp` only fires ι/ν
                    // rules on an already-neutral head, it does **not** δ-unfold a
                    // plain `Decl::Def` like `Equiv.f` — going through `self.eval`
                    // on the built term takes the ordinary `Term::Const` arm,
                    // which does perform that unfolding.
                    let ef_term = Term::apps(
                        Term::cnst(crate::term::name("Equiv.f"), vec![level::Level::of_nat(0)]),
                        [(**t).clone(), (**a).clone(), (**e).clone(), (**u).clone()],
                    );
                    self.eval(venv, &ef_term)
                } else if branches.iter().all(|(phi, _, _)| self.eval_face(venv, phi) == Some(false)) {
                    uv
                } else {
                    Rc::new(Value::Unglue(
                        self.eval(venv, a),
                        GlueClosure {
                            env: venv.clone(),
                            branches: Rc::new(
                                branches
                                    .iter()
                                    .map(|(p, t, e)| (p.clone(), self.eval(venv, t), self.eval(venv, e)))
                                    .collect(),
                            ),
                        },
                        uv,
                    ))
                }
            }
            // `glue [φ_1 ↦ t_1, …] a` (see `crate::term::Term::GlueIntro`, and
            // `crate::reduce::Reducer::whnf`'s matching arm — differentially
            // tested): the same two strictness laws as `Term::Glue` — the first
            // `φ_k` decided `⊤` reduces to `t_k`; every `φ_k` decided `⊥` reduces
            // to plain `a`; otherwise stays stuck.
            Term::GlueIntro(branches, a) => match self.eval_glue_intro_branches(venv, branches) {
                GlueIntroDecision::Top(t) => t,
                GlueIntroDecision::Bot => self.eval(venv, a),
                GlueIntroDecision::Stuck(vbranches) => Rc::new(Value::GlueIntro(
                    GlueIntroClosure { env: venv.clone(), branches: Rc::new(vbranches) },
                    self.eval(venv, a),
                )),
            },
        }
    }

    /// [`Self::eval_glue_branches`]'s analogue for [`Term::GlueIntro`] (no `e` to
    /// carry per branch).
    fn eval_glue_intro_branches(
        &self,
        venv: &Rc<VEnv>,
        branches: &[(Rc<Cof>, Rc<Term>)],
    ) -> GlueIntroDecision {
        if let Some((_, t)) = branches.iter().find(|(phi, _)| self.eval_face(venv, phi) == Some(true)) {
            return GlueIntroDecision::Top(self.eval(venv, t));
        }
        if branches.iter().all(|(phi, _)| self.eval_face(venv, phi) == Some(false)) {
            return GlueIntroDecision::Bot;
        }
        GlueIntroDecision::Stuck(branches.iter().map(|(p, t)| (p.clone(), self.eval(venv, t))).collect())
    }

    /// Evaluate every branch's guard against `venv`; if the first decided-`⊤`
    /// branch is found, eagerly evaluate *just its `T`* and return it (`unglue`
    /// doesn't need it, `Glue`'s `Top` case does); if every branch is decided `⊥`,
    /// report that; otherwise evaluate every branch's `T`/`e` (needed either way
    /// for the stuck `Value`) and report the whole list.
    fn eval_glue_branches(
        &self,
        venv: &Rc<VEnv>,
        branches: &[(Rc<Cof>, Rc<Term>, Rc<Term>)],
    ) -> GlueDecision {
        if let Some((_, t, _)) = branches.iter().find(|(phi, _, _)| self.eval_face(venv, phi) == Some(true)) {
            return GlueDecision::Top(self.eval(venv, t));
        }
        if branches.iter().all(|(phi, _, _)| self.eval_face(venv, phi) == Some(false)) {
            return GlueDecision::Bot;
        }
        GlueDecision::Stuck(
            branches
                .iter()
                .map(|(p, t, e)| (p.clone(), self.eval(venv, t), self.eval(venv, e)))
                .collect(),
        )
    }


    /// Evaluate a single face atom's subject against `venv` and classify it: `Some`
    /// when the subject has evaluated all the way to a *decided* literal endpoint (so
    /// the atom is decided), `None` when it's still genuinely open. Phase 3.5 (De
    /// Morgan interval, see `crate::cubical`): goes through [`interval_endpoint`],
    /// which additionally decides connections (`~`/`∧`/`∨`) whose value is forced by
    /// their operands even when built from a mix of literals and open variables (e.g.
    /// `i0 ∧ j` is decided `0` regardless of `j`) — the semantic-value analogue of
    /// `crate::face`'s `connection_atom` decomposition, kept as an independent
    /// implementation per this module's differential-testing convention.
    fn eval_face_atom(&self, venv: &Rc<VEnv>, atom: &Atom) -> Option<bool> {
        let (subject, want_one) = match atom {
            Atom::Eq0(t) => (t, false),
            Atom::Eq1(t) => (t, true),
        };
        interval_endpoint(&self.eval(venv, subject)).map(|is_one| is_one == want_one)
    }

    /// Three-valued evaluation of a cofibration against `venv` (`Some(true)` =
    /// decided `⊤`, `Some(false)` = decided `⊥`, `None` = still open) — the NbE
    /// analogue of `crate::face::is_true`, kept as a genuinely separate
    /// implementation (operating on evaluated [`Value`]s, not substituted [`Term`]s)
    /// so the two engines' system-reduction behaviour can be differentially tested
    /// against each other, matching this crate's standing convention.
    fn eval_face(&self, venv: &Rc<VEnv>, phi: &Cof) -> Option<bool> {
        match phi {
            Cof::Bot => Some(false),
            Cof::Top => Some(true),
            Cof::Atom(a) => self.eval_face_atom(venv, a),
            Cof::And(a, b) => match (self.eval_face(venv, a), self.eval_face(venv, b)) {
                (Some(false), _) | (_, Some(false)) => Some(false),
                (Some(true), Some(true)) => Some(true),
                _ => None,
            },
            Cof::Or(a, b) => match (self.eval_face(venv, a), self.eval_face(venv, b)) {
                (Some(true), _) | (_, Some(true)) => Some(true),
                (Some(false), Some(false)) => Some(false),
                _ => None,
            },
        }
    }

    /// Read a raw (unevaluated) cofibration back to a normal-form `Cof` by
    /// evaluating and quoting each atom's subject against `venv`/`level` (mirrors
    /// [`Self::quote`] for ordinary subterms — used by [`Self::quote`]'s
    /// `Value::Sys`/`Value::Partial` cases).
    fn quote_cof(&self, level: usize, venv: &Rc<VEnv>, phi: &Cof) -> Cof {
        match phi {
            Cof::Bot => Cof::Bot,
            Cof::Top => Cof::Top,
            Cof::Atom(Atom::Eq0(t)) => Cof::eq0(self.quote(level, &self.eval(venv, t))),
            Cof::Atom(Atom::Eq1(t)) => Cof::eq1(self.quote(level, &self.eval(venv, t))),
            Cof::And(a, b) => Cof::and(self.quote_cof(level, venv, a), self.quote_cof(level, venv, b)),
            Cof::Or(a, b) => Cof::or(self.quote_cof(level, venv, a), self.quote_cof(level, venv, b)),
        }
    }

    /// Apply a path value to an interval-value argument (the interval-binder analogue
    /// of [`Self::vapp`]): `(PLam body) @ r ↦ body[i := r]`; anything else (a neutral)
    /// stays stuck as a [`Head::PathApp`] atomic head, exactly mirroring
    /// [`crate::reduce::Reducer::whnf`]'s `Term::PApp` case.
    fn vpapp(&self, p: Rc<Value>, r: Rc<Value>) -> Rc<Value> {
        match &*p {
            Value::PLam(clo) => self.apply(clo, r),
            _ => Rc::new(Value::Stuck(Head::PathApp(p, r), Vec::new())),
        }
    }

    /// Apply a value to an argument (β, plus ι when a recursor saturates).
    fn vapp(&self, f: Rc<Value>, a: Rc<Value>) -> Rc<Value> {
        match &*f {
            Value::Lam(_, clo) => self.apply(clo, a),
            Value::Stuck(h, spine) => {
                let mut spine = spine.clone();
                spine.push(a);
                // A recursor may fire (ι); otherwise a destructor may fire (ν);
                // otherwise `Quot.lift` may fire (the quotient computation rule).
                let stuck = self.try_iota(h.clone(), spine);
                if let Value::Stuck(h2, spine2) = &*stuck {
                    let stuck = self.try_nu(h2.clone(), spine2.clone());
                    if let Value::Stuck(h3, spine3) = &*stuck {
                        let stuck = self.try_quot_lift(h3.clone(), spine3.clone());
                        if let Value::Stuck(h4, spine4) = &*stuck {
                            let stuck = self.try_trunc_lift(h4.clone(), spine4.clone());
                            if let Value::Stuck(h5, spine5) = &*stuck {
                                let stuck = self.try_trunc_rec(h5.clone(), spine5.clone());
                                if let Value::Stuck(h6, spine6) = &*stuck {
                                    let stuck = self.try_circle_rec(h6.clone(), spine6.clone());
                                    if let Value::Stuck(h7, spine7) = &*stuck {
                                        let stuck = self.try_i2_rec(h7.clone(), spine7.clone());
                                        if let Value::Stuck(h8, spine8) = &*stuck {
                                            let stuck = self.try_s1c_rec(h8.clone(), spine8.clone());
                                            if let Value::Stuck(h9, spine9) = &*stuck {
                                                let stuck =
                                                    self.try_cubical_hit_rec(h9.clone(), spine9.clone());
                                                if let Value::Stuck(h10, spine10) = &*stuck {
                                                    self.try_hit_rec(h10.clone(), spine10.clone())
                                                } else {
                                                    stuck
                                                }
                                            } else {
                                                stuck
                                            }
                                        } else {
                                            stuck
                                        }
                                    } else {
                                        stuck
                                    }
                                } else {
                                    stuck
                                }
                            } else {
                                stuck
                            }
                        } else {
                            stuck
                        }
                    } else {
                        stuck
                    }
                } else {
                    stuck
                }
            }
            // Applying a Sort/Pi is ill-typed; only reachable on ill-typed input.
            _ => f,
        }
    }

    fn apply(&self, clo: &Closure, a: Rc<Value>) -> Rc<Value> {
        self.eval(&clo.env.cons(a), &clo.body)
    }

    /// **The completeness fix**: a `venv`-aware regularity probe for [`Term::Transp`]
    /// (see [`Term::Transp`]'s arm in [`Self::eval`], which calls this instead of
    /// `crate::kan::family_is_constant`). Decides whether `fam` — a family under one
    /// (not-yet-introduced) interval binder, living in the *current* evaluation
    /// context `venv` — is constant in that binder, i.e. whether the enclosing
    /// `Transp`'s regularity rule may fire.
    ///
    /// # The gap this closes
    ///
    /// `crate::kan::family_is_constant` (still used, unchanged, by
    /// [`crate::reduce::Reducer::whnf`] — see below for why that call site doesn't
    /// need this fix) decides constancy by calling `Nbe::normalize_open`, which
    /// evaluates `fam` against a **brand-new, from-scratch** environment: the
    /// interval binder *and every other free variable `fam` mentions* each get a
    /// fresh, mutually-unrelated opaque neutral. That throws away exactly the
    /// information this evaluator's *lazy, closure-based* [`Self::eval`] already has
    /// sitting in `venv`: when `eval` reaches a `Term::Transp` node nested inside a
    /// larger computation (e.g. one `J`/`transp` built as the base case of an
    /// *outer* `J`'s own motive — precisely the shape `crate::cubical::
    /// trans_right_unit`/`trans_inv_right`/`trans_inv_left` build, and the shape
    /// `crate::cubical::trans3`'s "nesting `trans`" obstruction hits), the family's
    /// *other* free variables are not "any old value" — they are already bound, by
    /// `venv`, to concrete values threaded down from the enclosing `J`/`transp`
    /// (e.g. a variable whose value is definitionally `refl a`, or `p @ i0`). A
    /// family that only collapses to a constant *given those particular, already-
    /// substituted values* (not for arbitrary unrelated ones) was — before this fix —
    /// invisible to `family_is_constant`'s fresh-neutral probe, so the enclosing
    /// `Transp` stayed permanently stuck even though the surrounding, fully
    /// substituted computation was genuinely regular.
    ///
    /// This method fixes that by **reusing `venv` itself**: it extends the *real*
    /// environment with exactly one fresh marker for the interval binder being
    /// tested (nothing else is fabricated), evaluates `fam` under it with this same
    /// `self.eval`, and checks whether that one marker survives into the fully
    /// forced result.
    ///
    /// # Soundness
    ///
    /// This decides the *exact same proposition* `crate::kan::family_is_constant`
    /// already soundly decides ("does the family's fully computed value depend on
    /// its own interval binder") — see that function's doc for why that judgement is
    /// safe to trust (NbE normal forms are canonical, so "no occurrence of the fresh
    /// marker" means the family evaluates to the same result for *every* value the
    /// binder could take, in particular `i0` and `i1`, which is exactly the
    /// regularity rule's precondition). The only change is *which* environment the
    /// probe runs in: the family's other free variables are resolved against their
    /// real, already-known values (`venv`) instead of independently-fabricated fresh
    /// ones. Using the real values cannot manufacture a *new* fact — every value in
    /// `venv` already arose from a previously type-checked substitution — it only
    /// lets the *same* constant-family judgement see through substitutions that had
    /// already legitimately happened. In particular this cannot equate two distinct
    /// closed canonical values: the probe only ever gates whether `Transp` collapses
    /// to its own `a`-argument, and `a`'s type (`family[i:=i0]`) was already checked
    /// against the `Transp`'s declared type by [`crate::check::Checker`] at the
    /// point this term was accepted — this evaluator changes no typing judgement,
    /// only which reductions the (already-sound) evaluator manages to perform.
    ///
    /// The freshness — and, critically, the **quote-safety** — of the marker
    /// itself now comes from reusing exactly [`Self::quote`]'s own,
    /// already-proven-sound discipline (see [`VEnv::depth`]'s doc): the probe
    /// is pushed as `Head::Var(venv.depth())`, i.e. a genuine, **position-
    /// indexed** de Bruijn *level* — the same level a real `cons`ed binder at
    /// that point in `venv` would occupy — not an out-of-band sentinel from a
    /// disjoint numbering scheme. Concretely this means: (a) it is
    /// *indistinguishable*, as far as `eval`/`quote` are concerned, from an
    /// ordinary fresh bound variable introduced at this point (exactly what
    /// [`Self::quote`] itself pushes, e.g. in its `Value::Pi`/`Value::Lam`
    /// arms, every time it forces a closure body) — so nothing downstream
    /// needs to recognize or special-case it; (b) it round-trips through
    /// `quote(venv.depth() + 1, ..)` correctly by the same level-to-index
    /// arithmetic (`idx = level - 1 - k`) that already governs every other
    /// binding in `venv`, with **no risk of underflow or of colliding with a
    /// genuine bound variable's index** — the two things the old
    /// `PROBE_BASE`-offset out-of-band scheme could get wrong when this
    /// probe's marker was later dragged, unresolved, into a *nested* probe's
    /// own `quote` call (see [`Self::family_whnf_pi`]'s doc for the nested
    /// case this was blocking); and (c) it composes safely under nesting: a
    /// probe started while already nested inside another probe simply sees a
    /// `venv` one binding deeper (`depth` is always the literal, current
    /// `Cons`-chain length), so its own marker lands at the next level up,
    /// exactly like two ordinary nested binders would — there is no shared
    /// mutable counter to reason about, and no possibility of two *different*
    /// probes' markers being confused for one another (they occupy different,
    /// non-overlapping levels by construction, just like any other pair of
    /// nested bound variables).
    ///
    /// # Termination
    ///
    /// One `self.eval` call (the same total-on-well-typed-input evaluator every
    /// other `Transp`/`J` computation already relies on) plus one `self.quote` call
    /// over the result — no new recursion scheme, no looping: this performs exactly
    /// the work `crate::kan::family_is_constant`'s slow path already performed,
    /// against a differently-populated (but no larger) environment.
    ///
    /// # Why `crate::reduce::Reducer::whnf`'s call site is untouched
    ///
    /// `whnf` is a *substitution*-based reducer (plain `Term`, no closures/`venv`):
    /// by the time it reaches a `Term::Transp` node, every enclosing binder has
    /// already been eliminated by literal substitution (`instantiate`/`subst`), so
    /// `fam`'s free variables (besides the interval binder itself) are already
    /// baked into its syntax — there is no separate "hidden venv" for that call site
    /// to lose track of, and `crate::kan::family_is_constant`'s from-scratch probe
    /// is already working against the fully-substituted term.
    fn family_is_constant_value(&self, venv: &Rc<VEnv>, fam: &Term) -> bool {
        // Fast path, mirroring `crate::kan::family_is_constant`'s own: skip the
        // (cheap, but not free) probe entirely when the family's raw syntax doesn't
        // even mention its own binder.
        if !crate::term::mentions_var(fam, 0) {
            return true;
        }
        // Position-indexed marker (see this method's doc): the exact same
        // "push `Head::Var(depth)`, then quote at `depth + 1`" discipline
        // `Self::quote` itself already uses at every closure it forces —
        // never an out-of-band sentinel, so it is safe to nest.
        let level = venv.depth();
        let probe = Rc::new(Value::Stuck(Head::Var(level), Vec::new()));
        let v = self.eval(&venv.cons(probe), fam);
        // The probe (at level `level`) reads back as `Term::Var(0)` under
        // `quote(level + 1, ..)` — see `Self::quote`'s level-to-index
        // convention (`idx = level - 1 - k`) — so checking for `Var(0)` in
        // the quoted result is exactly checking whether the fresh marker
        // survived. Any *other* `Head::Var(k)` already present in `venv`
        // quotes back to a different (smaller) index, exactly as it would
        // for `Self::quote` itself, so it can't be mistaken for the probe.
        let quoted = self.quote(level + 1, &v);
        !crate::term::mentions_var(&quoted, 0)
    }

    /// **The completeness fix (nested-`trans`-as-`J`-subject gap)**: a `venv`-aware
    /// WHNF probe deciding whether `fam` — a family under one (not-yet-introduced)
    /// interval binder, exactly [`Term::Transp`]'s own `fam` field — computes,
    /// once genuinely evaluated against the *real* environment `venv`, to a `Π`
    /// type, even when `fam`'s own raw syntax is not literally a `Term::Pi` node
    /// (e.g. it's a beta-redex `App(App(motive, ..), ..)` that only *reduces* to
    /// one). On a hit, returns `(dom, cod)` in exactly the calling convention
    /// [`crate::kan::transp_pi_rule`] already expects from the syntactic-match call
    /// site right above it in [`Self::eval`]'s `Term::Transp` arm — i.e. both
    /// still living in the same "one interval binder" frame `fam` itself lives in
    /// (`dom` unchanged, `cod` one binder deeper) — so the two call sites can share
    /// that one, already-trusted Kan-filling builder verbatim.
    ///
    /// # The gap this closes
    ///
    /// [`Self::eval`]'s existing `Term::Transp` arm decides whether the Π-case
    /// filling rule applies by matching `fam.as_ref()` **syntactically** against
    /// `Term::Pi(..)` — no reduction first. That is exactly right for a *directly*
    /// Π-headed family (the overwhelmingly common case, and the one every existing
    /// `transp_pi_rule` test exercises), but it misses a family that is only a `Π`
    /// *up to computation* — concretely, `crate::cubical::j`'s own `family` field,
    /// built as `App(App(motive, p_at_i), connect)` (`motive` a literal two-`Lam`
    /// term whose body, once both arguments are substituted in, beta-reduces to a
    /// `Π`/arrow type). Every `J`-derived combinator (`crate::cubical::trans`
    /// included) builds its `Transp` this way, so this gap is latent in *all* of
    /// them — it stays invisible only because a single top-level `Transp` node is
    /// usually consumed by `is_def_eq`'s full `normalize_open`, which reaches the
    /// same Π shape via ordinary β-reduction *around* the (still literally stuck)
    /// `Value::Transp`, without ever needing this arm to fire. It stops being
    /// invisible exactly when a `Transp`-headed term's *value* — not just its type
    /// — is needed to drive a *further* computation, e.g. `crate::cubical::trans`'s
    /// own output (`App(Transp(..), q)`, a path) used as the *subject* `p` of an
    /// *outer* `J`/`trans` call (`crate::cubical::trans3`'s documented "nesting
    /// `trans`" obstruction, `equiv_hae::tests::
    /// debug_nested_trans_hits_the_documented_completeness_gap`): the outer `J`'s
    /// own `family_is_constant_value` regularity probe (and the boundary check in
    /// `Checker::check`'s `Term::Transp` arm) need the *inner* `Transp` to actually
    /// reduce — via this very Π-case rule — so that e.g. `pq @ i0` genuinely
    /// computes down to `pq`'s known left endpoint `w`. Without this fix the inner
    /// `Transp` stays permanently `Value::Stuck`-adjacent (wrapped in `Value::Transp`,
    /// never unfolding to the `Lam` the Π-rule would have built), so `pq @ i0`
    /// normalizes only as far as the *symbolic* application `(Transp(..) q) @ i0`
    /// — never reaching `w` — exactly the "expected"/"inferred" mismatch the
    /// diagnostic test records (`pq @ (#0 ∧ i0)` staying stuck instead of folding
    /// to `w`).
    ///
    /// This method closes that gap the same way [`Self::family_is_constant_value`]
    /// closed the sibling regularity gap: by asking the question against the
    /// **real** `venv` (with real values for every free variable `fam` mentions
    /// besides its own interval binder) instead of `fam`'s undecorated syntax.
    ///
    /// # Soundness
    ///
    /// Introduces **no new reduction rule and no new equation**. The only thing
    /// that fires here is [`crate::kan::transp_pi_rule`] — the exact same,
    /// pre-existing, independently soundness-argued Kan-filling construction the
    /// syntactic branch already calls (see that function's own doc and
    /// `crate::kan`'s "Phase 3.6" section) — applied to a `(dom, cod)` pair that is
    /// *provably* what `fam` denotes: `v = eval(venv.cons(probe), fam)` is the
    /// evaluator's own, already-trusted judgement of what `fam` computes to, and
    /// `quote` is its exact, sound left-inverse (re-reading a value back to a
    /// normal-form term valid in the same context) — so `(dom, cod)` are not a
    /// guess or an approximation, they are `fam`'s *actual* dom/cod once the
    /// probe's own level-bookkeeping (see below) is right. This is a strictly
    /// **completeness**-only extension of an already-sound rule to a syntactically
    /// larger, semantically identical set of `fam` shapes — it changes which
    /// `Transp` nodes *reduce*, never which *types* something is accepted at
    /// (`Checker::infer`/`check` are untouched by this module).
    ///
    /// # Why the probe must use the *real* depth
    ///
    /// The `(dom, cod)` this method returns get handed to
    /// [`crate::kan::transp_pi_rule`] and then *re-evaluated against this same
    /// `venv`* by the caller, so every *other* free variable `fam` mentions (i.e.
    /// every `Head::Var(k)` already present in `venv`, not the freshly pushed
    /// marker) must quote back to the **same** `Term::Var` index that correctly
    /// re-resolves through `venv.get` — which only holds when the quoting level
    /// matches `venv`'s *actual* depth (see [`VEnv::depth`]'s doc). An
    /// out-of-band, non-position-indexed level here would silently produce
    /// `(dom, cod)` with wildly wrong, out-of-range de Bruijn indices for every
    /// variable already bound in `venv` — not a soundness hole (the re-`eval`
    /// would simply panic on the out-of-range index, or in the worst case pick
    /// up an unrelated binding, on genuinely well-typed input), but a completeness
    /// bug (spurious failures/panics on well-typed terms) — so this method's
    /// `venv.depth()`-based quoting is the *only* correct freshness discipline
    /// here. [`Self::family_is_constant_value`] now shares this exact discipline
    /// too (see its doc) — the two probes are no longer allowed to diverge on
    /// this point, which is precisely what makes nesting them safe (next section).
    ///
    /// # Safe to fire nested inside `family_is_constant_value` (no bail-out needed)
    ///
    /// This used to bail out (return `None`) whenever `venv` already carried
    /// a marker pushed by an enclosing [`Self::family_is_constant_value`]
    /// probe, because that probe's *old* out-of-band `PROBE_BASE`-offset
    /// marker was **not** position-indexed — quoting a value that still
    /// mentioned it at this method's `venv.depth()`-based level could
    /// underflow `quote`'s `level - 1 - k` arithmetic, or produce a bogus
    /// small `Term::Var` index that collides with a genuinely bound variable
    /// (variable capture). [`Self::family_is_constant_value`] now pushes the
    /// *same* position-indexed `Head::Var(venv.depth())` marker this method
    /// does (see its doc), so every binding anywhere in `venv` — including
    /// one contributed by an enclosing `family_is_constant_value` probe — is
    /// now a genuine, position-indexed value that `quote` round-trips
    /// correctly, by construction, exactly as it does for any other bound
    /// variable. There is therefore nothing left to guard against: this
    /// method's own `venv.depth()`/`quote(level + 1, ..)` pair is sound
    /// regardless of what pushed the other bindings in `venv`, so it can
    /// (and, for `trans_assoc`'s base case, must) fire nested inside another
    /// probe's own recursive evaluation — see
    /// `crate::nbe::completeness_fix_soundness_tests::
    /// nested_probe_marker_quoting_does_not_capture_or_panic` for the direct
    /// adversarial exercise of exactly this nested shape.
    ///
    /// # Termination
    ///
    /// One `self.eval` call plus one `self.quote` call over the result — the exact
    /// same shape (and cost) as [`Self::family_is_constant_value`]'s own probe,
    /// against a `venv` no larger than the enclosing computation's. No new
    /// recursion scheme — and no risk of the removed guard silently masking
    /// non-termination either: this method never recurses into itself except
    /// via the same total `self.eval`/`self.quote` pair every other call site
    /// already relies on.
    fn family_whnf_pi(&self, venv: &Rc<VEnv>, fam: &Term) -> Option<(Term, Term)> {
        let level = venv.depth();
        let probe = Rc::new(Value::Stuck(Head::Var(level), Vec::new()));
        let v = self.eval(&venv.cons(probe), fam);
        if let Value::Pi(..) = &*v {
            if let Term::Pi(_g, dom, cod) = self.quote(level + 1, &v) {
                return Some(((*dom).clone(), (*cod).clone()));
            }
        }
        None
    }

    /// If `h spine` is a recursor saturated on a constructor major premise, fire its
    /// computation rule; otherwise leave it stuck.
    fn try_iota(&self, h: Head, spine: Vec<Rc<Value>>) -> Rc<Value> {
        if let Head::Const(rname, ls) = &h {
            if let Some(Decl::Recursor(rec)) = self.env.get(rname) {
                let mp = rec.major_pos();
                if spine.len() > mp {
                    if let Value::Stuck(Head::Const(ctor, _), cargs) = &*spine[mp] {
                        if let Some(rule) = rec.rules.get(ctor) {
                            let is_ctor = matches!(
                                self.env.get(ctor),
                                Some(Decl::Constructor(c)) if c.ind == rec.ind
                            );
                            if is_ctor {
                                let np = rec.num_params;
                                let nh = np + rec.num_motives;
                                // [params…, motives…] then the minors.
                                let params_and_motives = &spine[0..nh];
                                let minors = &spine[nh..nh + rec.num_minors];
                                let fields = &cargs[np..];
                                let extra = &spine[mp + 1..];
                                let mut v = if ls.is_empty() {
                                    self.eval(&Rc::new(VEnv::Nil), &rule.rhs)
                                } else {
                                    self.eval(&Rc::new(VEnv::Nil), &rule.rhs.instantiate_levels(ls))
                                };
                                for arg in params_and_motives
                                    .iter()
                                    .chain(minors)
                                    .chain(fields)
                                    .chain(extra)
                                {
                                    v = self.vapp(v, arg.clone());
                                }
                                return v;
                            }
                        }
                    }
                }
            }
        }
        Rc::new(Value::Stuck(h, spine))
    }

    /// If `h spine` is a **destructor** observing a saturated **corecursor** application,
    /// fire its ν-rule (one observation forces one layer); otherwise leave it stuck. This
    /// is the exact dual of [`try_iota`]: the scrutinee is at position `num_params +
    /// num_indices` of the destructor spine, and must be a stuck corecursor of the
    /// matching coinductive. For a corecursive destructor, the new indices are computed
    /// by evaluating the destructor's declared index-transform (a [`Term`], stored at
    /// declaration time) under a value environment built from the corecursor's current
    /// `[params, indices]` arguments — mirroring [`crate::reduce::Reducer::try_nu`]
    /// exactly (differentially cross-checked by the coinductive module's tests).
    fn try_nu(&self, h: Head, spine: Vec<Rc<Value>>) -> Rc<Value> {
        if let Head::Const(dname, _) = &h {
            if let Some(Decl::Destructor(dtor)) = self.env.get(dname) {
                if let Some(Decl::Coinductive(coind)) = self.env.get(&dtor.coind) {
                    let scrut_pos = coind.num_params + coind.num_indices;
                    if spine.len() > scrut_pos {
                        if let Value::Stuck(Head::Const(cname, cls), cargs) = &*spine[scrut_pos] {
                            if let Some(Decl::Corecursor(corec)) = self.env.get(cname) {
                                if corec.coind == dtor.coind && cargs.len() >= corec.arity() {
                                    if let Some(rule) = corec.rules.get(dname) {
                                        let step = cargs[rule.step_index].clone();
                                        let cur_indices =
                                            &cargs[corec.index_pos()..corec.index_pos() + corec.num_indices];
                                        let seed = cargs[corec.seed_pos()].clone();
                                        // observed field = step cur_indices… seed
                                        let mut observed = step;
                                        for idx in cur_indices {
                                            observed = self.vapp(observed, idx.clone());
                                        }
                                        observed = self.vapp(observed, seed);
                                        let mut v = if rule.corecursive {
                                            // Evaluate the index-transform terms under a
                                            // venv built from the current params ++
                                            // indices (in that order — matches the
                                            // transform's own `[params, indices]`
                                            // context, innermost/last index at Var(0)).
                                            let mut venv = Rc::new(VEnv::Nil);
                                            for a in cargs[..corec.num_params].iter().chain(cur_indices) {
                                                venv = venv.cons(a.clone());
                                            }
                                            let new_indices: Vec<Rc<Value>> = rule
                                                .index_transform
                                                .iter()
                                                .map(|t| self.eval(&venv, t))
                                                .collect();
                                            // Re-wrap the corecursor around the new
                                            // indices and the new seed.
                                            let mut new_args = cargs[..corec.arity()].to_vec();
                                            new_args[corec.seed_pos()] = observed;
                                            for (i, ni) in new_indices.into_iter().enumerate() {
                                                new_args[corec.index_pos() + i] = ni;
                                            }
                                            Rc::new(Value::Stuck(
                                                Head::Const(cname.clone(), cls.clone()),
                                                new_args,
                                            ))
                                        } else {
                                            observed
                                        };
                                        // re-attach over-application beyond the scrutinee
                                        for extra in &spine[scrut_pos + 1..] {
                                            v = self.vapp(v, extra.clone());
                                        }
                                        return v;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        Rc::new(Value::Stuck(h, spine))
    }

    /// If `h spine` is `Quot.lift` saturated on a `Quot.mk` scrutinee, fire the single
    /// quotient computation rule `Quot.lift … f resp (Quot.mk … a) ↦ f a`; otherwise
    /// leave it stuck. The exact dual of [`try_iota`]/[`try_nu`] for the fixed
    /// `Quot.lift` constant: `f` is at spine index 3, the scrutinee `q` at index 5, and
    /// the representative `a` is the last argument of the `Quot.mk` spine `[A, R, a]`.
    /// Also drives the **dependent** recursor `Quot.rec` (same spine positions as
    /// `Quot.lift` — see `crate::reduce::Reducer::try_quot_lift`'s doc comment).
    fn try_quot_lift(&self, h: Head, spine: Vec<Rc<Value>>) -> Rc<Value> {
        const F_POS: usize = 3;
        const SCRUT_POS: usize = 5;
        if let Head::Const(lname, _) = &h {
            if matches!(self.env.get(lname), Some(Decl::Quot(q)) if q.role == QuotRole::Lift || q.role == QuotRole::Rec)
                && spine.len() > SCRUT_POS
            {
                if let Value::Stuck(Head::Const(mkn, _), margs) = &*spine[SCRUT_POS] {
                    if matches!(self.env.get(mkn), Some(Decl::Quot(q)) if q.role == QuotRole::Mk)
                        && margs.len() == 3
                    {
                        let a = margs[2].clone();
                        let f = spine[F_POS].clone();
                        let mut v = self.vapp(f, a);
                        for extra in &spine[SCRUT_POS + 1..] {
                            v = self.vapp(v, extra.clone());
                        }
                        return v;
                    }
                }
            }
        }
        Rc::new(Value::Stuck(h, spine))
    }

    /// If `h spine` is `Trunc.lift` saturated on a `Trunc.tr` scrutinee, fire the single
    /// truncation computation rule `Trunc.lift … f resp (Trunc.tr … a) ↦ f a`; otherwise
    /// leave it stuck. Mirrors [`try_quot_lift`] for the fixed `Trunc.lift` constant: `f`
    /// is at spine index 2, the scrutinee `t` at index 4, and the representative `a` is
    /// the last argument of the `Trunc.tr` spine `[A, a]`. It never fires on the path
    /// constructor `Trunc.eq`.
    fn try_trunc_lift(&self, h: Head, spine: Vec<Rc<Value>>) -> Rc<Value> {
        const F_POS: usize = 2;
        const SCRUT_POS: usize = 4;
        if let Head::Const(lname, _) = &h {
            if matches!(self.env.get(lname), Some(Decl::Trunc(t)) if t.role == TruncRole::Lift)
                && spine.len() > SCRUT_POS
            {
                if let Value::Stuck(Head::Const(trn, _), targs) = &*spine[SCRUT_POS] {
                    if matches!(self.env.get(trn), Some(Decl::Trunc(t)) if t.role == TruncRole::Tr)
                        && targs.len() == 2
                    {
                        let a = targs[1].clone();
                        let f = spine[F_POS].clone();
                        let mut v = self.vapp(f, a);
                        for extra in &spine[SCRUT_POS + 1..] {
                            v = self.vapp(v, extra.clone());
                        }
                        return v;
                    }
                }
            }
        }
        Rc::new(Value::Stuck(h, spine))
    }

    /// If `h spine` is `Trunc.rec` saturated on a `Trunc.tr` scrutinee, fire the single
    /// dependent truncation computation rule
    /// `Trunc.rec … isProp f (Trunc.tr … a) ↦ f a`; otherwise leave it stuck. Mirrors
    /// [`Self::try_trunc_lift`]: `f` is at spine index 3 (one slot later than
    /// `Trunc.lift`'s `f`, since `C`/`isProp` occupy the slots `P`/`resp` did), the
    /// scrutinee `t` at index 4, and the representative `a` is the last argument of the
    /// `Trunc.tr` spine `[A, a]`. It never fires on the path constructor `Trunc.eq`.
    fn try_trunc_rec(&self, h: Head, spine: Vec<Rc<Value>>) -> Rc<Value> {
        const F_POS: usize = 3;
        const SCRUT_POS: usize = 4;
        if let Head::Const(lname, _) = &h {
            if matches!(self.env.get(lname), Some(Decl::Trunc(t)) if t.role == TruncRole::Rec)
                && spine.len() > SCRUT_POS
            {
                if let Value::Stuck(Head::Const(trn, _), targs) = &*spine[SCRUT_POS] {
                    if matches!(self.env.get(trn), Some(Decl::Trunc(t)) if t.role == TruncRole::Tr)
                        && targs.len() == 2
                    {
                        let a = targs[1].clone();
                        let f = spine[F_POS].clone();
                        let mut v = self.vapp(f, a);
                        for extra in &spine[SCRUT_POS + 1..] {
                            v = self.vapp(v, extra.clone());
                        }
                        return v;
                    }
                }
            }
        }
        Rc::new(Value::Stuck(h, spine))
    }

    /// If `h spine` is `S¹.rec` saturated on an `S¹.base` scrutinee, fire the single
    /// circle computation rule `S¹.rec P pt lp S¹.base ↦ pt`; otherwise leave it stuck.
    /// Mirrors [`Self::try_trunc_lift`] for the fixed `S¹.rec` constant: `pt` is at spine
    /// index 1, the scrutinee `t` at index 3, and `S¹.base` is nullary (empty spine). It
    /// never fires on the path constructor `S¹.loop`.
    fn try_circle_rec(&self, h: Head, spine: Vec<Rc<Value>>) -> Rc<Value> {
        const PT_POS: usize = 1;
        const SCRUT_POS: usize = 3;
        if let Head::Const(rname, _) = &h {
            if matches!(self.env.get(rname), Some(Decl::Circle(c)) if c.role == CircleRole::Rec)
                && spine.len() > SCRUT_POS
            {
                if let Value::Stuck(Head::Const(basen, _), bargs) = &*spine[SCRUT_POS] {
                    if matches!(self.env.get(basen), Some(Decl::Circle(c)) if c.role == CircleRole::Base)
                        && bargs.is_empty()
                    {
                        let pt = spine[PT_POS].clone();
                        let mut v = pt;
                        for extra in &spine[SCRUT_POS + 1..] {
                            v = self.vapp(v, extra.clone());
                        }
                        return v;
                    }
                }
            }
        }
        Rc::new(Value::Stuck(h, spine))
    }

    /// The interval-HIT (`I2`) computation rules, NbE counterpart of
    /// [`crate::reduce::Reducer::try_i2_rec`] (see [`crate::interval_hit`]). Three
    /// ι-rules for the fixed, **computing** `I2.rec.{v} C c0 c1 s x` (spine: `C`@0,
    /// `c0`@1, `c1`@2, `s`@3, scrutinee `x`@4):
    ///
    /// ```text
    ///   I2.rec C c0 c1 s I2.zero        ↦  c0
    ///   I2.rec C c0 c1 s I2.one         ↦  c1
    ///   I2.rec C c0 c1 s (I2.seg @ r)   ↦  s @ r
    /// ```
    ///
    /// The point rules mirror [`Self::try_circle_rec`] exactly (doubled for two point
    /// constructors). The path rule fires only when the scrutinee value is a
    /// [`Value::Stuck`] with head [`Head::PathApp`]`(p, r)` whose own `p` is,
    /// recursively, `Value::Stuck(Head::Const(seg, _), [])` for the literal `I2.seg`
    /// constant — i.e. the scrutinee is exactly `I2.seg @ r`, matching
    /// [`crate::reduce::Reducer::try_i2_rec`]'s structural test on `Term::PApp`.
    fn try_i2_rec(&self, h: Head, spine: Vec<Rc<Value>>) -> Rc<Value> {
        const C0_POS: usize = 1;
        const C1_POS: usize = 2;
        const S_POS: usize = 3;
        const SCRUT_POS: usize = 4;
        if let Head::Const(rname, _) = &h {
            if matches!(self.env.get(rname), Some(Decl::I2(c)) if c.role == I2Role::Rec)
                && spine.len() > SCRUT_POS
            {
                match &*spine[SCRUT_POS] {
                    Value::Stuck(Head::Const(ptn, _), pargs) if pargs.is_empty() => {
                        let role = match self.env.get(ptn) {
                            Some(Decl::I2(c)) => Some(c.role),
                            _ => None,
                        };
                        let pos = match role {
                            Some(I2Role::Zero) => Some(C0_POS),
                            Some(I2Role::One) => Some(C1_POS),
                            _ => None,
                        };
                        if let Some(pos) = pos {
                            let mut v = spine[pos].clone();
                            for extra in &spine[SCRUT_POS + 1..] {
                                v = self.vapp(v, extra.clone());
                            }
                            return v;
                        }
                    }
                    Value::Stuck(Head::PathApp(p, r), pargs) if pargs.is_empty() => {
                        if let Value::Stuck(Head::Const(segn, _), segargs) = &**p {
                            if matches!(self.env.get(segn), Some(Decl::I2(c)) if c.role == I2Role::Seg)
                                && segargs.is_empty()
                            {
                                let s = spine[S_POS].clone();
                                let mut v = self.vpapp(s, r.clone());
                                for extra in &spine[SCRUT_POS + 1..] {
                                    v = self.vapp(v, extra.clone());
                                }
                                return v;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        Rc::new(Value::Stuck(h, spine))
    }

    /// The cubical-circle (`S1c`) computation rules, NbE counterpart of
    /// [`crate::reduce::Reducer::try_s1c_rec`] (see [`crate::circle_cubical`]). Two
    /// ι-rules for the fixed, **computing** `S1c.rec.{v} C b l x` (spine: `C`@0,
    /// `b`@1, `l`@2, scrutinee `x`@3):
    ///
    /// ```text
    ///   S1c.rec C b l S1c.base        ↦  b
    ///   S1c.rec C b l (S1c.loop @ r)  ↦  l @ r
    /// ```
    ///
    /// Structurally identical to [`Self::try_i2_rec`] (one point constructor, one
    /// path constructor whose `PApp` head must be the literal, nullary `S1c.loop`).
    fn try_s1c_rec(&self, h: Head, spine: Vec<Rc<Value>>) -> Rc<Value> {
        const B_POS: usize = 1;
        const L_POS: usize = 2;
        const SCRUT_POS: usize = 3;
        if let Head::Const(rname, _) = &h {
            if matches!(self.env.get(rname), Some(Decl::S1c(c)) if c.role == S1cRole::Rec)
                && spine.len() > SCRUT_POS
            {
                match &*spine[SCRUT_POS] {
                    Value::Stuck(Head::Const(ptn, _), pargs) if pargs.is_empty() => {
                        if matches!(self.env.get(ptn), Some(Decl::S1c(c)) if c.role == S1cRole::Base)
                        {
                            let mut v = spine[B_POS].clone();
                            for extra in &spine[SCRUT_POS + 1..] {
                                v = self.vapp(v, extra.clone());
                            }
                            return v;
                        }
                    }
                    Value::Stuck(Head::PathApp(p, r), pargs) if pargs.is_empty() => {
                        if let Value::Stuck(Head::Const(loopn, _), loopargs) = &**p {
                            if matches!(self.env.get(loopn), Some(Decl::S1c(c)) if c.role == S1cRole::Loop)
                                && loopargs.is_empty()
                            {
                                let l = spine[L_POS].clone();
                                let mut v = self.vpapp(l, r.clone());
                                for extra in &spine[SCRUT_POS + 1..] {
                                    v = self.vapp(v, extra.clone());
                                }
                                return v;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        Rc::new(Value::Stuck(h, spine))
    }

    /// The **general, user-declared cubical HIT** computation rule (see
    /// [`crate::cubical_hit`]), NbE counterpart of
    /// [`crate::reduce::Reducer::try_cubical_hit_rec`]. Generalizes
    /// [`Self::try_i2_rec`]/[`Self::try_s1c_rec`] over `num_points`/`num_paths`,
    /// guarded per-HIT `id` (see that method's doc comment for the exact rule and
    /// the cross-fire guard).
    fn try_cubical_hit_rec(&self, h: Head, spine: Vec<Rc<Value>>) -> Rc<Value> {
        if let Head::Const(rname, ls) = &h {
            if let Some(Decl::CubHit(rc)) = self.env.get(rname) {
                if let CubHitRole::Rec { num_points, num_paths, num_surfaces, num_cubes, num_hypers } = rc.role {
                    let (num_points, num_paths, num_surfaces, num_cubes, num_hypers) = (
                        num_points as usize,
                        num_paths as usize,
                        num_surfaces as usize,
                        num_cubes as usize,
                        num_hypers as usize,
                    );
                    let scrut_pos = 1 + num_points + num_paths + num_surfaces + num_cubes + num_hypers;
                    if spine.len() > scrut_pos {
                        match &*spine[scrut_pos] {
                            // Point rule: fully applied to its declared fields
                            // (arity match), same HIT `id` — mirrors
                            // `try_hit_rec`'s fielded/recursive substitution.
                            Value::Stuck(Head::Const(ptn, _), pargs) => {
                                if let Some(Decl::CubHit(c)) = self.env.get(ptn) {
                                    if c.id == rc.id {
                                        if let CubHitRole::Point { idx, fields } = &c.role {
                                            if pargs.len() == fields.len() {
                                                let pos = 1 + *idx as usize;
                                                let mut v = spine[pos].clone();
                                                for (a, is_rec) in pargs.iter().zip(fields.iter()) {
                                                    // Keep the original field
                                                    // value (dependent case; see
                                                    // `point_case_ty`'s doc
                                                    // comment), then, for a
                                                    // recursive field, follow it
                                                    // with its IH.
                                                    v = self.vapp(v, a.clone());
                                                    if *is_rec {
                                                        let mut recur = Rc::new(Value::Stuck(
                                                            Head::Const(rname.clone(), ls.clone()),
                                                            Vec::new(),
                                                        ));
                                                        for pre in &spine[..scrut_pos] {
                                                            recur = self.vapp(recur, pre.clone());
                                                        }
                                                        let ih = self.vapp(recur, a.clone());
                                                        v = self.vapp(v, ih);
                                                    }
                                                }
                                                for extra in &spine[scrut_pos + 1..] {
                                                    v = self.vapp(v, extra.clone());
                                                }
                                                return v;
                                            }
                                        }
                                    }
                                }
                            }
                            // Path rule (1-path) AND Surface rule (2-path, "S²") —
                            // both scrutinees weak-head as `PathApp`, so they share
                            // one arm and are disambiguated by whether `p` (the
                            // thing being `@`-applied to `r`) is itself, in turn,
                            // ANOTHER `PathApp` (surface: `(H.surf_k @ ri) @ rj`) or
                            // directly a `Const` (ordinary path: `H.path_j .. @ r`).
                            // The surface check is tried FIRST — mirrors
                            // [`crate::reduce::Reducer::try_cubical_hit_rec`]'s
                            // equivalent structural disjointness argument (see that
                            // function's doc comment).
                            Value::Stuck(Head::PathApp(p, r), pargs) if pargs.is_empty() => {
                                if let Value::Stuck(Head::PathApp(p_inner, ri), iargs) = &**p {
                                    if iargs.is_empty() {
                                        if let Value::Stuck(Head::Const(surf_name, _), sargs) = &**p_inner {
                                            if sargs.is_empty() {
                                                if let Some(Decl::CubHit(c)) = self.env.get(surf_name) {
                                                    if c.id == rc.id {
                                                        if let CubHitRole::Surf { idx, .. } = &c.role {
                                                            let pos =
                                                                1 + num_points + num_paths + *idx as usize;
                                                            let t = spine[pos].clone();
                                                            let t_i = self.vpapp(t, ri.clone());
                                                            let mut v = self.vpapp(t_i, r.clone());
                                                            for extra in &spine[scrut_pos + 1..] {
                                                                v = self.vapp(v, extra.clone());
                                                            }
                                                            return v;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        // Cube rule (3-path / "S³"): `p_inner` itself is
                                        // ANOTHER `PathApp` (`(H.cube_l @ ri') @ rj`), so
                                        // the surface check above (which requires
                                        // `p_inner` to be a bare `Const`) silently fails
                                        // to match and falls through to here — mirrors
                                        // [`crate::reduce::Reducer::try_cubical_hit_rec`]'s
                                        // equivalent structural disjointness argument one
                                        // level deeper (see that function's doc comment).
                                        if let Value::Stuck(Head::PathApp(p_inner2, ri2), iargs2) = &**p_inner {
                                            if iargs2.is_empty() {
                                                if let Value::Stuck(Head::Const(cube_name, _), cargs) = &**p_inner2 {
                                                    if cargs.is_empty() {
                                                        if let Some(Decl::CubHit(c)) = self.env.get(cube_name) {
                                                            if c.id == rc.id {
                                                                if let CubHitRole::Cube { idx, .. } = &c.role {
                                                                    let pos = 1
                                                                        + num_points
                                                                        + num_paths
                                                                        + num_surfaces
                                                                        + *idx as usize;
                                                                    let u = spine[pos].clone();
                                                                    let u_i = self.vpapp(u, ri2.clone());
                                                                    let u_ij = self.vpapp(u_i, ri.clone());
                                                                    let mut v = self.vpapp(u_ij, r.clone());
                                                                    for extra in &spine[scrut_pos + 1..] {
                                                                        v = self.vapp(v, extra.clone());
                                                                    }
                                                                    return v;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                                // Hyper rule (4-path / "S⁴"): `p_inner2`
                                                // itself is ANOTHER `PathApp`
                                                // (`(H.hyper_l @ ri3') @ ri2)`), so the
                                                // cube check above (which requires
                                                // `p_inner2` to be a bare `Const`) silently
                                                // fails to match and falls through to here
                                                // — mirrors
                                                // [`crate::reduce::Reducer::try_cubical_hit_rec`]'s
                                                // equivalent structural disjointness
                                                // argument one level deeper still (see that
                                                // function's doc comment).
                                                if let Value::Stuck(Head::PathApp(p_inner3, ri3), iargs3) =
                                                    &**p_inner2
                                                {
                                                    if iargs3.is_empty() {
                                                        if let Value::Stuck(Head::Const(hyper_name, _), hargs) =
                                                            &**p_inner3
                                                        {
                                                            if hargs.is_empty() {
                                                                if let Some(Decl::CubHit(c)) =
                                                                    self.env.get(hyper_name)
                                                                {
                                                                    if c.id == rc.id {
                                                                        if let CubHitRole::Hyper { idx, .. } =
                                                                            &c.role
                                                                        {
                                                                            let pos = 1
                                                                                + num_points
                                                                                + num_paths
                                                                                + num_surfaces
                                                                                + num_cubes
                                                                                + *idx as usize;
                                                                            let w = spine[pos].clone();
                                                                            let w_i =
                                                                                self.vpapp(w, ri3.clone());
                                                                            let w_ij =
                                                                                self.vpapp(w_i, ri2.clone());
                                                                            let w_ijk =
                                                                                self.vpapp(w_ij, ri.clone());
                                                                            let mut v =
                                                                                self.vpapp(w_ijk, r.clone());
                                                                            for extra in
                                                                                &spine[scrut_pos + 1..]
                                                                            {
                                                                                v = self.vapp(v, extra.clone());
                                                                            }
                                                                            return v;
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                if let Value::Stuck(Head::Const(pathn, _), pathargs) = &**p {
                                    if let Some(Decl::CubHit(c)) = self.env.get(pathn) {
                                        if c.id == rc.id {
                                            if let CubHitRole::Path { idx, num_quant, .. } = &c.role {
                                                if pathargs.len() == *num_quant as usize {
                                                    let pos = 1 + num_points + *idx as usize;
                                                    let mut s = spine[pos].clone();
                                                    for q in pathargs {
                                                        s = self.vapp(s, q.clone());
                                                    }
                                                    let mut v = self.vpapp(s, r.clone());
                                                    for extra in &spine[scrut_pos + 1..] {
                                                        v = self.vapp(v, extra.clone());
                                                    }
                                                    return v;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        Rc::new(Value::Stuck(h, spine))
    }

    /// User-declared 1-HIT computation rule (see [`crate::hit`]), NbE counterpart of
    /// [`crate::reduce::Reducer::try_hit_rec`]: for `H.rec.{v} P case_0 .. resp_.. t`,
    /// fires when `t` is stuck on the `i`-th point constructor of the *same* HIT `id`
    /// as the `H.rec` head, fully applied to its declared fields — substituting a
    /// recursive `H.rec` call for each field of type `H` itself (see the reducer's
    /// doc comment for the exact rule); otherwise stays stuck. Never fires across two
    /// different declared HITs (guarded by comparing `id`s) or on a path constructor.
    fn try_hit_rec(&self, h: Head, spine: Vec<Rc<Value>>) -> Rc<Value> {
        if let Head::Const(rname, ls) = &h {
            if let Some(Decl::Hit(hh)) = self.env.get(rname) {
                if let HitRole::Rec { num_points, num_paths } = hh.role {
                    let scrut_pos = 1 + num_points as usize + num_paths as usize;
                    if spine.len() > scrut_pos {
                        if let Value::Stuck(Head::Const(pname, _), pargs) = &*spine[scrut_pos] {
                            if let Some(Decl::Hit(p)) = self.env.get(pname) {
                                if p.id == hh.id {
                                    if let HitRole::Point { index, fields } = &p.role {
                                        if pargs.len() == fields.len() {
                                            let case_pos = 1 + *index as usize;
                                            let mut v = spine[case_pos].clone();
                                            for (arg, is_rec) in pargs.iter().zip(fields.iter()) {
                                                let b = if *is_rec {
                                                    let mut rc = Rc::new(Value::Stuck(
                                                        Head::Const(rname.clone(), ls.clone()),
                                                        Vec::new(),
                                                    ));
                                                    for a in &spine[..scrut_pos] {
                                                        rc = self.vapp(rc, a.clone());
                                                    }
                                                    self.vapp(rc, arg.clone())
                                                } else {
                                                    arg.clone()
                                                };
                                                v = self.vapp(v, b);
                                            }
                                            for extra in &spine[scrut_pos + 1..] {
                                                v = self.vapp(v, extra.clone());
                                            }
                                            return v;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        Rc::new(Value::Stuck(h, spine))
    }

    /// Read a value back to a normal-form term, at binder depth `level`.
    pub fn quote(&self, level: usize, v: &Value) -> Term {
        match v {
            Value::Sort(l) => Term::Sort(l.clone()),
            Value::Pi(g, d, clo) => {
                let dom = self.quote(level, d);
                let body = self.apply(clo, Rc::new(Value::Stuck(Head::Var(level), Vec::new())));
                Term::pi_graded(*g, dom, self.quote(level + 1, &body))
            }
            Value::Lam(d, clo) => {
                let dom = self.quote(level, d);
                let body = self.apply(clo, Rc::new(Value::Stuck(Head::Var(level), Vec::new())));
                Term::lam(dom, self.quote(level + 1, &body))
            }
            Value::Stuck(h, spine) => {
                let mut t = match h {
                    // de Bruijn level → index at the current depth.
                    Head::Var(lvl) => Term::Var(level - 1 - lvl),
                    Head::Const(n, ls) => Term::cnst(n.clone(), ls.clone()),
                    Head::Meta(m) => Term::Meta(*m),
                    Head::PathApp(p, r) => Term::papp(self.quote(level, p), self.quote(level, r)),
                };
                for arg in spine {
                    t = Term::app(t, self.quote(level, arg));
                }
                t
            }
            Value::I => Term::I,
            Value::IZero => Term::IZero,
            Value::IOne => Term::IOne,
            Value::INeg(r) => Term::ineg(self.quote(level, r)),
            Value::IMeet(r, s) => Term::imeet(self.quote(level, r), self.quote(level, s)),
            Value::IJoin(r, s) => Term::ijoin(self.quote(level, r), self.quote(level, s)),
            Value::PLam(clo) => {
                let body = self.apply(clo, Rc::new(Value::Stuck(Head::Var(level), Vec::new())));
                Term::plam(self.quote(level + 1, &body))
            }
            Value::PathP(a0, a1, clo) => {
                let body = self.apply(clo, Rc::new(Value::Stuck(Head::Var(level), Vec::new())));
                Term::pathp(self.quote(level + 1, &body), self.quote(level, a0), self.quote(level, a1))
            }
            Value::Sys(sc) => {
                let qbranches = sc
                    .branches
                    .iter()
                    .map(|(phi, t)| {
                        let qphi = self.quote_cof(level, &sc.env, phi);
                        let qt = self.quote(level, &self.eval(&sc.env, t));
                        (Rc::new(qphi), Rc::new(qt))
                    })
                    .collect();
                Term::Sys(qbranches)
            }
            Value::Partial(a, fc) => {
                let qphi = self.quote_cof(level, &fc.env, &fc.phi);
                Term::Partial(Rc::new(qphi), Rc::new(self.quote(level, a)))
            }
            Value::Transp(tc, a) => {
                let qphi = self.quote_cof(level, &tc.env, &tc.phi);
                let famv = self.eval(&tc.env.cons(Rc::new(Value::Stuck(Head::Var(level), Vec::new()))), &tc.fam);
                let qfam = self.quote(level + 1, &famv);
                Term::transp(qfam, qphi, self.quote(level, a))
            }
            Value::HComp(hc, u0) => {
                let qty = self.quote(level, &hc.ty);
                let qphi = self.quote_cof(level, &hc.env, &hc.phi);
                let uv = self.eval(&hc.env.cons(Rc::new(Value::Stuck(Head::Var(level), Vec::new()))), &hc.u);
                let qu = self.quote(level + 1, &uv);
                Term::hcomp(qty, qphi, qu, self.quote(level, u0))
            }
            Value::Glue(a, gc) => {
                let branches = gc
                    .branches
                    .iter()
                    .map(|(p, t, e)| (self.quote_cof(level, &gc.env, p), self.quote(level, t), self.quote(level, e)))
                    .collect();
                Term::glue_ty_multi(self.quote(level, a), branches)
            }
            Value::Unglue(a, gc, u) => {
                let branches = gc
                    .branches
                    .iter()
                    .map(|(p, t, e)| (self.quote_cof(level, &gc.env, p), self.quote(level, t), self.quote(level, e)))
                    .collect();
                Term::unglue(self.quote(level, a), branches, self.quote(level, u))
            }
            Value::GlueIntro(gc, a) => {
                let branches = gc
                    .branches
                    .iter()
                    .map(|(p, t)| (Rc::new(self.quote_cof(level, &gc.env, p)), Rc::new(self.quote(level, t))))
                    .collect();
                Term::GlueIntro(Rc::new(branches), Rc::new(self.quote(level, a)))
            }
        }
    }

    /// Full normal form of a closed term.
    pub fn normalize(&self, t: &Term) -> Term {
        self.quote(0, &self.eval(&Rc::new(VEnv::Nil), t))
    }

    /// Full normal form of a term **open** in a context of `depth` binders. The
    /// context variables are evaluated to fresh neutrals (de Bruijn levels `0..depth`),
    /// so the result is a normal form valid in the same context.
    pub fn normalize_open(&self, depth: usize, t: &Term) -> Term {
        let mut venv = Rc::new(VEnv::Nil);
        for k in 0..depth {
            venv = venv.cons(Rc::new(Value::Stuck(Head::Var(k), Vec::new())));
        }
        self.quote(depth, &self.eval(&venv, t))
    }

    /// Conversion via NbE: normalize both and compare up to α, η, and grade-blindness.
    pub fn conv(&self, t1: &Term, t2: &Term) -> bool {
        alpha_eta_eq(&self.normalize(t1), &self.normalize(t2))
    }
}

/// Eager smart constructor for [`Term::INeg`]'s semantic value: `~i0 ↦ i1`, `~i1 ↦
/// i0`, `~~r ↦ r` (double-negation elimination — sound: `crate::cubical::
/// normalize_interval`'s own De Morgan normal form treats `~~r` and `r` identically),
/// otherwise stays wrapped as `Value::INeg`. See [`Value::INeg`]'s doc for the
/// soundness/termination argument (shared by this and its `imeet`/`ijoin` siblings).
fn veval_ineg(r: Rc<Value>) -> Rc<Value> {
    match &*r {
        Value::IZero => Rc::new(Value::IOne),
        Value::IOne => Rc::new(Value::IZero),
        Value::INeg(inner) => inner.clone(),
        _ => Rc::new(Value::INeg(r)),
    }
}

/// Eager smart constructor for [`Term::IMeet`]'s semantic value: the bounded-lattice
/// identity/absorption laws `i0 ∧ r ↦ i0`, `r ∧ i0 ↦ i0`, `i1 ∧ r ↦ r`, `r ∧ i1 ↦ r`;
/// otherwise stays wrapped as `Value::IMeet`. See [`Value::INeg`]'s doc.
fn veval_imeet(r: Rc<Value>, s: Rc<Value>) -> Rc<Value> {
    match (&*r, &*s) {
        (Value::IZero, _) | (_, Value::IZero) => Rc::new(Value::IZero),
        (Value::IOne, _) => s,
        (_, Value::IOne) => r,
        _ => Rc::new(Value::IMeet(r, s)),
    }
}

/// Eager smart constructor for [`Term::IJoin`]'s semantic value: the bounded-lattice
/// identity/absorption laws `i1 ∨ r ↦ i1`, `r ∨ i1 ↦ i1`, `i0 ∨ r ↦ r`, `r ∨ i0 ↦ r`;
/// otherwise stays wrapped as `Value::IJoin`. See [`Value::INeg`]'s doc.
fn veval_ijoin(r: Rc<Value>, s: Rc<Value>) -> Rc<Value> {
    match (&*r, &*s) {
        (Value::IOne, _) | (_, Value::IOne) => Rc::new(Value::IOne),
        (Value::IZero, _) => s,
        (_, Value::IZero) => r,
        _ => Rc::new(Value::IJoin(r, s)),
    }
}

/// Phase 3.5 (De Morgan interval, see `crate::cubical`): does `v` — a semantic
/// interval value, possibly built from `~`/`∧`/`∨` over literals and open
/// variables — evaluate to a *decided* endpoint? `Some(true)` = forced to `i1`,
/// `Some(false)` = forced to `i0`, `None` = still open (depends on an undecided
/// variable in a way the connective can't short-circuit). Total: strictly structural
/// recursion on `v`, which is already fully (weak-head, and for these constructors
/// eagerly) evaluated.
fn interval_endpoint(v: &Value) -> Option<bool> {
    match v {
        Value::IZero => Some(false),
        Value::IOne => Some(true),
        Value::INeg(r) => interval_endpoint(r).map(|b| !b),
        Value::IMeet(r, s) => match (interval_endpoint(r), interval_endpoint(s)) {
            (Some(false), _) | (_, Some(false)) => Some(false),
            (Some(true), Some(true)) => Some(true),
            _ => None,
        },
        Value::IJoin(r, s) => match (interval_endpoint(r), interval_endpoint(s)) {
            (Some(true), _) | (_, Some(true)) => Some(true),
            (Some(false), Some(false)) => Some(false),
            _ => None,
        },
        _ => None,
    }
}

/// Compare two normal-form terms up to α-equivalence, η, and grade-blindness on `Π`.
fn alpha_eta_eq(a: &Term, b: &Term) -> bool {
    match (a, b) {
        // Phase 3.5 (De Morgan interval, see `crate::cubical`): identical arm to
        // `check::Checker::compare`/`reduce::Reducer::is_def_eq` — kept in lockstep
        // across all three independent conversion checkers (differentially tested).
        // Only fires when a genuine connective head is present, so plain `Var`/`Var`
        // (needed for this normal-form comparator's η cases below) is untouched.
        (Term::INeg(..) | Term::IMeet(..) | Term::IJoin(..), _)
        | (_, Term::INeg(..) | Term::IMeet(..) | Term::IJoin(..))
            if crate::cubical::is_interval_expr(a) && crate::cubical::is_interval_expr(b) =>
        {
            crate::cubical::interval_eq(a, b)
        }
        (Term::Sort(l1), Term::Sort(l2)) => level::equiv(l1, l2),
        (Term::Var(i), Term::Var(j)) => i == j,
        (Term::Const(n1, l1), Term::Const(n2, l2)) => {
            n1 == n2 && l1.len() == l2.len() && l1.iter().zip(l2).all(|(x, y)| level::equiv(x, y))
        }
        (Term::App(f1, a1), Term::App(f2, a2)) => alpha_eta_eq(f1, f2) && alpha_eta_eq(a1, a2),
        (Term::Lam(d1, b1), Term::Lam(d2, b2)) => alpha_eta_eq(d1, d2) && alpha_eta_eq(b1, b2),
        (Term::Pi(_, d1, b1), Term::Pi(_, d2, b2)) => alpha_eta_eq(d1, d2) && alpha_eta_eq(b1, b2),
        // η: `λ. body ≡ f`  iff  `body ≡ f x`.
        (Term::Lam(_, body), _) => alpha_eta_eq(body, &Term::app(b.lift(1, 0), Term::Var(0))),
        (_, Term::Lam(_, body)) => alpha_eta_eq(&Term::app(a.lift(1, 0), Term::Var(0)), body),
        (Term::I, Term::I) | (Term::IZero, Term::IZero) | (Term::IOne, Term::IOne) => true,
        (Term::PLam(b1), Term::PLam(b2)) => alpha_eta_eq(b1, b2),
        // Path-η: `⟨i⟩ p @ i ≡ p`, the interval-binder analogue of the `Lam`-η
        // arms directly above — see `check::Checker::compare`'s matching arm for
        // the full soundness/termination argument (kept in lockstep here, as this
        // function's other cubical arms already are per the comment atop this
        // function). Purely syntactic and unconditional, exactly like `Lam`-η.
        (Term::PLam(body), _) => alpha_eta_eq(body, &Term::papp(b.lift(1, 0), Term::Var(0))),
        (_, Term::PLam(body)) => alpha_eta_eq(&Term::papp(a.lift(1, 0), Term::Var(0)), body),
        (Term::PApp(p1, r1), Term::PApp(p2, r2)) => alpha_eta_eq(p1, p2) && alpha_eta_eq(r1, r2),
        (Term::PathP(f1, a01, a11), Term::PathP(f2, a02, a12)) => {
            alpha_eta_eq(f1, f2) && alpha_eta_eq(a01, a02) && alpha_eta_eq(a11, a12)
        }
        (Term::Partial(p1, a1), Term::Partial(p2, a2)) => {
            crate::face::cof_equiv(p1, p2) && alpha_eta_eq(a1, a2)
        }
        (Term::Sys(b1), Term::Sys(b2)) => {
            b1.len() == b2.len()
                && b1.iter().zip(b2).all(|((p1, t1), (p2, t2))| {
                    crate::face::cof_equiv(p1, p2) && alpha_eta_eq(t1, t2)
                })
        }
        (Term::Transp(f1, p1, a1), Term::Transp(f2, p2, a2)) => {
            alpha_eta_eq(f1, f2) && crate::face::cof_equiv(p1, p2) && alpha_eta_eq(a1, a2)
        }
        (Term::HComp(t1, p1, u1, u01), Term::HComp(t2, p2, u2, u02)) => {
            alpha_eta_eq(t1, t2)
                && crate::face::cof_equiv(p1, p2)
                && alpha_eta_eq(u1, u2)
                && alpha_eta_eq(u01, u02)
        }
        (Term::Glue(a1, b1), Term::Glue(a2, b2)) => {
            alpha_eta_eq(a1, a2)
                && b1.len() == b2.len()
                && b1.iter().zip(b2.iter()).all(|((p1, t1, e1), (p2, t2, e2))| {
                    crate::face::cof_equiv(p1, p2) && alpha_eta_eq(t1, t2) && alpha_eta_eq(e1, e2)
                })
        }
        (Term::Unglue(a1, b1, u1), Term::Unglue(a2, b2, u2)) => {
            alpha_eta_eq(a1, a2)
                && b1.len() == b2.len()
                && b1.iter().zip(b2.iter()).all(|((p1, t1, e1), (p2, t2, e2))| {
                    crate::face::cof_equiv(p1, p2) && alpha_eta_eq(t1, t2) && alpha_eta_eq(e1, e2)
                })
                && alpha_eta_eq(u1, u2)
        }
        (Term::GlueIntro(b1, a1), Term::GlueIntro(b2, a2)) => {
            alpha_eta_eq(a1, a2)
                && b1.len() == b2.len()
                && b1.iter().zip(b2.iter()).all(|((p1, t1), (p2, t2))| {
                    crate::face::cof_equiv(p1, p2) && alpha_eta_eq(t1, t2)
                })
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::Checker;
    use crate::inductive::{declare_eq, declare_nat};
    use crate::kernel::Kernel;
    use crate::term::name;

    fn nat_kernel() -> Kernel {
        let mut k = Kernel::new();
        declare_nat(k.env_mut()).unwrap();
        declare_eq(k.env_mut()).unwrap();
        k.add_definition(
            "add",
            0,
            Term::pi(Term::cnst(name("Nat"), vec![]), Term::pi(Term::cnst(name("Nat"), vec![]), Term::cnst(name("Nat"), vec![]))),
            // add = λ m n. Nat.rec.{1} (λ_.Nat) n (λ p ih. succ ih) m
            {
                let nat = || Term::cnst(name("Nat"), vec![]);
                let succ = |x: Term| Term::app(Term::cnst(name("Nat.succ"), vec![]), x);
                Term::lam(
                    nat(),
                    Term::lam(
                        nat(),
                        Term::apps(
                            Term::cnst(name("Nat.rec"), vec![Level::of_nat(1)]),
                            [
                                Term::lam(nat(), nat()),
                                Term::Var(0),
                                Term::lam(nat(), Term::lam(nat(), succ(Term::Var(0)))),
                                Term::Var(1),
                            ],
                        ),
                    ),
                )
            },
        )
        .unwrap();
        k
    }

    fn lit(n: u32) -> Term {
        let mut t = Term::cnst(name("Nat.zero"), vec![]);
        for _ in 0..n {
            t = Term::app(Term::cnst(name("Nat.succ"), vec![]), t);
        }
        t
    }

    /// NbE computes through recursors: `add 2 3` normalizes to `5`.
    #[test]
    fn normalizes_arithmetic() {
        let k = nat_kernel();
        let nbe = Nbe::new(k.env());
        let e = Term::apps(Term::cnst(name("add"), vec![]), [lit(2), lit(3)]);
        assert_eq!(nbe.normalize(&e), lit(5));
    }

    /// Differential check: `normalize t` is definitionally equal to `t` (the trusted
    /// reducer agrees), across a battery of terms.
    #[test]
    fn normal_form_is_def_eq_to_original() {
        let k = nat_kernel();
        let nbe = Nbe::new(k.env());
        let chk = Checker::new(k.env());
        let terms = [
            Term::apps(Term::cnst(name("add"), vec![]), [lit(4), lit(1)]),
            Term::apps(Term::cnst(name("add"), vec![]), [lit(0), lit(3)]),
            Term::apps(Term::cnst(name("add"), vec![]), [
                Term::apps(Term::cnst(name("add"), vec![]), [lit(1), lit(2)]),
                lit(2),
            ]),
            // a function value (exercises quote under binders)
            Term::lam(Term::cnst(name("Nat"), vec![]),
                Term::apps(Term::cnst(name("add"), vec![]), [Term::Var(0), lit(1)])),
        ];
        for t in terms {
            let nf = nbe.normalize(&t);
            assert!(chk.def_eq(&t, &nf), "normalize disagreed with reducer on {t:?}");
        }
    }

    /// Differential check: `conv` agrees with the kernel's conversion.
    #[test]
    fn conv_agrees_with_kernel() {
        let k = nat_kernel();
        let nbe = Nbe::new(k.env());
        let chk = Checker::new(k.env());
        let pairs = [
            (Term::apps(Term::cnst(name("add"), vec![]), [lit(2), lit(3)]), lit(5), true),
            (Term::apps(Term::cnst(name("add"), vec![]), [lit(2), lit(2)]), lit(5), false),
            (Term::apps(Term::cnst(name("add"), vec![]), [lit(0), lit(4)]), lit(4), true),
        ];
        for (a, b, expected) in pairs {
            assert_eq!(nbe.conv(&a, &b), expected);
            assert_eq!(chk.def_eq(&a, &b), expected, "kernel/nbe disagree");
        }
    }

    /// η: `λx. f x` and `f` have the same normal form under `conv`.
    #[test]
    fn eta_equality() {
        let k = nat_kernel();
        let nbe = Nbe::new(k.env());
        // f := add 1 ;  λx. f x   vs   f
        let f = Term::app(Term::cnst(name("add"), vec![]), lit(1));
        let eta = Term::lam(Term::cnst(name("Nat"), vec![]), Term::app(f.lift(1, 0), Term::Var(0)));
        assert!(nbe.conv(&eta, &f));
    }

    /// `A : Type 0`, `a b c : A`, `p : Path A a b`, `q : Path A b c` — a minimal
    /// environment with an **opaque** (axiomatized, non-`PLam`) path `p`, used to
    /// exercise path-η on a neutral path.
    fn path_kernel() -> crate::kernel::Kernel {
        let mut k = crate::kernel::Kernel::new();
        let cn = |s: &str| Term::cnst(name(s), vec![]);
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        k.add_axiom("b", 0, cn("A")).unwrap();
        k.add_axiom("c", 0, cn("A")).unwrap();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        k.add_axiom("q", 0, Term::path(cn("A"), cn("b"), cn("c"))).unwrap();
        k
    }

    /// Path-η: `p ≡ ⟨i⟩ p @ i` for an opaque (axiomatized, non-`PLam`) path `p`.
    /// This is the direct payoff test for `alpha_eta_eq`'s new `PLam` arms —
    /// before this change, a neutral `p` had no `PLam` shape to reduce against, so
    /// only literal `PLam`-built paths were ever recognized as equal to their own
    /// η-expansion.
    #[test]
    fn path_eta_equality_on_an_opaque_path() {
        let k = path_kernel();
        let nbe = Nbe::new(k.env());
        let p = Term::cnst(name("p"), vec![]);
        let eta = Term::plam(Term::papp(p.lift(1, 0), Term::Var(0)));
        assert!(nbe.conv(&eta, &p), "opaque path must be conv-equal to its own η-expansion");
        // And the authoritative checker's `is_def_eq` agrees (differential check,
        // same discipline as `conv_agrees_with_kernel` above).
        let chk = Checker::new(k.env());
        assert!(chk.def_eq(&eta, &p));
    }

    /// Adversarial: path-η must NOT equate two genuinely distinct opaque paths
    /// with *different* endpoints (`p : Path A a b` vs `q : Path A b c`, so even
    /// their types differ) — path-η only ever equates a path with its own
    /// η-expansion, never two unrelated paths. If this were broken, path-η would
    /// be too strong (equating things that aren't propositionally equal, let
    /// alone definitionally) rather than just the standard η law.
    #[test]
    fn path_eta_does_not_equate_unrelated_opaque_paths() {
        let k = path_kernel();
        let nbe = Nbe::new(k.env());
        let chk = Checker::new(k.env());
        let p = Term::cnst(name("p"), vec![]);
        let q = Term::cnst(name("q"), vec![]);
        assert!(!nbe.conv(&p, &q), "distinct opaque paths with different endpoints must stay unequal");
        assert!(!chk.def_eq(&p, &q));
        // Nor does it collapse the *endpoints* of distinct paths — `a` and `c` are
        // unrelated closed axioms (no path between them was ever assumed) and must
        // stay distinct even after adding path-η.
        assert!(!chk.def_eq(&Term::cnst(name("a"), vec![]), &Term::cnst(name("c"), vec![])));
    }

    /// Termination: path-η is a single, bounded η-expansion step exactly like
    /// `Lam`-η (see `check::Checker::compare`'s doc comment on its matching arm
    /// for the full argument) — it does not loop even when compared against a
    /// deliberately deep chain of `PApp`/`PLam` wrappers around an opaque path.
    /// This just needs to terminate (and agree) rather than diverge or stack
    /// overflow.
    #[test]
    fn path_eta_terminates_on_nested_wrappers() {
        let k = path_kernel();
        let nbe = Nbe::new(k.env());
        let p = Term::cnst(name("p"), vec![]);
        // ⟨i⟩ (⟨j⟩ p @ j) @ i  — a doubly η-expanded wrapper around the opaque `p`.
        let once = Term::plam(Term::papp(p.lift(1, 0), Term::Var(0)));
        let twice = Term::plam(Term::papp(once.lift(1, 0), Term::Var(0)));
        assert!(nbe.conv(&twice, &p), "doubly-wrapped opaque path must still converge to conv-equal");
    }
}

/// Adversarial and termination coverage for the two conversion-completeness fixes
/// landed in this module (see [`Value::INeg`]'s doc for the interval-lattice
/// eager-folding fix, and [`Nbe::family_is_constant_value`]'s doc for the
/// `venv`-aware `Transp` regularity probe): both are *completeness*-only changes
/// (more well-typed terms become convertible), so the standing anti-`False`
/// discipline this crate requires everywhere near the trusted reducer applies here
/// too — these tests pin down that the fix does not equate anything it shouldn't,
/// and that the newly-unstuck nested reductions actually terminate.
#[cfg(test)]
mod completeness_fix_soundness_tests {
    use super::*;
    use crate::inductive::declare_nat;
    use crate::kernel::Kernel;
    use crate::term::name;

    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    fn nat_kernel() -> Kernel {
        let mut k = Kernel::new();
        declare_nat(k.env_mut()).unwrap();
        k
    }

    fn lit(n: u32) -> Term {
        let mut t = cn("Nat.zero");
        for _ in 0..n {
            t = Term::app(cn("Nat.succ"), t);
        }
        t
    }

    /// **Absolute anti-`False`, #1**: `Nat.zero` and `Nat.succ Nat.zero` — two
    /// distinct closed canonical values of an ordinary (non-cubical) inductive —
    /// remain non-convertible after both fixes. Neither fix touches ordinary
    /// (non-interval) evaluation/quoting at all, but this is exactly the kind of
    /// "did the conversion checker get looser than it should have" check this
    /// crate's soundness discipline demands before/after any reducer change.
    #[test]
    fn distinct_nat_canonicals_stay_distinct() {
        let k = nat_kernel();
        assert!(!k.def_eq(&lit(0), &lit(1)));
        assert!(!k.def_eq(&lit(1), &lit(2)));
        let nbe = Nbe::new(k.env());
        assert!(!nbe.conv(&lit(0), &lit(1)));
    }

    /// **Absolute anti-`False`, #2**: there is still no way to construct a closed
    /// `Path Nat 0 1` (nor, a fortiori, an `Empty`/`False` witness derived from
    /// one) — the fix changes *when* a `Transp` collapses to its own argument, it
    /// never lets a `Transp` produce a value that doesn't already inhabit the
    /// declared type, so distinct canonical `Nat`s still can't be bridged by a
    /// path. Mirrors this crate's standing convention (see e.g. `crate::cubical`'s
    /// and `crate::kan`'s own "cannot manufacture a path between unrelated
    /// axioms/values" tests) at the two constructions this pass actually touched:
    /// `crate::cubical::trans` and the interval-lattice-eager `IMeet`/`IJoin`
    /// smart constructors.
    #[test]
    fn no_path_nat_0_1_via_trans_or_interval_folding() {
        let k = nat_kernel();
        // `refl 0 : Path Nat 0 0` — trying to reuse it as if it proved `Path Nat 0
        // 1` must still be rejected by `check`, exactly as before this pass.
        let refl0 = crate::cubical::refl(&lit(0));
        assert!(k.check(&refl0, &Term::path(cn("Nat"), lit(0), lit(1))).is_err());
        // Nor does `trans` (now that its right-unit/inverse laws close) let two
        // *genuine* paths compose into a path between values they were never
        // endpoints of: `trans Nat 0 0 (refl 0) (refl 0) : Path Nat 0 0`, not
        // `Path Nat 0 1`.
        let composed = crate::cubical::trans(&cn("Nat"), &lit(0), &lit(0), &refl0.clone(), &refl0);
        let ty = k.infer(&composed).unwrap();
        assert!(k.def_eq(&ty, &Term::path(cn("Nat"), lit(0), lit(0))));
        assert!(!k.def_eq(&ty, &Term::path(cn("Nat"), lit(0), lit(1))));
    }

    /// **Absolute anti-`False`, #3** (the standing type-path-axiom smuggle attack —
    /// see `crate::kan::family_is_constant`'s own doc, "The critical non-example
    /// still stays stuck"): transporting along a genuinely-varying, opaque
    /// `p : Path Type A B` must still get stuck (not collapse) even after
    /// [`Nbe::family_is_constant_value`] reuses the real `venv` — the fresh marker
    /// this probe substitutes stands *only* for the `Transp`'s own interval binder,
    /// never for `p` itself (an ordinary, already-bound free variable whose real,
    /// opaque value is what the probe correctly propagates through unchanged).
    #[test]
    fn family_is_constant_value_does_not_smuggle_a_type_change_through_an_axiomatized_path() {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("B", 0, Term::typ(0)).unwrap();
        k.add_axiom("p", 0, Term::path(Term::typ(0), cn("A"), cn("B"))).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        // family := λi. p @ i  (genuinely varying: its own boundary literally is
        // `A`/`B`, two distinct axioms — no evaluation can make this constant).
        let fam = Term::papp(cn("p").lift(1, 0), Term::Var(0));
        let t = Term::transp(fam, crate::face::Cof::bot(), cn("a"));
        // `Transp` is well-typed regardless of whether regularity fires (its
        // `infer` rule only needs `a : family[i:=i0]`, which holds here) — the
        // soundness-relevant fact is that it stays *stuck at type `B`*, i.e. it
        // must NOT be convertible to `a` (which would mean the family was wrongly
        // judged constant and the value smuggled straight through, losing the
        // genuine `A`-to-`B` type change `p` witnesses).
        let ty = k.infer(&t).expect("transp is well-typed even when its family is genuinely non-constant");
        assert!(k.def_eq(&ty, &cn("B")));
        assert!(!k.def_eq(&t, &cn("a")), "a genuinely type-changing transp must not collapse to its own argument");
    }

    /// **Absolute anti-`False`, #4** (this pass's own fix —
    /// [`Nbe::family_whnf_pi`], the nested-`trans`-as-`J`-subject completeness
    /// fix): a nested `trans(trans(p,q),r)` now type-checks and its *value*
    /// reduces (see [`Nbe::family_whnf_pi`]'s doc), but it still only ever
    /// proves `Path A w z` — the *actual* composite of `p:w=x`, `q:x=y`,
    /// `r:y=z` — never an unrelated endpoint. `family_whnf_pi` only recognizes
    /// a family as `Π`-shaped by *actually evaluating* it against the real
    /// `venv` and reading back exactly what it denotes (never fabricating or
    /// guessing a `Π`), so a bogus target must still be rejected by
    /// `Checker::check`.
    #[test]
    fn nested_trans_still_rejects_a_wrong_endpoint() {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        for n in ["w", "x", "y", "z", "other"] {
            k.add_axiom(n, 0, cn("A")).unwrap();
        }
        k.add_axiom("p", 0, Term::path(cn("A"), cn("w"), cn("x"))).unwrap();
        k.add_axiom("q", 0, Term::path(cn("A"), cn("x"), cn("y"))).unwrap();
        k.add_axiom("r", 0, Term::path(cn("A"), cn("y"), cn("z"))).unwrap();
        let pq = crate::cubical::trans(&cn("A"), &cn("w"), &cn("y"), &cn("p"), &cn("q"));
        let pqr = crate::cubical::trans(&cn("A"), &cn("w"), &cn("z"), &pq, &cn("r"));
        let ty = k.infer(&pqr).expect("nested trans now typechecks");
        assert!(k.def_eq(&ty, &Term::path(cn("A"), cn("w"), cn("z"))));
        assert!(
            !k.def_eq(&ty, &Term::path(cn("A"), cn("w"), cn("other"))),
            "nested trans must not smuggle a path to an unrelated endpoint"
        );
        assert!(k.check(&pqr, &Term::path(cn("A"), cn("w"), cn("other"))).is_err());
        // And the genuine composite still doesn't degenerate into `refl`-at-`w`:
        // `w`/`z` are distinct opaque axioms, so `Path A w z` is not `Path A w w`.
        assert!(!k.def_eq(&ty, &Term::path(cn("A"), cn("w"), cn("w"))));
    }

    /// **Termination adversarial check**: the ordinary (non-nested-probe) path
    /// through [`Nbe::family_whnf_pi`] terminates and is deterministic — re-run
    /// the same nested-`trans` term through a plain top-level `Nbe::normalize`
    /// (no enclosing `family_is_constant_value` probe in scope) and confirm it
    /// terminates and reaches the same normal form both times.
    #[test]
    fn family_whnf_pi_guard_does_not_disable_the_ordinary_path() {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        for n in ["w", "x", "y", "z"] {
            k.add_axiom(n, 0, cn("A")).unwrap();
        }
        k.add_axiom("p", 0, Term::path(cn("A"), cn("w"), cn("x"))).unwrap();
        k.add_axiom("q", 0, Term::path(cn("A"), cn("x"), cn("y"))).unwrap();
        k.add_axiom("r", 0, Term::path(cn("A"), cn("y"), cn("z"))).unwrap();
        let pq = crate::cubical::trans(&cn("A"), &cn("w"), &cn("y"), &cn("p"), &cn("q"));
        let pqr = crate::cubical::trans(&cn("A"), &cn("w"), &cn("z"), &pq, &cn("r"));
        let nbe = Nbe::new(k.env());
        let n1 = nbe.normalize(&pqr);
        let n2 = nbe.normalize(&pqr);
        assert_eq!(n1, n2, "normalization must be deterministic/terminating on repeat calls");
        k.check(&pqr, &Term::path(cn("A"), cn("w"), cn("z"))).unwrap();
    }

    /// **Termination**: the previously-stuck nested `trans`-under-`J` redex
    /// (`crate::cubical::trans_right_unit`'s base case, and its two inverse-law
    /// siblings) now fully normalizes — and does so promptly, not by looping.
    /// `family_is_constant_value`'s smart-constructor probes are each `O(1)`
    /// (structural matches on already-evaluated operands, see [`Value::INeg`]'s
    /// doc) and the probe itself runs `eval`+`quote` exactly once per `Transp`
    /// node — so this is a plain "does the whole call return" check standing in
    /// for the doc's termination argument (an infinite loop here would hang the
    /// test, which the test harness's own timeout would catch).
    #[test]
    fn previously_stuck_nested_trans_terminates_and_closes() {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        k.add_axiom("b", 0, cn("A")).unwrap();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a"), cn("b"))).unwrap();
        let terms = [
            crate::cubical::trans_right_unit(&cn("A"), &cn("a"), &cn("b"), &cn("p")),
            crate::cubical::trans_inv_right(&cn("A"), &cn("a"), &cn("b"), &cn("p")),
            crate::cubical::trans_inv_left(&cn("A"), &cn("a"), &cn("b"), &cn("p")),
        ];
        for t in &terms {
            // Two independent code paths that both fully normalize the term —
            // `infer` (via `Checker::check`'s internal `is_def_eq`) and a direct
            // `Nbe::normalize` call — both must complete (not hang) and agree the
            // term is well-typed.
            k.infer(t).expect("previously-stuck nested trans law must now typecheck");
            let nbe = Nbe::new(k.env());
            let _ = nbe.normalize(t); // must terminate
        }
    }

    /// Differential check (this crate's standing convention): the level-0
    /// interval-lattice identity laws this pass added to [`Value::INeg`]'s
    /// evaluation agree with `crate::cubical::normalize_interval`'s independent,
    /// DNF-based authority on a handful of concrete cases.
    #[test]
    fn eager_interval_folding_agrees_with_normalize_interval() {
        let cases: Vec<(Term, Term)> = vec![
            (Term::imeet(Term::IZero, Term::Var(0)), Term::IZero),
            (Term::imeet(Term::Var(0), Term::IZero), Term::IZero),
            (Term::imeet(Term::IOne, Term::Var(0)), Term::Var(0)),
            (Term::ijoin(Term::IOne, Term::Var(0)), Term::IOne),
            (Term::ijoin(Term::IZero, Term::Var(0)), Term::Var(0)),
            (Term::ineg(Term::ineg(Term::Var(0))), Term::Var(0)),
        ];
        for (lhs, rhs) in cases {
            assert_eq!(
                crate::cubical::normalize_interval(&lhs),
                crate::cubical::normalize_interval(&rhs),
                "lhs={lhs:?} rhs={rhs:?}"
            );
        }
        // And the eager evaluator-level fold agrees definitionally too (checked via
        // `Nbe::conv`, open in one variable).
        let mut k = Kernel::new();
        let _ = &mut k; // env not needed (no constants referenced), kept for `Nbe::new`
        let env = crate::env::Env::new();
        let nbe = Nbe::new(&env);
        assert!(nbe.conv(&Term::plam(Term::imeet(Term::IZero, Term::Var(0))), &Term::plam(Term::IZero)));
        assert!(nbe.conv(&Term::plam(Term::imeet(Term::IOne, Term::Var(0))), &Term::plam(Term::Var(0))));
    }

    /// Sanity that [`Nbe::family_is_constant_value`]'s position-indexed marker
    /// scheme (see its doc) really does compose safely under nesting — a
    /// direct, minimal exercise of two *nested* probes (mirroring the real
    /// nested-`Transp` shape this fix targets) to confirm they don't collide,
    /// panic, or hang.
    #[test]
    fn nested_family_is_constant_probes_do_not_collide() {
        let k = nat_kernel();
        let nbe = Nbe::new(k.env());
        // outer family: λi. (λj. j) applied under a nested constant-check —
        // constructed directly rather than via `trans_right_unit` to keep this a
        // minimal, standalone repro of "two probes running one inside the other".
        let inner_fam = Term::Var(0).lift(1, 0); // λj. (outer i, lifted) -- non-constant in j on purpose
        let inner_transp = Term::transp(inner_fam, crate::face::Cof::bot(), Term::Var(0));
        let outer_fam = inner_transp; // λi. transp(...) -- itself independent of i's own occurrence pattern
        let outer = Term::transp(outer_fam.clone(), crate::face::Cof::bot(), lit(0));
        // Must not panic/hang; the exact reduction result isn't the point here (the
        // shape is deliberately degenerate), just that nested probes coexist safely.
        let _ = nbe.normalize(&outer);
    }

    /// **Direct adversarial exercise of the nested-probe quoting fix**: forces
    /// [`Nbe::family_whnf_pi`] to fire *while already nested inside* a
    /// [`Nbe::family_is_constant_value`] probe's own recursive evaluation —
    /// exactly the shape the old `contains_probe_marker` guard used to bail
    /// out of — and confirms (a) no panic (in particular no underflow in
    /// [`Nbe::quote`]'s `level - 1 - k` arithmetic), (b) the call terminates,
    /// and (c) no variable capture: a genuinely bound outer variable (`w`,
    /// opaque, distinct from every axiom the family touches) must still read
    /// back as itself, never silently aliased to the inner probe's own fresh
    /// marker or to an unrelated bound index. `trans_assoc`'s base case is
    /// the real-world instance of exactly this nesting (see
    /// `crate::cubical`'s "Phase 4.6" doc and
    /// `crate::cubical::groupoid_law_tests::trans_assoc_closes`).
    #[test]
    fn nested_probe_marker_quoting_does_not_capture_or_panic() {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("w", 0, cn("A")).unwrap();
        k.add_axiom("x", 0, cn("A")).unwrap();
        k.add_axiom("y", 0, cn("A")).unwrap();
        k.add_axiom("z", 0, cn("A")).unwrap();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("w"), cn("x"))).unwrap();
        k.add_axiom("q", 0, Term::path(cn("A"), cn("x"), cn("y"))).unwrap();
        k.add_axiom("r", 0, Term::path(cn("A"), cn("y"), cn("z"))).unwrap();
        let nbe = Nbe::new(k.env());
        // `trans (trans p q) r` — the inner `trans p q` is itself a `Transp`-
        // headed term (a `J`-motive application, not a syntactic `Term::Pi`),
        // used as the *subject* of the outer `trans`'s own `Transp`. Forcing
        // the outer `Transp`'s regularity probe (`family_is_constant_value`)
        // evaluates the inner `Transp` underneath it; the inner `Transp`'s own
        // `Π`-case filling needs `family_whnf_pi` to recognize its motive-
        // application family as a `Π` — while nested inside the outer probe.
        let pq = crate::cubical::trans(&cn("A"), &cn("w"), &cn("y"), &cn("p"), &cn("q"));
        let pqr = crate::cubical::trans(&cn("A"), &cn("w"), &cn("z"), &pq, &cn("r"));
        // Must not panic (no quote underflow) and must terminate.
        let n1 = nbe.normalize(&pqr);
        // Anti-capture: `w` (a genuinely bound/opaque axiom, unrelated to any
        // probe marker) must still appear, unshadowed, as the term's own left
        // endpoint once type-checked — i.e. the axiom `w` itself, not some
        // bogus small `Term::Var` index a captured marker could have produced.
        let ty = k.infer(&pqr).expect("nested trans (subject of an outer trans) typechecks");
        assert!(k.def_eq(&ty, &Term::path(cn("A"), cn("w"), cn("z"))));
        // Determinism: re-normalizing must reach the same result (no capture-
        // induced nondeterminism from a stray marker leaking into the output).
        let n2 = nbe.normalize(&pqr);
        assert_eq!(n1, n2, "nested-probe normalization must be deterministic");
    }
}
