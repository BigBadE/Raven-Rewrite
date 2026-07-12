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

use crate::env::{CircleRole, Decl, Env, HitRole, QuotRole, TruncRole};
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
    /// **Phase 3.5** (De Morgan interval, see `crate::cubical`): reversal/meet/join,
    /// kept as plain structural values (no eager simplification in the evaluator —
    /// the one normalization authority is `crate::cubical::normalize_interval`,
    /// applied at comparison time by [`Nbe::conv`]/`alpha_eta_eq` on the *quoted*
    /// term, exactly like `Value::Sys`/`Value::Partial` defer their face-formula
    /// reasoning to `crate::face` rather than reimplementing it here).
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
            Term::INeg(r) => Rc::new(Value::INeg(self.eval(venv, r))),
            Term::IMeet(r, s) => Rc::new(Value::IMeet(self.eval(venv, r), self.eval(venv, s))),
            Term::IJoin(r, s) => Rc::new(Value::IJoin(self.eval(venv, r), self.eval(venv, s))),
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
            // regularity rule — structural constancy, and *only* structural
            // constancy (never `φ`, see `crate::kan`'s soundness argument) —
            // fires as evaluation of `a`; otherwise stays stuck.
            Term::Transp(fam, phi, a) => {
                if !crate::term::mentions_var(fam, 0) {
                    self.eval(venv, a)
                } else if let Term::Pi(_g, dom, cod) = fam.as_ref() {
                    // `Π`-case filling (see `crate::kan`'s "Phase 3.6" doc, and
                    // `crate::reduce::Reducer::whnf`'s matching arm — differentially
                    // tested): the built term introduces no new *free* variable (every
                    // fresh binder it creates is bound within it), so it's evaluated
                    // against the very same `venv`.
                    let built = crate::kan::transp_pi_rule(dom, cod, a);
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
                    Rc::new(Value::HComp(
                        HCompClosure {
                            env: venv.clone(),
                            ty: self.eval(venv, ty),
                            phi: phi.clone(),
                            u: u.clone(),
                        },
                        self.eval(venv, u0),
                    ))
                }
            }
        }
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
                                        self.try_hit_rec(h7.clone(), spine7.clone())
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
