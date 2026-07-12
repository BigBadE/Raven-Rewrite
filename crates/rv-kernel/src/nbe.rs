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

use crate::env::{CircleRole, Decl, Env, QuotRole, TruncRole};
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
enum VEnv {
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
                                    self.try_circle_rec(h6.clone(), spine6.clone())
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
                };
                for arg in spine {
                    t = Term::app(t, self.quote(level, arg));
                }
                t
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

/// Compare two normal-form terms up to α-equivalence, η, and grade-blindness on `Π`.
fn alpha_eta_eq(a: &Term, b: &Term) -> bool {
    match (a, b) {
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
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::Checker;
    use crate::generate::{eq_spec, nat_spec};
    use crate::kernel::Kernel;
    use crate::term::name;

    fn nat_kernel() -> Kernel {
        let mut k = Kernel::new();
        k.declare_inductive(nat_spec()).unwrap();
        k.declare_inductive(eq_spec()).unwrap();
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
}
