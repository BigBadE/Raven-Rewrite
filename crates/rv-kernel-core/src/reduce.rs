//! Reduction and definitional equality — the computational heart of the kernel.
//!
//! Two services, both operating against an [`Env`]:
//!
//! * [`Reducer::whnf`] — weak-head normal form under the four reduction rules:
//!   **β** (`(λ. b) a ↦ b[a]`), **δ** (unfold a definition), **ζ** (`let`), and
//!   **ι** (a recursor applied to a constructor fires its computation rule). η is
//!   handled in conversion, not here.
//! * [`Reducer::is_def_eq`] — definitional (conversion) equality: are two terms equal
//!   up to reduction and η? This is the relation the type-checker uses whenever it
//!   must accept a value of an expected type.
//!
//! Soundness lives here as much as in the checker: if `whnf` reduced unsoundly or
//! `is_def_eq` equated distinct types, ill-typed programs would slip through. The
//! rules are the standard ones; we keep them total and structural.

use crate::env::{CircleRole, Decl, Destructor, Env, HitRole, QuotRole, Recursor, TruncRole};
use crate::level::{self, Level};
use crate::term::{Name, Term};

/// A reducer bound to an environment.
pub struct Reducer<'e> {
    pub env: &'e Env,
}

impl<'e> Reducer<'e> {
    pub fn new(env: &'e Env) -> Self {
        Self { env }
    }

    /// Reduce `t` to weak-head normal form: the outermost constructor is canonical
    /// (a `Sort`/`Pi`/`Lam`, or a neutral term whose head is a variable, axiom,
    /// constructor, or stuck recursor). Arguments are *not* recursively normalized.
    pub fn whnf(&self, t: &Term) -> Term {
        let (mut head, mut args) = t.unfold_apps();
        loop {
            match &head {
                // ζ: unfold a `let`.
                Term::Let(_, _, value, body) => {
                    head = body.instantiate(value);
                }
                Term::Const(n, ls) => match self.env.get(n) {
                    // δ: unfold a definition (instantiating its universe params).
                    Some(Decl::Def { value, .. }) => {
                        head = value.instantiate_levels(ls);
                    }
                    // ι: a recursor meeting its constructor.
                    Some(Decl::Recursor(rec)) => match self.try_iota(rec, ls, &args) {
                        Some(reduced) => {
                            let (h, a) = reduced.unfold_apps();
                            head = h;
                            args = a;
                        }
                        None => break,
                    },
                    // ν: a destructor observing a corecursor application.
                    Some(Decl::Destructor(dtor)) => match self.try_nu(n, dtor, ls, &args) {
                        Some(reduced) => {
                            let (h, a) = reduced.unfold_apps();
                            head = h;
                            args = a;
                        }
                        None => break,
                    },
                    // Quotient computation: `Quot.lift … f resp (Quot.mk … a) ↦ f a`, and
                    // identically for the dependent `Quot.rec` (same spine positions —
                    // see `try_quot_lift`'s doc comment).
                    Some(Decl::Quot(q)) if q.role == QuotRole::Lift || q.role == QuotRole::Rec => {
                        match self.try_quot_lift(&args) {
                            Some(reduced) => {
                                let (h, a) = reduced.unfold_apps();
                                head = h;
                                args = a;
                            }
                            None => break,
                        }
                    }
                    // Truncation computation: `Trunc.lift … f resp (Trunc.tr … a) ↦ f a`.
                    Some(Decl::Trunc(t)) if t.role == TruncRole::Lift => {
                        match self.try_trunc_lift(&args) {
                            Some(reduced) => {
                                let (h, a) = reduced.unfold_apps();
                                head = h;
                                args = a;
                            }
                            None => break,
                        }
                    }
                    // Truncation computation (dependent):
                    // `Trunc.rec … isProp f (Trunc.tr … a) ↦ f a`.
                    Some(Decl::Trunc(t)) if t.role == TruncRole::Rec => {
                        match self.try_trunc_rec(&args) {
                            Some(reduced) => {
                                let (h, a) = reduced.unfold_apps();
                                head = h;
                                args = a;
                            }
                            None => break,
                        }
                    }
                    // Circle computation: `S¹.rec P pt lp S¹.base ↦ pt`.
                    Some(Decl::Circle(c)) if c.role == CircleRole::Rec => {
                        match self.try_circle_rec(&args) {
                            Some(reduced) => {
                                let (h, a) = reduced.unfold_apps();
                                head = h;
                                args = a;
                            }
                            None => break,
                        }
                    }
                    // User-declared 1-HIT computation (see `crate::hit`):
                    // `H.rec.{v} P case_0 .. resp_0 .. (H.p_i) ↦ case_i`.
                    Some(Decl::Hit(hh)) if matches!(hh.role, HitRole::Rec { .. }) => {
                        match self.try_hit_rec(n, ls, hh, &args) {
                            Some(reduced) => {
                                let (h, a) = reduced.unfold_apps();
                                head = h;
                                args = a;
                            }
                            None => break,
                        }
                    }
                    _ => break,
                },
                // β: a lambda meeting an argument.
                Term::Lam(_, body) => {
                    if args.is_empty() {
                        break;
                    }
                    let arg = args.remove(0);
                    head = body.instantiate(&arg);
                }
                // A substitution re-exposed an application spine: re-flatten.
                Term::App(..) => {
                    let (h, mut a) = head.unfold_apps();
                    a.extend(args.drain(..));
                    head = h;
                    args = a;
                }
                // Sort, Var, Pi, or a stuck Const: weak-head normal.
                _ => break,
            }
        }
        Term::apps(head, args)
    }

    /// Try one ι-reduction of `rec` (carrying universe args `ls`) applied to `args`.
    /// Returns the contracted term, or `None` if the recursor is stuck (too few
    /// arguments, or the major premise is not a constructor application).
    fn try_iota(&self, rec: &Recursor, ls: &[level::Level], args: &[Term]) -> Option<Term> {
        let major_pos = rec.major_pos();
        if args.len() <= major_pos {
            return None; // not yet saturated up to the scrutinee
        }
        // Reduce the major premise and split off its constructor head.
        let major = self.whnf(&args[major_pos]);
        let (ctor_head, ctor_args) = major.unfold_apps();
        let Term::Const(ctor_name, _) = &ctor_head else {
            return None;
        };
        // It must be a constructor of *this* inductive, with a matching rule.
        let rule = rec.rules.get(ctor_name)?;
        match self.env.get(ctor_name) {
            Some(Decl::Constructor(c)) if c.ind == rec.ind => {}
            _ => return None,
        }
        // Constructor arguments are [inductive params…, fields…]; the recursor
        // already knows the params, so we forward only the fields.
        let fields = &ctor_args[rec.num_params..];
        // [params…, motives…, minors…] — motives is `num_motives` wide (the group size
        // for a mutual recursor, else 1).
        let nh = rec.num_params + rec.num_motives;
        let params_and_motives = &args[0..nh];
        let minors = &args[nh..nh + rec.num_minors];

        // rhs applied to [params…, motives…, minors…, fields…]; the rhs was built to
        // re-invoke the (possibly sibling) recursor on recursive fields, so this is the
        // whole step.
        let mut applied = rule.rhs.instantiate_levels(ls);
        for a in params_and_motives.iter().chain(minors).chain(fields) {
            applied = Term::app(applied, a.clone());
        }
        // Any arguments beyond the major premise + indices were over-application;
        // re-attach them.
        for extra in &args[major_pos + 1..] {
            applied = Term::app(applied, extra.clone());
        }
        Some(applied)
    }

    /// Try one ν-reduction: destructor `dtor` (carrying universe args `ls`) applied to
    /// `args`, whose scrutinee (the argument right after the parameters and indices)
    /// whnf's to a **corecursor** application. Observation forces exactly one layer:
    ///
    /// * a **plain** destructor `d` reduces `d params indices (S.corec params X steps
    ///   cur_indices seed)` to `step_d cur_indices seed`;
    /// * a **corecursive** destructor `d` (result is the coinductive again) reduces it to
    ///   `S.corec params X steps new_indices (step_d cur_indices seed)` — one layer
    ///   peeled and the corecursor re-wrapped around the *new* seed **and** the *new*
    ///   indices (computed by instantiating the destructor's declared index-transform
    ///   with the current `[params, cur_indices]`). Because the recursive occurrence is
    ///   placed back *under* the corecursor (i.e. under a fresh observation),
    ///   corecursion is guarded by construction: no unfolding happens until the next
    ///   observation demands it.
    ///
    /// Returns `None` if the destructor is not yet saturated to its scrutinee or the
    /// scrutinee is not a corecursor application (a stuck/neutral observation).
    fn try_nu(
        &self,
        dtor_name: &crate::term::Name,
        dtor: &Destructor,
        _ls: &[level::Level],
        args: &[Term],
    ) -> Option<Term> {
        // Destructor spine: [params…, indices…, scrutinee, extra…]. The scrutinee sits
        // right after the coinductive's parameters and indices, whose counts we read
        // off the coinductive once we know which one this is.
        let coind = match self.env.get(&dtor.coind) {
            Some(Decl::Coinductive(c)) => c.clone(),
            _ => return None,
        };
        let scrut_pos = coind.num_params + coind.num_indices;
        if args.len() <= scrut_pos {
            return None; // not saturated to the scrutinee
        }
        let scrut = self.whnf(&args[scrut_pos]);
        let (corec_head, corec_args) = scrut.unfold_apps();
        let Term::Const(corec_name, _corec_ls) = &corec_head else {
            return None;
        };
        let corec = match self.env.get(corec_name) {
            Some(Decl::Corecursor(c)) if c.coind == dtor.coind => c.clone(),
            _ => return None,
        };
        let _ = dtor.index;
        let rule = corec.rules.get(dtor_name)?;
        if corec_args.len() < corec.arity() {
            return None; // corecursor itself not fully applied
        }
        // `S.corec params X steps cur_indices seed` — pull out the pieces.
        let step = &corec_args[rule.step_index];
        let cur_indices = &corec_args[corec.index_pos()..corec.index_pos() + corec.num_indices];
        let seed = &corec_args[corec.seed_pos()];
        // The observed field is `step cur_indices… seed` (a step is index-polymorphic:
        // `Π indices. X → R`).
        let mut observed = step.clone();
        for idx in cur_indices {
            observed = Term::app(observed, idx.clone());
        }
        observed = Term::app(observed, seed.clone());
        let result = if rule.corecursive {
            // Compute the *new* indices by instantiating the destructor's declared
            // index-transform (in context `[params, indices]`) with the corecursor's
            // *current* params+indices arguments. `subst_ctx` expects `images[i]` to
            // replace `Var(i)`; the transform's `Var(0)` is the innermost/last index,
            // so the substitution images are `[params ++ cur_indices]` reversed.
            let actual: Vec<Term> =
                corec_args[..corec.num_params].iter().chain(cur_indices).cloned().collect();
            let images: Vec<Term> = actual.into_iter().rev().collect();
            let new_indices: Vec<Term> =
                rule.index_transform.iter().map(|t| t.subst_ctx(&images)).collect();
            // Re-wrap: `S.corec params X steps new_indices (step cur_indices seed)` —
            // the next state under a fresh corecursor. Reuse the original corecursor
            // spine, swapping the indices and the seed.
            let mut rebuilt = corec_head.clone();
            for (i, a) in corec_args.iter().enumerate().take(corec.arity()) {
                if i == corec.seed_pos() {
                    rebuilt = Term::app(rebuilt, observed.clone());
                } else if i >= corec.index_pos() && i < corec.index_pos() + corec.num_indices {
                    rebuilt = Term::app(rebuilt, new_indices[i - corec.index_pos()].clone());
                } else {
                    rebuilt = Term::app(rebuilt, a.clone());
                }
            }
            rebuilt
        } else {
            observed
        };
        // Re-attach any over-application beyond the scrutinee.
        let mut applied = result;
        for extra in &args[scrut_pos + 1..] {
            applied = Term::app(applied, extra.clone());
        }
        Some(applied)
    }

    /// Try the single **quotient** computation rule (the dual of an ι-rule for the
    /// fixed `Quot.lift` constant):
    ///
    /// ```text
    ///   Quot.lift.{u v} A R B f resp (Quot.mk.{u} A R a)  ↦  f a
    /// ```
    ///
    /// `Quot.lift`'s spine is `[A, R, B, f, resp, q, extra…]`; the scrutinee `q` is at
    /// index 5 and `f` at index 3. We fire only when `q` weak-head-reduces to a literal
    /// `Quot.mk` application (spine `[A, R, a]`, so `a` is its last argument), discarding
    /// `resp` exactly as Lean does — its only role is to have been *type-checked to
    /// exist*, guaranteeing `f` respects `R`. Returns `None` (stuck/neutral) when not
    /// saturated to the scrutinee or the scrutinee is not a `Quot.mk`.
    ///
    /// Also drives the **dependent** recursor `Quot.rec`: its argument spine
    /// `[A, R, C, f, resp, q]` places `f` and the scrutinee `q` at the exact same
    /// indices (`C` merely occupies the slot `B` occupied for `Quot.lift`), so the same
    /// ι-rule `Quot.rec … f resp (Quot.mk … a) ↦ f a` applies unchanged; soundness for
    /// the dependent case comes from `resp`'s (richer, `Eq.rec`-transporting) type
    /// having been checked to exist — see `crate::quotient`'s doc comment.
    fn try_quot_lift(&self, args: &[Term]) -> Option<Term> {
        const F_POS: usize = 3;
        const SCRUT_POS: usize = 5;
        if args.len() <= SCRUT_POS {
            return None; // not yet applied to the quotient value
        }
        let scrut = self.whnf(&args[SCRUT_POS]);
        let (mk_head, mk_args) = scrut.unfold_apps();
        let Term::Const(mk_name, _) = &mk_head else {
            return None;
        };
        match self.env.get(mk_name) {
            Some(Decl::Quot(q)) if q.role == QuotRole::Mk => {}
            _ => return None,
        }
        // `Quot.mk A R a` — the representative `a` is the last (3rd) argument.
        if mk_args.len() != 3 {
            return None;
        }
        let a = &mk_args[2];
        let f = &args[F_POS];
        let mut applied = Term::app(f.clone(), a.clone());
        // Re-attach any over-application beyond the scrutinee.
        for extra in &args[SCRUT_POS + 1..] {
            applied = Term::app(applied, extra.clone());
        }
        Some(applied)
    }

    /// Try the single **propositional-truncation** computation rule (the point-constructor
    /// ι-rule for the fixed `Trunc.lift` constant):
    ///
    /// ```text
    ///   Trunc.lift.{u v} A P f resp (Trunc.tr.{u} A a)  ↦  f a
    /// ```
    ///
    /// `Trunc.lift`'s spine is `[A, P, f, resp, t, extra…]`; the scrutinee `t` is at index
    /// 4 and `f` at index 2. We fire only when `t` weak-head-reduces to a literal
    /// `Trunc.tr` application (spine `[A, a]`, so `a` is its last argument), discarding
    /// `resp` — its only role is to have been *type-checked to exist*, guaranteeing `f`
    /// respects the truncation. It NEVER fires on the path constructor `Trunc.eq` (that is
    /// not a `Trunc.tr` head). Returns `None` (stuck/neutral) when not saturated to the
    /// scrutinee or the scrutinee is not a `Trunc.tr`.
    fn try_trunc_lift(&self, args: &[Term]) -> Option<Term> {
        const F_POS: usize = 2;
        const SCRUT_POS: usize = 4;
        if args.len() <= SCRUT_POS {
            return None; // not yet applied to the truncation value
        }
        let scrut = self.whnf(&args[SCRUT_POS]);
        let (tr_head, tr_args) = scrut.unfold_apps();
        let Term::Const(tr_name, _) = &tr_head else {
            return None;
        };
        match self.env.get(tr_name) {
            Some(Decl::Trunc(t)) if t.role == TruncRole::Tr => {}
            _ => return None,
        }
        // `Trunc.tr A a` — the representative `a` is the last (2nd) argument.
        if tr_args.len() != 2 {
            return None;
        }
        let a = &tr_args[1];
        let f = &args[F_POS];
        let mut applied = Term::app(f.clone(), a.clone());
        // Re-attach any over-application beyond the scrutinee.
        for extra in &args[SCRUT_POS + 1..] {
            applied = Term::app(applied, extra.clone());
        }
        Some(applied)
    }

    /// Try the single **dependent truncation** computation rule (the point-constructor
    /// ι-rule for the fixed `Trunc.rec` constant):
    ///
    /// ```text
    ///   Trunc.rec.{u v} A C isProp f (Trunc.tr.{u} A a)  ↦  f a
    /// ```
    ///
    /// `Trunc.rec`'s spine is `[A, C, isProp, f, t, extra…]`; the scrutinee `t` is at
    /// index 4 and `f` at index 3 (one slot later than `Trunc.lift`'s `f`, since `C`
    /// and `isProp` together occupy the slots `P` and `resp` occupied for `Trunc.lift`).
    /// We fire only when `t` weak-head-reduces to a literal `Trunc.tr` application,
    /// discarding `isProp` — its only role is to have been *type-checked to exist*,
    /// guaranteeing `C` is a mere proposition pointwise (see `crate::trunc`'s doc
    /// comment for why that alone suffices, with no per-witness transport premise).
    /// It NEVER fires on the path constructor `Trunc.eq`. Returns `None` (stuck/neutral)
    /// when not saturated to the scrutinee or the scrutinee is not a `Trunc.tr`.
    fn try_trunc_rec(&self, args: &[Term]) -> Option<Term> {
        const F_POS: usize = 3;
        const SCRUT_POS: usize = 4;
        if args.len() <= SCRUT_POS {
            return None; // not yet applied to the truncation value
        }
        let scrut = self.whnf(&args[SCRUT_POS]);
        let (tr_head, tr_args) = scrut.unfold_apps();
        let Term::Const(tr_name, _) = &tr_head else {
            return None;
        };
        match self.env.get(tr_name) {
            Some(Decl::Trunc(t)) if t.role == TruncRole::Tr => {}
            _ => return None,
        }
        // `Trunc.tr A a` — the representative `a` is the last (2nd) argument.
        if tr_args.len() != 2 {
            return None;
        }
        let a = &tr_args[1];
        let f = &args[F_POS];
        let mut applied = Term::app(f.clone(), a.clone());
        // Re-attach any over-application beyond the scrutinee.
        for extra in &args[SCRUT_POS + 1..] {
            applied = Term::app(applied, extra.clone());
        }
        Some(applied)
    }

    /// Try the single **circle** computation rule (the point-constructor ι-rule for the
    /// fixed `S¹.rec` constant):
    ///
    /// ```text
    ///   S¹.rec.{v} P pt lp S¹.base  ↦  pt
    /// ```
    ///
    /// `S¹.rec`'s spine is `[P, pt, lp, t, extra…]`; the scrutinee `t` is at index 3 and
    /// `pt` at index 1. We fire only when `t` weak-head-reduces to the literal (nullary)
    /// `S¹.base` constant, discarding `lp` — its only role is to have been *type-checked
    /// to exist*, guaranteeing `pt` respects the `loop` path constructor. It NEVER fires
    /// on the path constructor `S¹.loop` (that is not an `S¹.base` head — `loop` is a
    /// proof of `Eq S¹ base base`, not itself a `S¹` value). Returns `None` (stuck/neutral)
    /// when not saturated to the scrutinee or the scrutinee is not `S¹.base`.
    fn try_circle_rec(&self, args: &[Term]) -> Option<Term> {
        const PT_POS: usize = 1;
        const SCRUT_POS: usize = 3;
        if args.len() <= SCRUT_POS {
            return None; // not yet applied to the circle value
        }
        let scrut = self.whnf(&args[SCRUT_POS]);
        let (base_head, base_args) = scrut.unfold_apps();
        let Term::Const(base_name, _) = &base_head else {
            return None;
        };
        match self.env.get(base_name) {
            Some(Decl::Circle(c)) if c.role == CircleRole::Base => {}
            _ => return None,
        }
        // `S¹.base` is nullary — any (well-typed) scrutinee reaching this point applies it
        // to no arguments.
        if !base_args.is_empty() {
            return None;
        }
        let pt = &args[PT_POS];
        let mut applied = pt.clone();
        // Re-attach any over-application beyond the scrutinee.
        for extra in &args[SCRUT_POS + 1..] {
            applied = Term::app(applied, extra.clone());
        }
        Some(applied)
    }

    /// Try a **user-declared 1-HIT** computation rule (see [`crate::hit`]): for
    /// `H.rec.{v} P case_0 .. case_{n-1} resp_0 .. resp_{m-1} t`, fires when `t`
    /// weak-head-reduces to the `i`-th point constructor *of the same HIT `id`* as
    /// `hh`, fully applied to its fields — `H.rec ... (H.p_i a_0 .. a_{k-1}) ↦
    /// case_i b_0 .. b_{k-1}` where `b_j = a_j` for a non-recursive field and `b_j =
    /// H.rec ... a_j` (a recursive call) for a field of type `H` itself. Never fires
    /// on a path constructor (its type is `Eq H _ _`, not `H` — ill-typed as a
    /// scrutinee), on a point constructor belonging to a *different* declared HIT
    /// (guarded by comparing `id`s), or when the scrutinee is not fully applied to its
    /// declared fields (stuck, e.g. a partially-applied point constructor or a
    /// neutral).
    fn try_hit_rec(&self, rname: &Name, ls: &[Level], hh: &crate::env::Hit, args: &[Term]) -> Option<Term> {
        let HitRole::Rec { num_points, num_paths } = hh.role else { return None };
        let scrut_pos = 1 + num_points as usize + num_paths as usize;
        if args.len() <= scrut_pos {
            return None; // not yet applied to the scrutinee
        }
        let scrut = self.whnf(&args[scrut_pos]);
        let (pt_head, pt_args) = scrut.unfold_apps();
        let Term::Const(pt_name, _) = &pt_head else {
            return None;
        };
        let (index, fields) = match self.env.get(pt_name) {
            Some(Decl::Hit(p)) if p.id == hh.id => match &p.role {
                HitRole::Point { index, fields } => (*index, fields.clone()),
                _ => return None,
            },
            _ => return None,
        };
        if pt_args.len() != fields.len() {
            return None; // not fully applied to its declared fields — stuck
        }
        let case_pos = 1 + index as usize;
        let mut applied = args[case_pos].clone();
        for (arg, is_rec) in pt_args.iter().zip(fields.iter()) {
            let b = if *is_rec {
                // Recursive call on this field: `H.rec.{v} <same P/case/resp> arg`.
                let mut rc = Term::cnst(rname.clone(), ls.to_vec());
                for a in &args[..scrut_pos] {
                    rc = Term::app(rc, a.clone());
                }
                Term::app(rc, arg.clone())
            } else {
                arg.clone()
            };
            applied = Term::app(applied, b);
        }
        for extra in &args[scrut_pos + 1..] {
            applied = Term::app(applied, extra.clone());
        }
        Some(applied)
    }

    /// Definitional equality: are `a` and `b` interchangeable up to reduction and η?
    pub fn is_def_eq(&self, a: &Term, b: &Term) -> bool {
        let a = self.whnf(a);
        let b = self.whnf(b);
        // Fast path: syntactic identity after whnf.
        if a == b {
            return true;
        }
        match (&a, &b) {
            (Term::Sort(l1), Term::Sort(l2)) => level::equiv(l1, l2),
            (Term::Var(i), Term::Var(j)) => i == j,
            (Term::Const(n1, l1), Term::Const(n2, l2)) => {
                n1 == n2
                    && l1.len() == l2.len()
                    && l1.iter().zip(l2).all(|(x, y)| level::equiv(x, y))
            }
            (Term::Pi(_, d1, b1), Term::Pi(_, d2, b2)) => {
                self.is_def_eq(d1, d2) && self.is_def_eq(b1, b2)
            }
            (Term::Lam(d1, b1), Term::Lam(d2, b2)) => {
                self.is_def_eq(d1, d2) && self.is_def_eq(b1, b2)
            }
            // η: `λx. body ≡ f`  iff  `body ≡ f x` (with `f` shifted under the binder).
            (Term::Lam(_, body), _) => {
                let eta = Term::app(b.lift(1, 0), Term::Var(0));
                self.is_def_eq(body, &eta)
            }
            (_, Term::Lam(_, body)) => {
                let eta = Term::app(a.lift(1, 0), Term::Var(0));
                self.is_def_eq(&eta, body)
            }
            // Neutral application spines: equal heads and pointwise-equal arguments.
            (Term::App(..), Term::App(..)) => {
                let (h1, a1) = a.unfold_apps();
                let (h2, a2) = b.unfold_apps();
                a1.len() == a2.len()
                    && self.is_def_eq(&h1, &h2)
                    && a1.iter().zip(&a2).all(|(x, y)| self.is_def_eq(x, y))
            }
            _ => false,
        }
    }
}
