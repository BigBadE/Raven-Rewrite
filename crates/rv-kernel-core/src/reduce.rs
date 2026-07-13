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

use crate::env::{
    CircleRole, Decl, Destructor, Env, HitRole, I2Role, QuotRole, Recursor, S1cRole, TruncRole,
};
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
                    // Interval-HIT computation (see `crate::interval_hit`): the
                    // *computing* `I2.rec`, with THREE ι-rules — two point rules
                    // (`zero`/`one`) and, the whole point of the module, a PATH rule
                    // that fires on a literal `I2.seg @ r` scrutinee.
                    Some(Decl::I2(c)) if c.role == I2Role::Rec => {
                        match self.try_i2_rec(&args) {
                            Some(reduced) => {
                                let (h, a) = reduced.unfold_apps();
                                head = h;
                                args = a;
                            }
                            None => break,
                        }
                    }
                    // Cubical circle computation (see `crate::circle_cubical`): the
                    // *computing* `S1c.rec`, with TWO ι-rules — a point rule (`base`)
                    // and, the whole point of the module, a PATH rule that fires on a
                    // literal `S1c.loop @ r` (a genuine SELF-loop) scrutinee.
                    Some(Decl::S1c(c)) if c.role == S1cRole::Rec => {
                        match self.try_s1c_rec(&args) {
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
                // Path application: `(PLam body) @ r ↦ body[i := r]` (see
                // `crate::cubical` — Phase-1's one computation rule for paths). If the
                // path being applied doesn't whnf to a literal `PLam` (e.g. it's a
                // free/neutral variable of `PathP` type), this stays *stuck*: Phase 1
                // has no η/boundary axiom for neutrals, only for actual abstractions
                // (see the module doc's soundness argument for why that's fine).
                Term::PApp(p, r) => {
                    let pw = self.whnf(p);
                    match &pw {
                        Term::PLam(body) => head = body.instantiate(r),
                        _ => {
                            head = Term::papp(pw, (**r).clone());
                            break;
                        }
                    }
                }
                // System reduction (see `crate::face`): a branch fires as soon as its
                // guard is *decided* true (not merely satisfiable) — e.g.
                // `[(i=0)↦t,(i=1)↦u]` reduces to `t` once `i` has been substituted to
                // `i0` elsewhere and this whnf call reaches the (by-then-literal)
                // guard. If no branch currently holds, the system is stuck: a valid
                // normal form, exactly like a neutral variable.
                Term::Sys(branches) => {
                    match branches.iter().find(|(phi, _)| crate::face::is_true(phi)) {
                        Some((_, t)) => head = (**t).clone(),
                        None => break,
                    }
                }
                // `transp` (see `crate::kan`): the **regularity rule** — transport
                // along a family that doesn't actually vary is the identity. This
                // is checked *structurally* first (`!mentions_var(fam, 0)`), then,
                // if that fails, via full computation
                // (`crate::kan::family_is_constant` — see its doc for the
                // normalization-aware extension and soundness argument); never via
                // `φ` (see `crate::kan`'s soundness argument for why a `φ = ⊤`
                // shortcut here would be UNSOUND: `φ` is unrelated to whether the
                // family genuinely depends on the interval variable).
                Term::Transp(fam, _phi, a) => {
                    if crate::kan::family_is_constant(self.env, fam) {
                        head = (**a).clone();
                    } else if let Term::Pi(_g, dom, cod) = fam.as_ref() {
                        // `Π`-case filling (see `crate::kan`'s "Phase 3.6" doc):
                        // matched *syntactically* on the raw family (no `whnf`),
                        // deliberately mirroring the regularity rule's own
                        // structural-only convention just above — a family that
                        // only *reduces* to a `Π` (e.g. behind a `Let`/`Const`)
                        // stays stuck, exactly as a family that only reduces to
                        // being interval-constant does for the regularity rule.
                        head = crate::kan::transp_pi_rule(dom, cod, a);
                    } else {
                        // Parametrized-inductive filling (see `crate::kan`'s
                        // "Phase 3.10" doc): matched *syntactically* (no `whnf`)
                        // on both the family and the argument, mirroring every
                        // other rule in this arm. Only fires when the family is
                        // headed by a non-indexed user inductive with exactly one
                        // varying parameter and the argument is a literal
                        // fully-applied constructor of matching shape.
                        match crate::kan::transp_inductive_rule(self.env, fam, a) {
                            Some(built) => head = built,
                            None => break,
                        }
                    }
                }
                // `hcomp` (see `crate::kan`): the **trivial-system rule** — when `φ`
                // is decided `⊤`, the composite is just the system's value at `i1`
                // (the cap coherence, `u(i0) ≡ u0`, was already enforced at
                // check-time — see `Checker::infer`'s `Term::HComp` arm). Otherwise
                // stuck.
                Term::HComp(ty, phi, u, u0) => {
                    if crate::face::is_true(phi) {
                        head = u.instantiate(&Term::IOne);
                    } else if let Term::Pi(_g, dom, cod) = ty.as_ref() {
                        // `Π`-case filling (see `crate::kan`'s "Phase 3.7" doc):
                        // matched *syntactically* on the raw type (no `whnf`),
                        // mirroring `transp`'s own structural-only convention; only
                        // fires when `u` is itself a literal `Sys` (see
                        // `crate::kan::hcomp_pi_rule`'s doc for why).
                        match crate::kan::hcomp_pi_rule(dom, cod, phi, u, u0) {
                            Some(built) => head = built,
                            None => break,
                        }
                    } else if let Term::PathP(fam, a0, a1) = ty.as_ref() {
                        // `PathP`-case filling (see `crate::kan`'s "Phase 3.9" doc):
                        // matched *syntactically* on the raw type (no `whnf`),
                        // mirroring the `Π` case's own structural-only convention;
                        // only fires when `u` is itself a literal `Sys` (see
                        // `crate::kan::hcomp_pathp_rule`'s doc for why).
                        match crate::kan::hcomp_pathp_rule(fam, a0, a1, phi, u, u0) {
                            Some(built) => head = built,
                            None => break,
                        }
                    } else {
                        // Constructor-compatible `hcomp` for a user inductive
                        // (see `crate::kan`'s "Phase 3.11" doc): matched
                        // *syntactically* (no `whnf`) on `ty`/`u`/`u0`; only
                        // fires when `u` is a literal `Sys` whose every branch,
                        // and `u0`, are the *same* constructor applied.
                        match crate::kan::hcomp_inductive_rule(self.env, ty, phi, u, u0) {
                            Some(built) => head = built,
                            None => break,
                        }
                    }
                }
                // `Glue A [φ_1 ↦ (T_1,e_1), …]` (see `crate::term::Term::Glue`): the
                // two strictness laws, generalized to `n` branches — the *first*
                // branch whose `φ_k` is decided `⊤` reduces to `T_k` (CCHM's defining
                // strictness property; compatible branches agree wherever more than
                // one fires, so "first" is a sound, arbitrary tie-break); if *every*
                // `φ_k` is decided `⊥`, reduces to plain `A`, mirroring `Term::Sys`'s
                // "fire once decided" convention. Otherwise stuck — a valid normal
                // form, exactly like a stuck `Sys`/`HComp`.
                Term::Glue(a, branches) => {
                    if let Some((_, t, _)) = branches.iter().find(|(phi, _, _)| crate::face::is_true(phi)) {
                        head = (**t).clone();
                    } else if branches.iter().all(|(phi, _, _)| crate::face::is_false(phi)) {
                        head = (**a).clone();
                    } else {
                        break;
                    }
                }
                // `unglue A [φ_1 ↦ (T_1,e_1), …] u` (see `crate::term::Term::Unglue`):
                // on a decided `⊤` face, `unglue` is that branch's `e_k.f`; off every
                // face (all decided `⊥`), `unglue` is the identity; otherwise stuck.
                Term::Unglue(a, branches, u) => {
                    // β: `unglue A […] (glue […] a) ↦ a` (see
                    // `crate::term::Term::GlueIntro`'s doc) — checked *before* the
                    // ⊤/⊥ strictness rules below, since this fires unconditionally
                    // once the scrutinee is literally a `glue` introduction,
                    // regardless of whether any face happens to be decided.
                    let uw = self.whnf(u);
                    if let Term::GlueIntro(_, ga) = &uw {
                        head = (**ga).clone();
                        continue;
                    }
                    if let Some((_, t, e)) = branches.iter().find(|(phi, _, _)| crate::face::is_true(phi)) {
                        // `Equiv.f T A e u` — the level argument is a genuine
                        // universe-polymorphism parameter of `Equiv.f`'s *type*
                        // only; its declared *value* (see `crate::equiv`'s
                        // `declare_equiv_projections`) never inspects the level at
                        // all (it just unpacks `e`'s `f` field via `Equiv.rec`'s
                        // ι-rule), so any placeholder level reduces to the same
                        // normal form here — untyped `whnf` has no sort available
                        // to plug in the "real" one.
                        let ef = crate::term::Term::apps(
                            crate::term::Term::cnst(
                                crate::term::name("Equiv.f"),
                                vec![crate::level::Level::of_nat(0)],
                            ),
                            [(**t).clone(), (**a).clone(), (**e).clone(), (**u).clone()],
                        );
                        let (h, mut a2) = ef.unfold_apps();
                        a2.extend(args);
                        head = h;
                        args = a2;
                    } else if branches.iter().all(|(phi, _, _)| crate::face::is_false(phi)) {
                        head = (**u).clone();
                    } else {
                        break;
                    }
                }
                // `glue [φ_1 ↦ t_1, …] a` (see `crate::term::Term::GlueIntro`): the
                // same two strictness laws as `Glue` itself (mirroring `Value`'s
                // "collapse when a face is decided" convention) — the *first*
                // branch whose `φ_k` is decided `⊤` reduces to `t_k`; if *every*
                // `φ_k` is decided `⊥`, reduces to plain `a`. Otherwise stuck.
                Term::GlueIntro(branches, a) => {
                    if let Some((_, t)) = branches.iter().find(|(phi, _)| crate::face::is_true(phi)) {
                        head = (**t).clone();
                    } else if branches.iter().all(|(phi, _)| crate::face::is_false(phi)) {
                        head = (**a).clone();
                    } else {
                        break;
                    }
                }
                // Sort, Var, Pi, I/IZero/IOne, PLam, PathP, Partial, or a stuck Const:
                // weak-head normal.
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

    /// Try the interval-HIT (`I2`) computation rules (see [`crate::interval_hit`]) —
    /// the **computing** dependent recursor `I2.rec.{v} C c0 c1 s x`. Spine positions:
    /// `C`@0, `c0`@1, `c1`@2, `s`@3, scrutinee `x`@4. Three ι-rules:
    ///
    /// ```text
    ///   I2.rec C c0 c1 s I2.zero        ↦  c0
    ///   I2.rec C c0 c1 s I2.one         ↦  c1
    ///   I2.rec C c0 c1 s (I2.seg @ r)   ↦  s @ r
    /// ```
    ///
    /// The first two mirror [`Self::try_circle_rec`]'s point rule (just doubled for
    /// two point constructors). The third is new: it fires when the scrutinee's
    /// weak-head form is *literally* a [`Term::PApp`] whose head weak-head-reduces to
    /// the nullary `I2.seg` constant — never on a bare neutral, never on an unrelated
    /// `PathP`-typed application (guarded by checking the `PApp` head is specifically
    /// `I2.seg`), and never confused with the point rules (a `PApp` node is never a
    /// `Term::Const` head, so `unfold_apps` can't route it into the point-rule match
    /// arm by accident). Returns `None` (stuck/neutral) when not yet saturated to the
    /// scrutinee or the scrutinee matches none of the three shapes.
    fn try_i2_rec(&self, args: &[Term]) -> Option<Term> {
        const C0_POS: usize = 1;
        const C1_POS: usize = 2;
        const S_POS: usize = 3;
        const SCRUT_POS: usize = 4;
        if args.len() <= SCRUT_POS {
            return None; // not yet applied to the I2 value
        }
        let scrut = self.whnf(&args[SCRUT_POS]);
        // Point rules: scrutinee weak-head-reduces to a literal, nullary `I2.zero` or
        // `I2.one`.
        let (pt_head, pt_args) = scrut.unfold_apps();
        if let Term::Const(pt_name, _) = &pt_head {
            let role = match self.env.get(pt_name) {
                Some(Decl::I2(c)) => Some(c.role),
                _ => None,
            };
            match role {
                Some(I2Role::Zero) if pt_args.is_empty() => {
                    let mut applied = args[C0_POS].clone();
                    for extra in &args[SCRUT_POS + 1..] {
                        applied = Term::app(applied, extra.clone());
                    }
                    return Some(applied);
                }
                Some(I2Role::One) if pt_args.is_empty() => {
                    let mut applied = args[C1_POS].clone();
                    for extra in &args[SCRUT_POS + 1..] {
                        applied = Term::app(applied, extra.clone());
                    }
                    return Some(applied);
                }
                _ => {}
            }
        }
        // Path rule: scrutinee is (weak-head) `PApp(p, r)` with `p`'s own weak-head
        // form the literal, nullary `I2.seg`.
        if let Term::PApp(p, r) = &scrut {
            let p_whnf = self.whnf(p);
            let (seg_head, seg_args) = p_whnf.unfold_apps();
            if let Term::Const(seg_name, _) = &seg_head {
                if matches!(self.env.get(seg_name), Some(Decl::I2(c)) if c.role == I2Role::Seg)
                    && seg_args.is_empty()
                {
                    let s = &args[S_POS];
                    let mut applied = Term::papp(s.clone(), (**r).clone());
                    for extra in &args[SCRUT_POS + 1..] {
                        applied = Term::app(applied, extra.clone());
                    }
                    return Some(applied);
                }
            }
        }
        None
    }

    /// Try the cubical-circle (`S1c`) computation rules (see
    /// [`crate::circle_cubical`]) — the **computing** dependent recursor
    /// `S1c.rec.{v} C b l x`. Spine positions: `C`@0, `b`@1, `l`@2, scrutinee `x`@3.
    /// Two ι-rules:
    ///
    /// ```text
    ///   S1c.rec C b l S1c.base        ↦  b
    ///   S1c.rec C b l (S1c.loop @ r)  ↦  l @ r
    /// ```
    ///
    /// Structurally identical to [`Self::try_i2_rec`] (one point constructor instead
    /// of two, one path constructor whose two endpoints happen to *both* be `base` —
    /// see [`crate::circle_cubical`]'s "Endpoint coherence, both ends" for why that
    /// self-loop shape doesn't need any different reduction logic here: the rule
    /// still only ever inspects `r`, never the path's endpoints). Returns `None`
    /// (stuck/neutral) when not yet saturated to the scrutinee or the scrutinee
    /// matches neither shape.
    fn try_s1c_rec(&self, args: &[Term]) -> Option<Term> {
        const B_POS: usize = 1;
        const L_POS: usize = 2;
        const SCRUT_POS: usize = 3;
        if args.len() <= SCRUT_POS {
            return None; // not yet applied to the S1c value
        }
        let scrut = self.whnf(&args[SCRUT_POS]);
        // Point rule: scrutinee weak-head-reduces to a literal, nullary `S1c.base`.
        let (pt_head, pt_args) = scrut.unfold_apps();
        if let Term::Const(pt_name, _) = &pt_head {
            if matches!(self.env.get(pt_name), Some(Decl::S1c(c)) if c.role == S1cRole::Base)
                && pt_args.is_empty()
            {
                let mut applied = args[B_POS].clone();
                for extra in &args[SCRUT_POS + 1..] {
                    applied = Term::app(applied, extra.clone());
                }
                return Some(applied);
            }
        }
        // Path rule: scrutinee is (weak-head) `PApp(p, r)` with `p`'s own weak-head
        // form the literal, nullary `S1c.loop`.
        if let Term::PApp(p, r) = &scrut {
            let p_whnf = self.whnf(p);
            let (loop_head, loop_args) = p_whnf.unfold_apps();
            if let Term::Const(loop_name, _) = &loop_head {
                if matches!(self.env.get(loop_name), Some(Decl::S1c(c)) if c.role == S1cRole::Loop)
                    && loop_args.is_empty()
                {
                    let l = &args[L_POS];
                    let mut applied = Term::papp(l.clone(), (**r).clone());
                    for extra in &args[SCRUT_POS + 1..] {
                        applied = Term::app(applied, extra.clone());
                    }
                    return Some(applied);
                }
            }
        }
        None
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
            // Phase 3.5 (De Morgan interval, see `crate::cubical`): see the matching
            // arm in `check::Checker::compare` for the rationale (kept in lockstep
            // between the two independent conversion checkers) — only fires when a
            // genuine connective head is present, so plain `Var`/`Var` comparisons are
            // untouched (this checker has no proof-irrelevance/η-for-Path fallback to
            // preserve, but keeping the two implementations structurally identical is
            // what the differential tests below check).
            (Term::INeg(..) | Term::IMeet(..) | Term::IJoin(..), _)
            | (_, Term::INeg(..) | Term::IMeet(..) | Term::IJoin(..))
                if crate::cubical::is_interval_expr(&a) && crate::cubical::is_interval_expr(&b) =>
            {
                crate::cubical::interval_eq(&a, &b)
            }
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
            // Phase-1 cubical (see `crate::cubical`): structural, no Path-specific η.
            (Term::I, Term::I) | (Term::IZero, Term::IZero) | (Term::IOne, Term::IOne) => true,
            (Term::PLam(b1), Term::PLam(b2)) => self.is_def_eq(b1, b2),
            (Term::PApp(p1, r1), Term::PApp(p2, r2)) => {
                self.is_def_eq(p1, p2) && self.is_def_eq(r1, r2)
            }
            (Term::PathP(f1, a01, a11), Term::PathP(f2, a02, a12)) => {
                self.is_def_eq(f1, f2) && self.is_def_eq(a01, a02) && self.is_def_eq(a11, a12)
            }
            // Phase-2 cubical (see `crate::face`): mirrors `check::Checker::compare`'s
            // `Partial`/`Sys` cases (this lower-level reducer stays structural, no
            // proof irrelevance/context — cofibration comparison is via semantic
            // equivalence, which is already context-free).
            (Term::Partial(p1, a1), Term::Partial(p2, a2)) => {
                crate::face::cof_equiv(p1, p2) && self.is_def_eq(a1, a2)
            }
            (Term::Sys(b1), Term::Sys(b2)) => {
                b1.len() == b2.len()
                    && b1.iter().zip(b2).all(|((p1, t1), (p2, t2))| {
                        crate::face::cof_equiv(p1, p2) && self.is_def_eq(t1, t2)
                    })
            }
            // Phase-3 cubical (see `crate::kan`): structural, mirrors `PathP`/`Sys`.
            (Term::Transp(f1, p1, a1), Term::Transp(f2, p2, a2)) => {
                self.is_def_eq(f1, f2) && crate::face::cof_equiv(p1, p2) && self.is_def_eq(a1, a2)
            }
            (Term::HComp(t1, p1, u1, u01), Term::HComp(t2, p2, u2, u02)) => {
                self.is_def_eq(t1, t2)
                    && crate::face::cof_equiv(p1, p2)
                    && self.is_def_eq(u1, u2)
                    && self.is_def_eq(u01, u02)
            }
            // `glue [φ ↦ t, …] a` (see `crate::term::Term::GlueIntro`): structural,
            // mirroring `Sys`/`Transp`/`HComp` above (this lower-level reducer has
            // no `Glue`/`Unglue` structural-equality arm of its own either — see
            // `check::Checker::compare`, the authoritative conversion relation
            // used by the type-checker, for the complete treatment).
            (Term::GlueIntro(b1, a1), Term::GlueIntro(b2, a2)) => {
                self.is_def_eq(a1, a2)
                    && b1.len() == b2.len()
                    && b1.iter().zip(b2.iter()).all(|((p1, t1), (p2, t2))| {
                        crate::face::cof_equiv(p1, p2) && self.is_def_eq(t1, t2)
                    })
            }
            _ => false,
        }
    }
}
