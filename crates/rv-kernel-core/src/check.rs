//! The trusted type-checker: `infer` a term's type, or `check` it against an
//! expected type, in a local context.
//!
//! This and the [reducer](crate::reduce) are the soundness-critical core. The rules
//! are the standard dependent-type-theory ones:
//!
//! * `Sort u : Sort (u+1)`
//! * a variable's type comes from the context (re-indexed for its de Bruijn depth),
//! * a constant's type is its declaration's type at the supplied universe arguments,
//! * application requires a `Π` and substitutes the argument into the codomain,
//! * `λ` introduces a `Π`,
//! * `Π` is well-formed when domain and codomain are sorts, and itself inhabits
//!   `Sort (imax u v)` — the **impredicative** product rule, which makes `Prop`
//!   (`Sort 0`) impredicative.
//!
//! The local context is a stack of binder types. `ctx[k]` is the type of the binder
//! introduced `k`-th from the outside; a `Var(i)` refers to the binder `i+1` levels
//! in, so its type is read from the top of the stack and lifted to the current depth.

use crate::env::Env;
use crate::face::{self, Atom, Cof};
use crate::level::{self, Level};
use crate::reduce::Reducer;
use crate::term::Term;
use std::rc::Rc;

/// A local typing context: a stack of binder types (innermost last).
#[derive(Clone, Debug, Default)]
pub struct LocalCtx {
    types: Vec<Term>,
}

impl LocalCtx {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        self.types.len()
    }
    pub fn is_empty(&self) -> bool {
        self.types.is_empty()
    }
    /// The type of `Var(i)`, re-indexed into the current context.
    pub fn var_type(&self, i: usize) -> Option<Term> {
        let n = self.types.len();
        if i >= n {
            return None;
        }
        // The binder for `Var(i)` was recorded `i+1` levels shallower; lift its type
        // so its own free variables stay valid here.
        Some(self.types[n - 1 - i].lift(i as isize + 1, 0))
    }
    /// Push `ty` as a fresh innermost binder (the caller manages the matching pop, or
    /// discards the context). Used to assemble a telescope's context for sort-checking.
    pub fn push(&mut self, ty: Term) {
        self.types.push(ty);
    }

    /// Run `f` with `ty` pushed as a fresh innermost binder.
    fn with<R>(&mut self, ty: Term, f: impl FnOnce(&mut Self) -> R) -> R {
        self.types.push(ty);
        let r = f(self);
        self.types.pop();
        r
    }
}

/// The type-checker, bound to an environment.
pub struct Checker<'e> {
    env: &'e Env,
}

impl<'e> Checker<'e> {
    pub fn new(env: &'e Env) -> Self {
        Self { env }
    }

    fn reducer(&self) -> Reducer<'e> {
        Reducer::new(self.env)
    }

    /// Infer the type of `t` in `ctx`, or return a diagnostic.
    pub fn infer(&self, ctx: &mut LocalCtx, t: &Term) -> Result<Term, String> {
        match t {
            Term::Meta(m) => Err(format!("unsolved metavariable ?{m} reached the kernel")),
            Term::Sort(l) => Ok(Term::Sort(Level::succ(l.clone()))),
            Term::Var(i) => {
                ctx.var_type(*i).ok_or_else(|| format!("unbound de Bruijn index {i}"))
            }
            Term::Const(n, ls) => {
                let decl = self
                    .env
                    .get(n)
                    .ok_or_else(|| format!("unknown constant '{n}'"))?;
                if ls.len() as u32 != decl.num_levels() {
                    return Err(format!(
                        "'{n}' expects {} universe argument(s), got {}",
                        decl.num_levels(),
                        ls.len()
                    ));
                }
                Ok(decl.ty().instantiate_levels(ls))
            }
            Term::App(f, a) => {
                let tf = self.infer(ctx, f)?;
                let tf = self.reducer().whnf(&tf);
                let Term::Pi(_, dom, cod) = &tf else {
                    return Err(format!("cannot apply: head is not a function, has type {tf:?}"));
                };
                self.check(ctx, a, dom)?;
                Ok(cod.instantiate(a))
            }
            Term::Lam(dom, body) => {
                // The domain must be a type.
                self.infer_sort(ctx, dom)?;
                let tbody = ctx.with((**dom).clone(), |c| self.infer(c, body))?;
                Ok(Term::pi((**dom).clone(), tbody))
            }
            Term::Pi(_, dom, cod) => {
                let s1 = self.infer_sort(ctx, dom)?;
                let s2 = ctx.with((**dom).clone(), |c| self.infer_sort(c, cod))?;
                // Impredicative product rule.
                Ok(Term::Sort(Level::imax(s1, s2)))
            }
            Term::Let(_, ty, value, body) => {
                self.infer_sort(ctx, ty)?;
                self.check(ctx, value, ty)?;
                let tbody = ctx.with((**ty).clone(), |c| self.infer(c, body))?;
                // The body's type may mention the let-bound variable; substitute the
                // value to eliminate the now-departing binder.
                Ok(tbody.instantiate(value))
            }

            // ---- Phase-1 cubical (see `crate::cubical`) ----

            // `I` is a phantom classifier, not itself a checkable value/type: this is
            // exactly what makes it "not fibrant" — nothing can quantify a real Type
            // over it (a `Π (i : I). _` domain would have to `infer` to a `Sort`, and
            // this errors instead), and no closed term of "type `I`" other than the
            // two literal endpoints or a bound interval variable can be built.
            Term::I => Err("`I` (the interval) is not itself a type or a value".to_string()),
            Term::IZero | Term::IOne => Ok(Term::I),

            // **Phase 3.5** (De Morgan interval, see `crate::cubical`): reversal and
            // the two connections. Each operand must itself check against `I`
            // (exactly like `Term::PApp`'s argument); the result is again `I` — these
            // are interval-*expressions*, not fibrant data, so they can no more
            // escape into a `Π` domain/codomain than `IZero`/`IOne` can (see
            // `interval_still_cannot_be_a_pi_domain_with_connections_in_scope` below).
            Term::INeg(r) => {
                let tr = self.infer(ctx, r)?;
                if !self.is_def_eq(ctx, &tr, &Term::I) {
                    return Err(format!("`~r` requires `r : I`, got {tr:?}"));
                }
                Ok(Term::I)
            }
            Term::IMeet(r, s) | Term::IJoin(r, s) => {
                let tr = self.infer(ctx, r)?;
                if !self.is_def_eq(ctx, &tr, &Term::I) {
                    return Err(format!("interval connection requires `r : I`, got {tr:?}"));
                }
                let ts = self.infer(ctx, s)?;
                if !self.is_def_eq(ctx, &ts, &Term::I) {
                    return Err(format!("interval connection requires `s : I`, got {ts:?}"));
                }
                Ok(Term::I)
            }

            // Path abstraction: `⟨i⟩ body` has type `PathP (λi. type-of body) body[i:=i0] body[i:=i1]`.
            // Reuses the ordinary `Var` binder machinery (see `Term::PLam`'s doc
            // comment) — push `I` as the new binder's "type" so `is_interval_var`
            // recognizes it, then `instantiate` (the same substitution `Lam`/`Pi` use)
            // computes the two endpoints.
            Term::PLam(body) => {
                let tbody = ctx.with(Term::I, |c| self.infer(c, body))?;
                let a0 = body.instantiate(&Term::IZero);
                let a1 = body.instantiate(&Term::IOne);
                Ok(Term::pathp(tbody, a0, a1))
            }

            // Path application `p @ r`: `r` must itself check against `I` (so, in a
            // well-typed term, `r` is `IZero`, `IOne`, or a bound interval variable —
            // nothing else can have inferred type `I`, since `I` is rejected as a `Π`
            // domain/codomain and thus no function can return it either). The result
            // type is the family instantiated at `r` — definitionally equal to the
            // declared endpoint when `r` is `IZero`/`IOne` (the boundary equations,
            // enforced by `PathP`'s well-formedness check below, not by this rule).
            Term::PApp(p, r) => {
                let tr = self.infer(ctx, r)?;
                if !self.is_def_eq(ctx, &tr, &Term::I) {
                    return Err(format!(
                        "path application argument must be an interval term (: I), got type {}",
                        tr.pretty()
                    ));
                }
                let tp = self.infer(ctx, p)?;
                let tp = self.reducer().whnf(&tp);
                let Term::PathP(fam, _, _) = &tp else {
                    return Err(format!(
                        "path application: head is not a Path/PathP, has type {}",
                        tp.pretty()
                    ));
                };
                Ok(fam.instantiate(r))
            }

            // `PathP (λi. family) a0 a1` is itself a type: check the family is a type
            // under an interval binder, and its two endpoints match the family
            // instantiated at `i0`/`i1` (up to conversion — the boundary condition).
            Term::PathP(fam, a0, a1) => {
                let sort = ctx.with(Term::I, |c| self.infer_sort(c, fam))?;
                self.check(ctx, a0, &fam.instantiate(&Term::IZero))?;
                self.check(ctx, a1, &fam.instantiate(&Term::IOne))?;
                Ok(Term::Sort(sort))
            }

            // ---- Phase-2 cubical: cofibrations and partial elements (see `crate::face`) ----

            // `Partial φ A`: well-formed when `A` is a type and every atom subject in
            // `φ` is genuinely interval-classified (`: I`) — this keeps a cofibration
            // from smuggling arbitrary ill-typed data through an atom's subject
            // position (mirrors `Term::PApp`'s check that its interval argument has
            // type `I`). Lives in the same sort as `A`.
            Term::Partial(phi, a) => {
                self.check_cof_wellformed(ctx, phi)?;
                let s = self.infer_sort(ctx, a)?;
                Ok(Term::Sort(s))
            }

            // A system has no type of its own to *infer* — it only makes sense
            // relative to an expected `Partial ψ A` (which supplies both `A` and the
            // coverage obligation). See `Checker::check`'s `Term::Sys` special case.
            Term::Sys(_) => Err(
                "cannot infer the type of a system [φ ↦ t, …]; check it against `Partial φ A`"
                    .to_string(),
            ),

            // ---- Phase-3 cubical: the minimal sound Kan core (see `crate::kan`) ----

            // `transp (λi. family) φ a : family[i:=i1]`, given `a : family[i:=i0]`.
            // `φ`'s well-formedness is checked (so it stays a genuine cofibration
            // over in-scope interval variables), but — per `crate::kan` — it is
            // never trusted for the *reduction* rule; only structural constancy is.
            Term::Transp(fam, phi, a) => {
                ctx.with(Term::I, |c| self.infer_sort(c, fam))?;
                self.check_cof_wellformed(ctx, phi)?;
                self.check(ctx, a, &fam.instantiate(&Term::IZero))?;
                Ok(fam.instantiate(&Term::IOne))
            }

            // `hcomp A φ u u0 : A`, given `u : (i:I) -> Partial φ A` and `u0 : A`
            // with `u`'s cap at `i0` required to agree with `u0` (see `crate::kan`
            // for why this is checked unconditionally, not only when `φ` holds).
            Term::HComp(ty, phi, u, u0) => {
                self.infer_sort(ctx, ty)?;
                self.check_cof_wellformed(ctx, phi)?;
                let partial_ty = Term::partial((**phi).clone(), (**ty).clone());
                ctx.with(Term::I, |c| {
                    self.check(c, u, &partial_ty.lift(1, 0))
                })?;
                self.check(ctx, u0, ty)?;
                let cap = u.instantiate(&Term::IZero);
                if !self.is_def_eq(ctx, &cap, u0) {
                    return Err(
                        "hcomp: the system's cap at i0 does not match u0".to_string(),
                    );
                }
                Ok((**ty).clone())
            }

            // `Glue A [φ_1 ↦ (T_1,e_1), …] : Sort u`, given `A, T_k : Sort u` (same
            // universe for every branch — see `Term::Glue`'s doc) and each
            // `e_k : Equiv T_k A` (a *total*, not merely `φ_k`-partial,
            // equivalence). Requires the branch list to be non-empty (an empty
            // `Glue` would be `Glue A []`, which is just `A` — reject rather than
            // silently permit a degenerate encoding), and every pair of branches
            // to be **compatible on their overlap** (see `Term::Glue`'s doc and
            // `check_sys`'s own compatibility loop, which this mirrors exactly).
            Term::Glue(a, branches) => {
                if branches.is_empty() {
                    return Err("Glue: the branch list [φ ↦ (T,e), …] must be non-empty".to_string());
                }
                let sort_a = self.infer_sort(ctx, a)?;
                for (phi, t, e) in branches.iter() {
                    self.check_cof_wellformed(ctx, phi)?;
                    let sort_t = self.infer_sort(ctx, t)?;
                    if !level::equiv(&sort_a, &sort_t) {
                        return Err(format!(
                            "Glue: every branch's T and the base type A must live in the same \
                             universe (got T : Sort {sort_t:?}, A : Sort {sort_a:?})"
                        ));
                    }
                    let equiv_ty = Term::apps(
                        Term::cnst(crate::term::name("Equiv"), vec![sort_a.clone()]),
                        [(**t).clone(), (**a).clone()],
                    );
                    self.check(ctx, e, &equiv_ty)?;
                }
                self.check_glue_branches_compatible(ctx, branches)?;
                Ok(Term::Sort(sort_a))
            }
            // `unglue A [φ_1 ↦ (T_1,e_1), …] u : A` — same branch obligations as
            // `Glue` (this is its elimination form: `u` must inhabit the `Glue`
            // type built from exactly these branches), plus `u : Glue A […]`.
            Term::Unglue(a, branches, u) => {
                if branches.is_empty() {
                    return Err("unglue: the branch list [φ ↦ (T,e), …] must be non-empty".to_string());
                }
                let sort_a = self.infer_sort(ctx, a)?;
                for (phi, t, e) in branches.iter() {
                    self.check_cof_wellformed(ctx, phi)?;
                    let sort_t = self.infer_sort(ctx, t)?;
                    if !level::equiv(&sort_a, &sort_t) {
                        return Err(format!(
                            "unglue: every branch's T and the base type A must live in the same \
                             universe (got T : Sort {sort_t:?}, A : Sort {sort_a:?})"
                        ));
                    }
                    let equiv_ty = Term::apps(
                        Term::cnst(crate::term::name("Equiv"), vec![sort_a.clone()]),
                        [(**t).clone(), (**a).clone()],
                    );
                    self.check(ctx, e, &equiv_ty)?;
                }
                self.check_glue_branches_compatible(ctx, branches)?;
                let glue_ty = Term::Glue((*a).clone(), branches.clone());
                self.check(ctx, u, &glue_ty)?;
                Ok((**a).clone())
            }

            // `glue [φ ↦ t, …] a` (see `Term::GlueIntro`) is check-only, exactly
            // like `Term::Sys` — it needs an expected `Glue A […]` to know each
            // branch's `T_k`/`e_k`. See `Checker::check`'s special case and
            // `Checker::check_glue_intro`.
            Term::GlueIntro(..) => Err(
                "cannot infer the type of `glue [φ ↦ t, …] a`; check it against a `Glue A [...]` type"
                    .to_string(),
            ),
        }
    }

    /// The compatibility obligation shared by [`Term::Glue`] and [`Term::Unglue`]:
    /// on any overlap `φ_i ∧ φ_j` (`i≠j`) that isn't `⊥`, `T_i ≡ T_j` and
    /// `e_i ≡ e_j` **under restriction to the overlap** — exactly `check_sys`'s
    /// compatibility loop (see its doc for the full soundness argument), applied
    /// to `(T,e)` pairs instead of a single branch term.
    fn check_glue_branches_compatible(
        &self,
        ctx: &mut LocalCtx,
        branches: &[(Rc<Cof>, Rc<Term>, Rc<Term>)],
    ) -> Result<(), String> {
        for i in 0..branches.len() {
            for j in (i + 1)..branches.len() {
                let overlap = Cof::and((*branches[i].0).clone(), (*branches[j].0).clone());
                if face::is_false(&overlap) {
                    continue;
                }
                for clause in face::overlap_clauses(&branches[i].0, &branches[j].0) {
                    let ti = face::restrict_clause_term(&clause, &branches[i].1);
                    let tj = face::restrict_clause_term(&clause, &branches[j].1);
                    if !self.is_def_eq(ctx, &ti, &tj) {
                        return Err(format!(
                            "incompatible Glue: branches {i} and {j} disagree on their overlapping T \
                             (φ_{i} ∧ φ_{j} is satisfiable, but the branch types are not definitionally \
                             equal after restricting to the overlapping face)"
                        ));
                    }
                    let ei = face::restrict_clause_term(&clause, &branches[i].2);
                    let ej = face::restrict_clause_term(&clause, &branches[j].2);
                    if !self.is_def_eq(ctx, &ei, &ej) {
                        return Err(format!(
                            "incompatible Glue: branches {i} and {j} disagree on their overlapping e \
                             (φ_{i} ∧ φ_{j} is satisfiable, but the branch equivalences are not \
                             definitionally equal after restricting to the overlapping face)"
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    /// Check `glue [φ_1↦t_1, …] a` (see [`crate::term::Term::GlueIntro`]) against
    /// an expected `Glue A [φ_1↦(T_1,e_1), …]` type. Four obligations, in order:
    ///
    /// 1. **Shape match**: same number of branches, each `φ_k` here semantically
    ///    the same cofibration as the Glue type's `φ_k` (index-for-index — see
    ///    `Term::GlueIntro`'s doc for why this kernel doesn't attempt to permute
    ///    or re-derive a correspondence), and `t_k : T_k`.
    /// 2. **Mutual compatibility** of the `t_k` on their overlaps — the same
    ///    restriction-aware condition [`Self::check_glue_branches_compatible`]
    ///    already imposes on `Glue`'s own `(T,e)` pairs, here applied to the
    ///    `t_k` payloads (reusing the Glue type's own guards, already confirmed
    ///    equivalent to this term's guards by step 1).
    /// 3. `a : A`.
    /// 4. **Agreement**: on each `φ_k` (restriction-aware, exactly like step 2 —
    ///    a face that's unconditionally `⊥` imposes no obligation, since
    ///    `overlap_clauses(φ_k, ⊤) = to_dnf(φ_k)` is then empty),
    ///    `Equiv.f T_k A e_k t_k ≡ a`: the glued partial data must map to the
    ///    base under the equivalence wherever it's defined. This is the one
    ///    obligation with no `Glue`-type analogue — it's what makes `glue`
    ///    genuinely introduce an element of `Glue A […]`, not just restate its
    ///    formation data.
    fn check_glue_intro(
        &self,
        ctx: &mut LocalCtx,
        branches: &[(Rc<Cof>, Rc<Term>)],
        a: &Term,
        expected: &Term,
    ) -> Result<(), String> {
        let expected_w = self.reducer().whnf(expected);
        let Term::Glue(base_ty, glue_branches) = &expected_w else {
            return Err(format!(
                "`glue [φ ↦ t, …] a` must be checked against a `Glue A [...]` type, got {}",
                expected_w.pretty()
            ));
        };
        if branches.len() != glue_branches.len() {
            return Err(format!(
                "glue: branch count mismatch (term has {}, the Glue type has {})",
                branches.len(),
                glue_branches.len()
            ));
        }
        let sort_a = self.infer_sort(ctx, base_ty)?;

        // Step 1: shape match + per-branch typing.
        for (i, ((phi, t), (gphi, gt, _ge))) in branches.iter().zip(glue_branches.iter()).enumerate() {
            self.check_cof_wellformed(ctx, phi)?;
            if !face::cof_equiv(phi, gphi) {
                return Err(format!(
                    "glue: branch {i}'s cofibration does not match the Glue type's corresponding branch"
                ));
            }
            self.check(ctx, t, gt)?;
        }

        // Step 2: mutual compatibility of the t_k on overlaps (reuse the Glue
        // type's own guards — already confirmed cof_equiv to this term's own,
        // above).
        for i in 0..branches.len() {
            for j in (i + 1)..branches.len() {
                let overlap = Cof::and((*glue_branches[i].0).clone(), (*glue_branches[j].0).clone());
                if face::is_false(&overlap) {
                    continue;
                }
                for clause in face::overlap_clauses(&glue_branches[i].0, &glue_branches[j].0) {
                    let ti = face::restrict_clause_term(&clause, &branches[i].1);
                    let tj = face::restrict_clause_term(&clause, &branches[j].1);
                    if !self.is_def_eq(ctx, &ti, &tj) {
                        return Err(format!(
                            "incompatible glue: branches {i} and {j} disagree on their overlap \
                             (φ_{i} ∧ φ_{j} is satisfiable, but the branch terms are not \
                             definitionally equal after restricting to the overlapping face)"
                        ));
                    }
                }
            }
        }

        // Step 3: the base.
        self.check(ctx, a, base_ty)?;

        // Step 4: agreement — on φ_k, Equiv.f T_k A e_k t_k ≡ a, restriction-aware.
        for (i, ((_phi, t), (gphi, gt, ge))) in branches.iter().zip(glue_branches.iter()).enumerate() {
            let clauses = face::overlap_clauses(gphi, &Cof::top());
            if clauses.is_empty() {
                continue; // φ_k unsatisfiable: vacuous, nothing to check
            }
            let ef = Term::apps(
                Term::cnst(crate::term::name("Equiv.f"), vec![sort_a.clone()]),
                [(**gt).clone(), (**base_ty).clone(), (**ge).clone(), (**t).clone()],
            );
            for clause in clauses {
                let lhs = face::restrict_clause_term(&clause, &ef);
                let rhs = face::restrict_clause_term(&clause, a);
                if !self.is_def_eq(ctx, &lhs, &rhs) {
                    return Err(format!(
                        "glue: branch {i} does not agree with the base `a` under `Equiv.f` on its \
                         face φ_{i} (Equiv.f T_{i} A e_{i} t_{i} ≢ a after restricting to the face)"
                    ));
                }
            }
        }

        Ok(())
    }

    /// Check that a cofibration's every atom subject is genuinely interval-classified.
    fn check_cof_wellformed(&self, ctx: &mut LocalCtx, phi: &Cof) -> Result<(), String> {
        match phi {
            Cof::Bot | Cof::Top => Ok(()),
            Cof::Atom(Atom::Eq0(t)) | Cof::Atom(Atom::Eq1(t)) => {
                let tt = self.infer(ctx, t)?;
                if self.is_def_eq(ctx, &tt, &Term::I) {
                    Ok(())
                } else {
                    Err(format!(
                        "cofibration atom's subject must be an interval term (: I), got {}",
                        tt.pretty()
                    ))
                }
            }
            Cof::And(a, b) | Cof::Or(a, b) => {
                self.check_cof_wellformed(ctx, a)?;
                self.check_cof_wellformed(ctx, b)
            }
        }
    }

    /// Check a system `[φ_1 ↦ t_1, …, φ_n ↦ t_n]` against an expected `Partial ψ A`:
    /// coverage (`ψ ⊢ φ_1 ∨ … ∨ φ_n`), each branch at `A`, and the **compatibility
    /// condition** (see `crate::face`'s module doc, and [`face::restrict_clause_term`]'s
    /// doc for the full soundness argument) — on any overlap `φ_i ∧ φ_j` that isn't
    /// `⊥`, `t_i` and `t_j` must agree **under restriction to the overlap**: for
    /// every clause `C` of `to_dnf(φ_i ∧ φ_j)` (each clause pins a finite set of
    /// already-in-scope interval variables to literal endpoints), `t_i` and `t_j`
    /// must be definitionally equal *after* substituting those forced endpoints —
    /// this is exactly cubical type theory's "compatible system" condition (Cohen–
    /// Coquand–Huber–Mörtberg, *Cubical Type Theory*, §4.2), strictly more general
    /// than (and a conservative relaxation of) requiring unconditional equality: an
    /// overlap of `⊤` restricts along the single vacuous clause `[]`, so
    /// `restrict_clause_term` is the identity and this reduces to plain
    /// `is_def_eq(t_i, t_j)` exactly as before. Every clause must agree (`all`, not
    /// `any`) — see `restrict_clause_term`'s doc for why that's the only sound
    /// choice.
    fn check_sys(
        &self,
        ctx: &mut LocalCtx,
        branches: &[(Rc<Cof>, Rc<Term>)],
        expected: &Term,
    ) -> Result<(), String> {
        let expected_w = self.reducer().whnf(expected);
        let Term::Partial(psi, a) = &expected_w else {
            return Err(format!(
                "a system [φ ↦ t, …] must be checked against a `Partial φ A` type, got {}",
                expected_w.pretty()
            ));
        };
        self.check_cof_wellformed(ctx, psi)?;
        if branches.is_empty() {
            return if face::is_false(psi) {
                Ok(())
            } else {
                Err("empty system [] does not cover a satisfiable cofibration".to_string())
            };
        }
        let mut cover = (*branches[0].0).clone();
        for (phi, _) in &branches[1..] {
            cover = Cof::or(cover, (**phi).clone());
        }
        if !face::entails(psi, &cover) {
            return Err(
                "system does not cover the required cofibration: ψ ⊬ φ_1 ∨ … ∨ φ_n".to_string(),
            );
        }
        for (phi, t) in branches {
            self.check_cof_wellformed(ctx, phi)?;
            self.check(ctx, t, a)?;
        }
        for i in 0..branches.len() {
            for j in (i + 1)..branches.len() {
                let overlap = Cof::and((*branches[i].0).clone(), (*branches[j].0).clone());
                if face::is_false(&overlap) {
                    continue; // unsatisfiable overlap imposes no obligation
                }
                for clause in face::overlap_clauses(&branches[i].0, &branches[j].0) {
                    let ti = face::restrict_clause_term(&clause, &branches[i].1);
                    let tj = face::restrict_clause_term(&clause, &branches[j].1);
                    if !self.is_def_eq(ctx, &ti, &tj) {
                        return Err(format!(
                            "incompatible system: branches {i} and {j} disagree on their overlap \
                             (φ_{i} ∧ φ_{j} is satisfiable, but the branch terms are not \
                             definitionally equal after restricting to the overlapping face)"
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    /// Check that `t` has type `expected` (up to definitional equality).
    pub fn check(&self, ctx: &mut LocalCtx, t: &Term, expected: &Term) -> Result<(), String> {
        // A system is check-only (see `Term::Sys`'s doc and the `Term::Sys` arm of
        // `infer`): its type can't be inferred, only checked against an expected
        // `Partial ψ A`.
        if let Term::Sys(branches) = t {
            return self.check_sys(ctx, branches, expected);
        }
        // `glue [φ ↦ t, …] a` is likewise check-only (see `Term::GlueIntro`'s doc).
        if let Term::GlueIntro(branches, a) = t {
            return self.check_glue_intro(ctx, branches, a, expected);
        }
        let inferred = self.infer(ctx, t)?;
        if self.is_def_eq(ctx, &inferred, expected) {
            Ok(())
        } else {
            Err(format!(
                "type mismatch:\n  expected: {}\n  inferred: {}",
                expected.pretty(),
                inferred.pretty()
            ))
        }
    }

    /// Definitional equality of `a` and `b` in `ctx` — the **authoritative** typing
    /// conversion. Built on the [reducer](crate::reduce)'s computational equality
    /// (β/δ/ζ/ι + η) and additionally closes under **proof irrelevance**: any two
    /// proofs of (definitionally equal) propositions are equal. Threads the local
    /// context so it can infer the type of a subterm and ask whether that type is a
    /// `Prop`.
    pub fn is_def_eq(&self, ctx: &mut LocalCtx, a: &Term, b: &Term) -> bool {
        // Syntactically identical terms are definitionally equal — skip normalizing two
        // big types when the inferred type already matches the expected one verbatim.
        if a == b {
            return true;
        }
        // Otherwise reduce with NbE (the fast evaluator), then compare the normal forms
        // with the complete structural logic — η and proof irrelevance are preserved.
        let nbe = crate::nbe::Nbe::new(self.env);
        let depth = ctx.len();
        let a = nbe.normalize_open(depth, a);
        let b = nbe.normalize_open(depth, b);
        self.compare(ctx, &a, &b)
    }

    /// Compare two **normal-form** terms (no further reduction) up to α, η, grade-blind
    /// `Π`, and proof irrelevance.
    ///
    /// All inputs — top-level (from [`is_def_eq`]) and every recursive call — are in
    /// full normal form, and every subterm of a normal form is itself normal. So the
    /// recursion stays *structural*: it calls back into `compare`, never `is_def_eq`,
    /// and so normalizes the pair **once** rather than re-normalizing every subterm at
    /// every node (which was an O(N²) blowup on large reflected proofs). η-expanding a
    /// normal non-`λ` term keeps it normal, so those branches recurse structurally too.
    /// The lone exception is [`proof_irrelevant`], which compares freshly *inferred*
    /// (non-normal) types and must go back through `is_def_eq`.
    fn compare(&self, ctx: &mut LocalCtx, a: &Term, b: &Term) -> bool {
        if a == b {
            return true;
        }
        let structural = match (a, b) {
            // Phase 3.5 (De Morgan interval, see `crate::cubical`): whenever *at
            // least one* side actually has a connective head (`~`/`∧`/`∨`) and both
            // sides are pure interval expressions, route through the De Morgan-algebra
            // normal form instead of plain structural comparison — this is what makes
            // `~i0 ≡ i1`, `i∧i ≡ i`, etc. hold *definitionally*. Deliberately **not**
            // a blanket check on `Var`/`Var` alone (that would bypass the
            // `proof_irrelevant`/`path_boundary` fallback below for ordinary,
            // non-interval variable comparisons — those still go through the
            // pre-existing `(Term::Var, Term::Var)` arm further down).
            (Term::INeg(..) | Term::IMeet(..) | Term::IJoin(..), _)
            | (_, Term::INeg(..) | Term::IMeet(..) | Term::IJoin(..))
                if crate::cubical::is_interval_expr(a) && crate::cubical::is_interval_expr(b) =>
            {
                crate::cubical::interval_eq(a, b)
            }
            (Term::Sort(l1), Term::Sort(l2)) => crate::level::equiv(l1, l2),
            (Term::Var(i), Term::Var(j)) => i == j,
            (Term::Const(n1, l1), Term::Const(n2, l2)) => {
                n1 == n2
                    && l1.len() == l2.len()
                    && l1.iter().zip(l2).all(|(x, y)| crate::level::equiv(x, y))
            }
            // Grades are erasure annotations, not part of type identity, so ignore
            // them in conversion (this keeps typing identical to the ungraded system).
            (Term::Pi(_, d1, b1), Term::Pi(_, d2, b2)) => {
                self.compare(ctx, d1, d2)
                    && ctx.with((**d1).clone(), |c| self.compare(c, b1, b2))
            }
            (Term::Lam(d1, b1), Term::Lam(d2, b2)) => {
                self.compare(ctx, d1, d2)
                    && ctx.with((**d1).clone(), |c| self.compare(c, b1, b2))
            }
            // η: `λx. body ≡ f` iff `body ≡ f x` under the binder.
            (Term::Lam(d, body), _) => {
                let eta = Term::app(b.lift(1, 0), Term::Var(0));
                ctx.with((**d).clone(), |c| self.compare(c, body, &eta))
            }
            (_, Term::Lam(d, body)) => {
                let eta = Term::app(a.lift(1, 0), Term::Var(0));
                ctx.with((**d).clone(), |c| self.compare(c, &eta, body))
            }
            (Term::App(..), Term::App(..)) => {
                let (h1, a1) = a.unfold_apps();
                let (h2, a2) = b.unfold_apps();
                a1.len() == a2.len()
                    && self.compare(ctx, &h1, &h2)
                    && a1.iter().zip(&a2).all(|(x, y)| self.compare(ctx, x, y))
            }
            // Phase-1 cubical (see `crate::cubical`): structural comparison, same
            // shape as the `Pi`/`Lam` cases above (the interval binder reuses `Var`,
            // so it gets `Term::I` pushed as its "domain" exactly like a real binder).
            (Term::I, Term::I) | (Term::IZero, Term::IZero) | (Term::IOne, Term::IOne) => true,
            (Term::PLam(b1), Term::PLam(b2)) => ctx.with(Term::I, |c| self.compare(c, b1, b2)),
            // Path-η: `⟨i⟩ p @ i ≡ p` for *any* `p : PathP C a0 a1`, literal `PLam`
            // or not (e.g. an opaque axiom/neutral path). This is exactly the
            // standard definitional η for the path type — the interval-binder
            // analogue of the `Lam`-η arms directly above — and, like those arms,
            // is purely **syntactic**: it fires unconditionally whenever one side
            // is a `PLam`, with no separate check that the other side's type is
            // really a `PathP`. That's sound for the same reason ordinary `Lam`-η
            // is sound without re-deriving "the domain is really a `Π`": `compare`
            // (via `is_def_eq`) is only ever invoked on two terms already known,
            // from a prior typing judgement, to inhabit *the same* type. If one
            // side is syntactically a `PLam` its type was checked to be a `PathP`
            // (`Checker::infer`'s `Term::PLam` arm — see `crate::cubical`), so the
            // other side's type is `PathP` too, and η-expanding it to `⟨i⟩ b @ i`
            // (`b` the other side, `Var(0)` the fresh interval binder, lifted
            // exactly as the `Lam` case lifts across its own fresh binder) is the
            // very definition of path-η, not a new equation.
            //
            // What this adds and nothing more: it equates `p` with `⟨i⟩ p @ i` —
            // literally $\eta$ for `PathP`, standard in cubical type theory (CCHM/
            // cubical Agda) — and closes `compare` under that single fact
            // congruently (via the recursive call on bodies). It does NOT equate
            // paths with different endpoints or different interiors: the
            // recursive `self.compare(c, body, &eta)` call still requires the
            // *bodies* to be convertible under the interval binder, so e.g. two
            // opaque paths `p`, `q` with unrelated bodies remain inequal (see
            // `path_eta_does_not_equate_unrelated_opaque_paths` in `nbe.rs`'s
            // tests) — this mirrors exactly how ordinary `Lam`-η never equates
            // `λx.f x` with `λx.g x` unless `f x ≡ g x` already held.
            //
            // Termination: strictly structurally decreasing, exactly like `Lam`-η.
            // The non-`PLam` side `b`/`a` (whichever triggers the arm) is pushed
            // one `PApp` deeper (`b.lift(1,0) @ Var(0)`) and compared against the
            // *body* of the `PLam` side, which is one constructor smaller than the
            // original `PLam` term; the non-`PLam` side can itself only ever
            // η-expand once more (were it to become a `PLam` after eta-expansion
            // it wouldn't — `PApp(_, Var(0))` is never itself a `PLam`), so this
            // cannot loop, exactly as the existing, known-terminating `Lam` case
            // does not loop.
            (Term::PLam(body), _) => {
                let eta = Term::papp(b.lift(1, 0), Term::Var(0));
                ctx.with(Term::I, |c| self.compare(c, body, &eta))
            }
            (_, Term::PLam(body)) => {
                let eta = Term::papp(a.lift(1, 0), Term::Var(0));
                ctx.with(Term::I, |c| self.compare(c, &eta, body))
            }
            (Term::PApp(p1, r1), Term::PApp(p2, r2)) => {
                self.compare(ctx, p1, p2) && self.compare(ctx, r1, r2)
            }
            (Term::PathP(f1, a01, a11), Term::PathP(f2, a02, a12)) => {
                ctx.with(Term::I, |c| self.compare(c, f1, f2))
                    && self.compare(ctx, a01, a02)
                    && self.compare(ctx, a11, a12)
            }
            // Phase-2 cubical (see `crate::face`): guards compare up to semantic
            // cofibration equivalence (the same sub-cube, not necessarily the same
            // `∧`/`∨` tree — see `face::cof_equiv`), branches/codomains structurally.
            (Term::Partial(p1, a1), Term::Partial(p2, a2)) => {
                face::cof_equiv(p1, p2) && self.compare(ctx, a1, a2)
            }
            (Term::Sys(b1), Term::Sys(b2)) => {
                b1.len() == b2.len()
                    && b1.iter().zip(b2).all(|((p1, t1), (p2, t2))| {
                        face::cof_equiv(p1, p2) && self.compare(ctx, t1, t2)
                    })
            }
            // Phase-3 cubical (see `crate::kan`): structural, same shape as `PathP`
            // above — `φ` compares up to semantic cofibration equivalence.
            (Term::Transp(f1, p1, a1), Term::Transp(f2, p2, a2)) => {
                ctx.with(Term::I, |c| self.compare(c, f1, f2))
                    && face::cof_equiv(p1, p2)
                    && self.compare(ctx, a1, a2)
            }
            (Term::HComp(t1, p1, u1, u01), Term::HComp(t2, p2, u2, u02)) => {
                self.compare(ctx, t1, t2)
                    && face::cof_equiv(p1, p2)
                    && ctx.with(Term::I, |c| self.compare(c, u1, u2))
                    && self.compare(ctx, u01, u02)
            }
            // `Glue` (see `crate::term::Term::Glue`): structural, same shape as
            // `Partial`/`HComp` above — `φ` compares up to semantic cofibration
            // equivalence, `A`/`T`/`e` structurally.
            (Term::Glue(a1, b1), Term::Glue(a2, b2)) => {
                self.compare(ctx, a1, a2)
                    && b1.len() == b2.len()
                    && b1.iter().zip(b2.iter()).all(|((p1, t1, e1), (p2, t2, e2))| {
                        face::cof_equiv(p1, p2) && self.compare(ctx, t1, t2) && self.compare(ctx, e1, e2)
                    })
            }
            (Term::Unglue(a1, b1, u1), Term::Unglue(a2, b2, u2)) => {
                self.compare(ctx, a1, a2)
                    && b1.len() == b2.len()
                    && b1.iter().zip(b2.iter()).all(|((p1, t1, e1), (p2, t2, e2))| {
                        face::cof_equiv(p1, p2) && self.compare(ctx, t1, t2) && self.compare(ctx, e1, e2)
                    })
                    && self.compare(ctx, u1, u2)
            }
            // `glue [φ ↦ t, …] a` (see `Term::GlueIntro`): structural, same shape
            // as `Glue`/`Unglue` above.
            (Term::GlueIntro(b1, a1), Term::GlueIntro(b2, a2)) => {
                self.compare(ctx, a1, a2)
                    && b1.len() == b2.len()
                    && b1.iter().zip(b2.iter()).all(|((p1, t1), (p2, t2))| {
                        face::cof_equiv(p1, p2) && self.compare(ctx, t1, t2)
                    })
            }
            _ => false,
        };
        structural || self.proof_irrelevant(ctx, a, b) || self.path_boundary(ctx, a, b)
    }

    /// The **boundary equation** for `Path`/`PathP` (see `crate::cubical`): for *any*
    /// `p : PathP (λi. A) a0 a1` — not just a literal `Term::PLam` (that case is
    /// already handled by ordinary β-reduction in [`crate::reduce::Reducer::whnf`]) —
    /// `p @ i0 ≡ a0` and `p @ i1 ≡ a1` hold **definitionally**, by the well-formedness
    /// of the `PathP` type itself (`Checker::infer`'s `Term::PathP` arm already checked
    /// exactly this equation when `p`'s type was established). This is the
    /// type-directed counterpart to η for `Path` — mirrors how [`Self::proof_irrelevant`]
    /// is also a type-directed equation that plain structural `compare` can't express —
    /// and is what lets `funext`/`ap` (see `crate::cubical`) synthesize their *stated*
    /// general endpoint types even when the underlying path (`h x`, say) is a neutral
    /// application rather than a literal path abstraction.
    ///
    /// Soundness: this adds no equation between terms that weren't already forced
    /// equal by a *previously checked* typing judgement — `a0`/`a1` are read out of
    /// `p`'s own (already-verified) `PathP` type, not asserted here. If that type came
    /// from an inconsistent axiom, the inconsistency was already introduced by
    /// accepting the axiom, exactly as for any other axiom in the kernel (see
    /// `crate::cubical`'s module-level soundness argument, point 3).
    fn path_boundary(&self, ctx: &mut LocalCtx, a: &Term, b: &Term) -> bool {
        self.path_boundary_one(ctx, a, b) || self.path_boundary_one(ctx, b, a)
    }

    /// One direction of [`Self::path_boundary`]: if `probe` is `p @ i0` or `p @ i1`,
    /// infer `p`'s type and — if it's a `PathP` — compare the declared endpoint
    /// against `other`.
    fn path_boundary_one(&self, ctx: &mut LocalCtx, probe: &Term, other: &Term) -> bool {
        let Term::PApp(p, r) = probe else { return false };
        // Phase 3.5 (De Morgan interval, see `crate::cubical`): decide "is this
        // argument the `i0`/`i1` boundary" up to the De Morgan normal form, not just
        // literal syntactic `IZero`/`IOne` — so e.g. `p @ (~i0)` (which normalizes to
        // `i1`) still hits the `a1` boundary, exactly as `p @ i1` would.
        let rn = crate::cubical::normalize_interval(r);
        let at_zero = rn == Term::IZero;
        let at_one = rn == Term::IOne;
        if at_zero || at_one {
            if let Ok(tp) = self.infer(ctx, p) {
                if let Term::PathP(_, a0, a1) = self.reducer().whnf(&tp) {
                    let endpoint = if at_zero { a0 } else { a1 };
                    if self.compare(ctx, &endpoint, other) {
                        return true;
                    }
                }
            }
        }
        // NESTED boundary, one level down (needed by
        // [`crate::cubical_hit`]'s 2-dimensional/"S²" 2-path recursor case:
        // its well-formedness check compares the motive at a fixed OUTER
        // boundary `i0`/`i1` but a still-GENERIC inner interval variable —
        // e.g. `(H.surf_k @ i0) @ j` against a `j`-independent term. `p`
        // itself may be `p2 @ r2` for a literal `r2` one level down (`surf @
        // i0`) — even though `p` isn't *syntactically* a `PLam` (so ordinary
        // β/whnf can't fire on it), it's still DEFINITIONALLY `p2`'s own
        // declared `a0`/`a1` endpoint (`refl base`, here) by this SAME
        // boundary rule applied one level inward; once substituted in, that
        // endpoint is typically a concrete `PLam` (as it always is for the
        // `CubHitSpec` schema's declared surfaces/paths), so `@ r` on it
        // reduces normally via ordinary `whnf`. Bounded to exactly one extra
        // level (mirrors the schema's own "at most 2-dimensional" scope) —
        // `p2` is strictly smaller than `p`, so this cannot loop. Adds no new
        // equation beyond what `p2`'s own (already-checked) `PathP` typing
        // judgement forces, for the identical soundness reason given in this
        // function's own doc comment above.
        if let Term::PApp(p2, r2) = p.as_ref() {
            let rn2 = crate::cubical::normalize_interval(r2);
            let at_zero2 = rn2 == Term::IZero;
            let at_one2 = rn2 == Term::IOne;
            if at_zero2 || at_one2 {
                if let Ok(tp2) = self.infer(ctx, p2) {
                    if let Term::PathP(_, a0, a1) = self.reducer().whnf(&tp2) {
                        let endpoint2 = if at_zero2 { a0 } else { a1 };
                        let simplified = self.reducer().whnf(&Term::papp((*endpoint2).clone(), (**r).clone()));
                        if self.compare(ctx, &simplified, other) {
                            return true;
                        }
                    }
                }
            }
            // NESTED boundary, TWO levels down (needed by
            // [`crate::cubical_hit`]'s 3-dimensional/"S³" 3-path recursor
            // case — the exact same move as the one-level extension above,
            // applied once more: `p2` may itself be `p3 @ r3` for a literal
            // `r3` one level further in (`cube @ i0 @ j`), so `p2`'s own
            // declared `PathP` endpoint (read off `p3`'s type) gives `p2`'s
            // boundary value definitionally, which is then `@ r2`-then-`@ r`
            // applied to reach `probe`'s value. Bounded to exactly one extra
            // level beyond the existing extension (mirrors this schema's own
            // "at most 3-dimensional" scope) — `p3` is strictly smaller than
            // `p2`, which is strictly smaller than `p`, so this still cannot
            // loop. Adds no new equation beyond what `p3`'s own
            // (already-checked) `PathP` typing judgement forces, for the
            // identical soundness reason given in this function's own doc
            // comment above.
            if let Term::PApp(p3, r3) = p2.as_ref() {
                let rn3 = crate::cubical::normalize_interval(r3);
                let at_zero3 = rn3 == Term::IZero;
                let at_one3 = rn3 == Term::IOne;
                if at_zero3 || at_one3 {
                    if let Ok(tp3) = self.infer(ctx, p3) {
                        if let Term::PathP(_, a0, a1) = self.reducer().whnf(&tp3) {
                            let endpoint3 = if at_zero3 { a0 } else { a1 };
                            let step2 = self.reducer().whnf(&Term::papp((*endpoint3).clone(), (**r2).clone()));
                            let step1 = self.reducer().whnf(&Term::papp(step2, (**r).clone()));
                            if self.compare(ctx, &step1, other) {
                                return true;
                            }
                        }
                    }
                }
                // NESTED boundary, THREE levels down (needed by
                // [`crate::cubical_hit`]'s 4-dimensional/"S⁴" 4-path recursor
                // case — the exact same move as the two extensions above,
                // applied once more: `p3` may itself be `p4 @ r4` for a
                // literal `r4` one level further in (`hyper @ i0 @ j @ k`), so
                // `p3`'s own declared `PathP` endpoint (read off `p4`'s type)
                // gives `p3`'s boundary value definitionally, which is then
                // `@ r3`-then-`@ r2`-then-`@ r` applied to reach `probe`'s
                // value. Bounded to exactly one extra level beyond the
                // existing extension (mirrors this schema's own "at most
                // 4-dimensional" scope) — `p4` is strictly smaller than `p3`,
                // which is strictly smaller than `p2`, which is strictly
                // smaller than `p`, so this still cannot loop. Adds no new
                // equation beyond what `p4`'s own (already-checked) `PathP`
                // typing judgement forces, for the identical soundness reason
                // given in this function's own doc comment above.
                if let Term::PApp(p4, r4) = p3.as_ref() {
                    let rn4 = crate::cubical::normalize_interval(r4);
                    let at_zero4 = rn4 == Term::IZero;
                    let at_one4 = rn4 == Term::IOne;
                    if at_zero4 || at_one4 {
                        if let Ok(tp4) = self.infer(ctx, p4) {
                            if let Term::PathP(_, a0, a1) = self.reducer().whnf(&tp4) {
                                let endpoint4 = if at_zero4 { a0 } else { a1 };
                                let step3 =
                                    self.reducer().whnf(&Term::papp((*endpoint4).clone(), (**r3).clone()));
                                let step2 = self.reducer().whnf(&Term::papp(step3, (**r2).clone()));
                                let step1 = self.reducer().whnf(&Term::papp(step2, (**r).clone()));
                                if self.compare(ctx, &step1, other) {
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
        false
    }

    /// Convenience: definitional equality of two **closed** terms.
    pub fn def_eq(&self, a: &Term, b: &Term) -> bool {
        self.is_def_eq(&mut LocalCtx::new(), a, b)
    }

    /// Proof irrelevance: if `a` is a proof — i.e. its type `TA` is a proposition
    /// (`TA : Prop`) — and `b` is a proof of a definitionally equal proposition, then
    /// `a` and `b` are equal regardless of how they were built. This never fires on
    /// data (whose type lives in a `Type` universe), so it cannot equate distinct
    /// values; and the recursion is well-founded because the type of a *proof* is a
    /// `Prop`, whose own type is `Type 0` (not a `Prop`), so the check bottoms out.
    fn proof_irrelevant(&self, ctx: &mut LocalCtx, a: &Term, b: &Term) -> bool {
        let Ok(ta) = self.infer(ctx, a) else { return false };
        let Ok(sort) = self.infer(ctx, &ta) else { return false };
        let is_prop = matches!(self.reducer().whnf(&sort), Term::Sort(l) if matches!(l.normalize(), Level::Zero));
        if !is_prop {
            return false;
        }
        let Ok(tb) = self.infer(ctx, b) else { return false };
        self.is_def_eq(ctx, &ta, &tb)
    }

    /// Infer the type of `t`, require it to be a sort, and return that level.
    pub fn infer_sort(&self, ctx: &mut LocalCtx, t: &Term) -> Result<Level, String> {
        let ty = self.infer(ctx, t)?;
        match self.reducer().whnf(&ty) {
            Term::Sort(l) => Ok(l),
            other => Err(format!("expected a type (sort), got {other:?}")),
        }
    }

    /// Type-check a closed term and return its type.
    pub fn infer_closed(&self, t: &Term) -> Result<Term, String> {
        let mut ctx = LocalCtx::new();
        self.infer(&mut ctx, t)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Env;

    /// Proof irrelevance: in a context `p : Prop, h1 : p, h2 : p`, the two distinct
    /// hypotheses `h1` and `h2` are definitionally equal — because their type `p` is
    /// a proposition.
    #[test]
    fn proof_irrelevance_fires_for_props() {
        let env = Env::new();
        let chk = Checker::new(&env);
        let mut ctx = LocalCtx::new();
        ctx.push(Term::prop()); // p : Prop      (level 0)
        ctx.push(Term::Var(0)); // h1 : p        (level 1)
        ctx.push(Term::Var(1)); // h2 : p        (level 2)
        // h1 = Var(1), h2 = Var(0) in this 3-deep context; syntactically distinct.
        assert!(chk.is_def_eq(&mut ctx, &Term::Var(1), &Term::Var(0)));
    }

    /// It does *not* fire for data: in `n : Type 0` … actually distinct variables of a
    /// `Type` are NOT equated.
    #[test]
    fn proof_irrelevance_does_not_fire_for_data() {
        let env = Env::new();
        let chk = Checker::new(&env);
        let mut ctx = LocalCtx::new();
        ctx.push(Term::typ(0)); // A : Type 0
        ctx.push(Term::Var(0)); // x : A
        ctx.push(Term::Var(1)); // y : A
        assert!(!chk.is_def_eq(&mut ctx, &Term::Var(1), &Term::Var(0)));
    }
}
