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
use crate::level::Level;
use crate::reduce::Reducer;
use crate::term::Term;

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
        }
    }

    /// Check that `t` has type `expected` (up to definitional equality).
    pub fn check(&self, ctx: &mut LocalCtx, t: &Term, expected: &Term) -> Result<(), String> {
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
            (Term::PApp(p1, r1), Term::PApp(p2, r2)) => {
                self.compare(ctx, p1, p2) && self.compare(ctx, r1, r2)
            }
            (Term::PathP(f1, a01, a11), Term::PathP(f2, a02, a12)) => {
                ctx.with(Term::I, |c| self.compare(c, f1, f2))
                    && self.compare(ctx, a01, a02)
                    && self.compare(ctx, a11, a12)
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
        let at_zero = matches!(&**r, Term::IZero);
        let at_one = matches!(&**r, Term::IOne);
        if !at_zero && !at_one {
            return false;
        }
        let Ok(tp) = self.infer(ctx, p) else { return false };
        let Term::PathP(_, a0, a1) = self.reducer().whnf(&tp) else { return false };
        let endpoint = if at_zero { a0 } else { a1 };
        self.compare(ctx, &endpoint, other)
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
