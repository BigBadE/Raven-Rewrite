//! Quantitative (QTT) **usage checking**: the structural linearity/erasure discipline.
//!
//! The kernel's [`Grade`](crate::term::Grade)s (`0` erased, `1` linear, `ω`
//! unrestricted) form the standard Quantitative Type Theory semiring, and a `Π`
//! binder already carries the grade at which its argument may be consumed. The
//! trusted [`Checker`](crate::check) treats grades as *annotations* — ignoring them
//! keeps its judgement identical to the ungraded system, which is what makes graded
//! code backward-compatible. The [`erase`](crate::erase) pass then uses the `0`
//! grades to drop ghosts and to reject a ghost used at runtime.
//!
//! This module supplies the **missing half** of the discipline: the *quantitative*
//! accounting that a **linear** (grade `1`) binder is used **exactly once** — not
//! dropped, not duplicated — and, uniformly, that every binder's actual usage *fits*
//! within the grade its `Π` allows. Concretely it implements the QTT context rules:
//!
//! * **variable**  — a use of `Var(i)` contributes usage `1` to binder `i` and `0`
//!   to every other binder (the singleton context `0·Γ, x :¹ A`);
//! * **application** `f a` at a `Π (_ :ᵖ A). B` — usages **add**, and the argument's
//!   usages are **scaled** by the binder grade `p`: `usage(f a) = usage(f) + p · usage(a)`
//!   (so an argument passed to an erased position costs `0`, and one passed to an
//!   unrestricted position costs `ω`);
//! * **lambda**    `λ (_ :ᵖ A). t` — infer the body's usages in the extended context,
//!   *split off* the bound variable's own usage `u₀`, **check `u₀` fits `p`** (and for
//!   a linear `p = 1`, that `u₀` is *exactly* `1`), and return the usages of the free
//!   variables;
//! * **let / Π / sorts / consts** — analogously; types (the domains of `Π`/`λ`, the
//!   type of a `let`) live in the **erased (grade-0) fragment**: their variable
//!   occurrences are scaled by `0` and so never count as computational use. This is
//!   what lets a linear resource still appear in *types* and *specifications* without
//!   being counted as consumed.
//!
//! ## Soundness & non-regression
//!
//! This pass is **opt-in and purely additive**: it only ever *rejects* terms; it can
//! never make the kernel accept something [`Checker`] rejected. Every binder that is
//! not explicitly graded is `ω` (the default of [`Term::pi`]/[`Term::lam`]), and `ω`
//! admits *any* usage (`Grade::fits(_, Many)` is always true), so **ungraded code —
//! the entire existing corpus — is accepted unchanged**. Restrictions bite only where
//! a `Π` was deliberately annotated `Zero`/`One`.
//!
//! Grades are never consulted by reduction or conversion, so this pass cannot change
//! what normalizes to what, nor prove any new proposition: a term this pass rejects
//! was already well-typed, and one it accepts is a *subset* of the well-typed terms.
//! It therefore cannot introduce a proof of `False`.
//!
//! The analysis is deliberately a **usage skeleton**, independent of full type
//! inference: it walks the term's structure and consults declared `Π` grades (on
//! `λ` via an inferred expected type, and on application heads via the checker),
//! exactly as [`erase`](crate::erase) does. Where a `Π` grade is not available (e.g.
//! an open application head whose type cannot be found) it falls back to `ω`, which
//! can only *relax* — never tighten — so it stays sound.

use crate::check::{Checker, LocalCtx};
use crate::reduce::Reducer;
use crate::term::{Grade, Term};
use crate::Env;

/// A **usage vector**: for the binders currently in scope (indexed by de Bruijn
/// index, `0` = innermost), how much each has been consumed. Absent entries are
/// `Grade::Zero`. Stored densely as a `Vec` indexed by de Bruijn index so that
/// crossing a binder is a cheap push/pop.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Usage {
    /// `grades[i]` is the total usage of `Var(i)` in the analysed term.
    grades: Vec<Grade>,
}

impl Usage {
    /// The empty usage (everything `Zero`).
    pub fn empty() -> Usage {
        Usage { grades: Vec::new() }
    }

    /// The usage of a single occurrence of `Var(i)`: grade `1` at `i`, `0` elsewhere.
    fn single(i: usize) -> Usage {
        let mut grades = vec![Grade::Zero; i + 1];
        grades[i] = Grade::One;
        Usage { grades }
    }

    /// Read the usage of de Bruijn index `i` (defaulting to `Zero`).
    #[cfg(test)]
    fn get(&self, i: usize) -> Grade {
        self.grades.get(i).copied().unwrap_or(Grade::Zero)
    }

    /// Pointwise semiring **addition** (`usage(f) + usage(a)`): combine two sub-usages,
    /// e.g. the two sides of an application or two branches that both mention a variable.
    fn add(mut self, other: &Usage) -> Usage {
        if other.grades.len() > self.grades.len() {
            self.grades.resize(other.grades.len(), Grade::Zero);
        }
        for (i, g) in other.grades.iter().enumerate() {
            self.grades[i] = self.grades[i].add(*g);
        }
        self
    }

    /// Scale every entry by the semiring **multiplication** with `p` (`p · usage`).
    /// Used when a sub-usage flows into an argument position of grade `p`: an erased
    /// (`p = 0`) position zeroes all usage, a linear (`p = 1`) position is unchanged,
    /// an unrestricted (`p = ω`) position saturates every real use to `ω`.
    fn scale(mut self, p: Grade) -> Usage {
        for g in &mut self.grades {
            *g = g.mul(p);
        }
        self
    }

    /// Remove the innermost binder (`Var(0)`) when leaving its scope, returning its own
    /// total usage together with the shifted-down usage of the *outer* binders.
    fn pop_binder(mut self) -> (Grade, Usage) {
        if self.grades.is_empty() {
            return (Grade::Zero, self);
        }
        let head = self.grades.remove(0);
        (head, self)
    }
}

/// Errors from the usage discipline.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GradeError {
    /// A binder graded `allowed` was used with an actual usage that does not fit it
    /// (e.g. a linear binder used twice, or an erased binder used at grade `1`).
    UsageMismatch { allowed: Grade, actual: Grade, what: String },
    /// A linear (grade-`1`) binder was **dropped** — used zero times.
    LinearUnused { what: String },
    /// Structural problem while walking the term (e.g. an application head whose
    /// function type could not be determined).
    Structural(String),
}

impl std::fmt::Display for GradeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GradeError::UsageMismatch { allowed, actual, what } => write!(
                f,
                "usage discipline: binder {what} allows grade {allowed:?} but is used at grade {actual:?}"
            ),
            GradeError::LinearUnused { what } => {
                write!(f, "usage discipline: linear binder {what} is dropped (used zero times)")
            }
            GradeError::Structural(m) => write!(f, "usage discipline: {m}"),
        }
    }
}

impl std::error::Error for GradeError {}

/// The usage-checker, bound to an environment. It reuses the trusted
/// [`Checker`]/[`Reducer`] only to *read declared `Π` grades* (never to change any
/// typing decision).
pub struct Graded<'e> {
    env: &'e Env,
    /// Binder types, innermost last — kept in lock-step with the analysed context so
    /// we can infer the type of an application head to recover its argument grades.
    binders: Vec<Term>,
}

impl<'e> Graded<'e> {
    pub fn new(env: &'e Env) -> Self {
        Graded { env, binders: Vec::new() }
    }

    fn reducer(&self) -> Reducer<'e> {
        Reducer::new(self.env)
    }

    fn ctx(&self) -> LocalCtx {
        let mut c = LocalCtx::new();
        for ty in &self.binders {
            c.push(ty.clone());
        }
        c
    }

    /// The type of the head of an application spine, used to recover its `Π` grades.
    fn head_type(&self, head: &Term) -> Result<Term, GradeError> {
        match head {
            Term::Const(n, ls) => self
                .env
                .get(n)
                .map(|d| d.ty().instantiate_levels(ls))
                .ok_or_else(|| GradeError::Structural(format!("unknown constant '{n}'"))),
            Term::Var(i) => {
                let n = self.binders.len();
                if *i >= n {
                    return Err(GradeError::Structural(format!("unbound variable {i}")));
                }
                Ok(self.binders[n - 1 - *i].lift(*i as isize + 1, 0))
            }
            other => Checker::new(self.env)
                .infer(&mut self.ctx(), other)
                .map_err(GradeError::Structural),
        }
    }

    /// Infer the usage vector of `t`, using `expected` (its declared type, in whnf when
    /// possible) to recover binder grades that a bare `λ` does not itself carry. This is
    /// the entry the discipline is checked through: the grade of a `λ`'s binder lives on
    /// the `Π` of its *type*, so we thread the type down alongside the term.
    pub fn infer_checked(&mut self, t: &Term, expected: &Term) -> Result<Usage, GradeError> {
        if let Term::Lam(dom, body) = t {
            // Read the binder grade from the expected `Π`; default `ω` if unavailable.
            let exp = self.reducer().whnf(expected);
            let (grade, codom) = match &exp {
                Term::Pi(p, _, cod) => (*p, Some((**cod).clone())),
                _ => (Grade::Many, None),
            };
            let ud = self.infer(dom)?.scale(Grade::Zero);
            let ub = match codom {
                Some(cod) => self.under(dom, |s| s.infer_checked(body, &cod))?,
                None => self.under(dom, |s| s.infer(body))?,
            };
            let (u0, urest) = ub.pop_binder();
            self.check_binder(grade, u0, "λ")?;
            return Ok(ud.add(&urest));
        }
        // Not a λ: the expected type carries no further binder grades to thread, so fall
        // back to the structural pass (which still reads grades off `Π` heads/λ types).
        self.infer(t)
    }

    /// Infer the usage vector of `t` in the current context, checking the discipline of
    /// every binder `t` introduces along the way.
    pub fn infer(&mut self, t: &Term) -> Result<Usage, GradeError> {
        match t {
            // Sorts and constants mention no local variables.
            Term::Sort(_) | Term::Const(..) => Ok(Usage::empty()),
            // An unsolved metavariable should never reach here; be conservative.
            Term::Meta(m) => Err(GradeError::Structural(format!("unsolved metavariable ?{m}"))),
            // A computationally-relevant occurrence: usage 1 of this binder.
            Term::Var(i) => Ok(Usage::single(*i)),

            // `Π` is a type; the domain and codomain live in the erased fragment. Their
            // variable occurrences are scaled to `0` so they never count as use; this is
            // exactly what lets a linear resource appear in a type without being
            // consumed. We still recurse to keep de Bruijn depths aligned.
            Term::Pi(_, dom, cod) => {
                let ud = self.infer(dom)?.scale(Grade::Zero);
                let uc = self.under(dom, |s| s.infer(cod))?;
                let (_head, uc) = uc.pop_binder();
                Ok(ud.add(&uc.scale(Grade::Zero)))
            }

            // `λ (_ :ᵖ dom). body`: recover the binder grade `p` from the `λ`'s inferred
            // `Π` type (else `ω`, the safe default), analyse the body in the extended
            // context, split off the bound variable's usage `u₀`, and check that `u₀`
            // fits `p` (exactly `1` for a linear `p`). The domain is a type, so its
            // usages are erased.
            Term::Lam(dom, body) => {
                let grade = self.lambda_grade(t);
                let ud = self.infer(dom)?.scale(Grade::Zero);
                let ub = self.under(dom, |s| s.infer(body))?;
                let (u0, urest) = ub.pop_binder();
                self.check_binder(grade, u0, "λ")?;
                Ok(ud.add(&urest))
            }

            // `let (_ : ty) := value in body`. `let` carries no grade, so the bound
            // binder is treated as unrestricted (grade `ω`) — imposing no discipline,
            // which keeps it backward-compatible. The value's usages add into the total.
            Term::Let(ty, value, body) => {
                let ut = self.infer(ty)?.scale(Grade::Zero);
                let uv = self.infer(value)?;
                let ub = self.under(ty, |s| s.infer(body))?;
                let (_u0, urest) = ub.pop_binder();
                Ok(ut.add(&uv).add(&urest))
            }

            // An application spine `head a0 a1 …`: start from the head's usage, then for
            // each argument add its usage *scaled by the corresponding Π grade*.
            Term::App(..) => {
                let (head, args) = t.unfold_apps();
                let mut acc = self.infer(&head)?;
                let mut ty = self.reducer().whnf(&self.head_type(&head)?);
                for arg in &args {
                    let Term::Pi(p, _dom, cod) = &ty else {
                        // Head type isn't a readable function type: treat the argument as
                        // unrestricted (the sound, never-tightening default).
                        let ua = self.infer(arg)?.scale(Grade::Many);
                        acc = acc.add(&ua);
                        continue;
                    };
                    let (p, cod) = (*p, (**cod).clone());
                    let ua = self.infer(arg)?.scale(p);
                    acc = acc.add(&ua);
                    ty = self.reducer().whnf(&cod.instantiate(arg));
                }
                Ok(acc)
            }
        }
    }

    /// Run `f` with `dom` pushed as the innermost binder.
    fn under<R>(
        &mut self,
        dom: &Term,
        f: impl FnOnce(&mut Self) -> Result<R, GradeError>,
    ) -> Result<R, GradeError> {
        self.binders.push(dom.clone());
        let r = f(self);
        self.binders.pop();
        r
    }

    /// The declared grade of a `λ`'s binder. A bare `λ` carries no grade of its own —
    /// the grade lives on the `Π` it inhabits — so we infer the `λ`'s type and read the
    /// grade off that `Π`. If inference fails (e.g. an open term), default to `ω`, which
    /// imposes no restriction and so can only ever be conservative.
    fn lambda_grade(&self, lam: &Term) -> Grade {
        match Checker::new(self.env).infer(&mut self.ctx(), lam) {
            Ok(ty) => match self.reducer().whnf(&ty) {
                Term::Pi(p, _, _) => p,
                _ => Grade::Many,
            },
            Err(_) => Grade::Many,
        }
    }

    /// Enforce the discipline for a binder graded `allowed` whose bound variable was
    /// actually used at grade `actual`:
    ///
    /// * `actual` must `fit` within `allowed` (`0 ⊑ {0,1,ω}`, `1 ⊑ {1,ω}`, `ω ⊑ {ω}`);
    /// * additionally, a **linear** binder (`allowed = 1`) must be used *exactly* once —
    ///   `actual = 1` — so use-zero (a dropped linear resource) is also rejected.
    fn check_binder(&self, allowed: Grade, actual: Grade, what: &str) -> Result<(), GradeError> {
        if allowed == Grade::One && actual == Grade::Zero {
            return Err(GradeError::LinearUnused { what: what.to_string() });
        }
        if !actual.fits(allowed) {
            return Err(GradeError::UsageMismatch {
                allowed,
                actual,
                what: what.to_string(),
            });
        }
        Ok(())
    }
}

/// Check the QTT usage discipline of a closed term. Returns `Ok(())` if every graded
/// binder in `t` is used within its grade (linear = exactly once, erased = never in a
/// relevant position, unrestricted = freely). Ungraded (`ω`-defaulted) terms always
/// pass, so this never rejects existing code.
pub fn check_usage(env: &Env, t: &Term) -> Result<(), GradeError> {
    Graded::new(env).infer(t).map(|_| ())
}

/// Check the usage discipline of `t` against its **declared type** `ty`. This is the
/// intended entry point for the linear discipline: a bare `λ` carries no grade (the
/// grade lives on the `Π` of its type), so the grades of the *outer* binders are
/// recovered from `ty` and threaded down through nested `λ`s. Ungraded (`ω`) types
/// impose no restriction, so existing code passes unchanged.
pub fn check_usage_against(env: &Env, t: &Term, ty: &Term) -> Result<(), GradeError> {
    Graded::new(env).infer_checked(t, ty).map(|_| ())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Kernel;
    use crate::term::{name, Grade};

    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    /// Direct unit tests of the binder discipline: linear used twice/zero is rejected,
    /// exactly once accepted; erased in a relevant position rejected, unused fine;
    /// unrestricted accepts anything.
    #[test]
    fn check_binder_discipline() {
        let env = Env::new();
        let g = Graded::new(&env);
        // linear
        assert!(g.check_binder(Grade::One, Grade::One, "x").is_ok());
        assert!(matches!(
            g.check_binder(Grade::One, Grade::Many, "x"),
            Err(GradeError::UsageMismatch { .. })
        ));
        assert!(matches!(
            g.check_binder(Grade::One, Grade::Zero, "x"),
            Err(GradeError::LinearUnused { .. })
        ));
        // erased: a relevant (grade-1/ω) use is rejected, unused is fine.
        assert!(matches!(
            g.check_binder(Grade::Zero, Grade::One, "x"),
            Err(GradeError::UsageMismatch { .. })
        ));
        assert!(g.check_binder(Grade::Zero, Grade::Zero, "x").is_ok());
        // unrestricted: anything fits.
        assert!(g.check_binder(Grade::Many, Grade::Zero, "x").is_ok());
        assert!(g.check_binder(Grade::Many, Grade::One, "x").is_ok());
        assert!(g.check_binder(Grade::Many, Grade::Many, "x").is_ok());
    }

    /// Usage arithmetic: `usage(f a)` adds head and (scaled) argument usages.
    #[test]
    fn usage_add_and_scale() {
        let u = Usage::single(0).add(&Usage::single(1));
        assert_eq!(u.get(0), Grade::One);
        assert_eq!(u.get(1), Grade::One);
        let z = u.clone().scale(Grade::Zero);
        assert_eq!(z.get(0), Grade::Zero);
        assert_eq!(z.get(1), Grade::Zero);
        // two occurrences of the same var saturate to Many.
        let two = Usage::single(0).add(&Usage::single(0));
        assert_eq!(two.get(0), Grade::Many);
    }

    /// An ungraded (ω-default) term is always accepted — the backward-compat guarantee.
    #[test]
    fn ungraded_identity_accepted() {
        let env = Env::new();
        let id = Term::lam(Term::typ(0), Term::lam(Term::Var(0), Term::Var(0)));
        assert!(check_usage(&env, &id).is_ok());
    }

    // --- End-to-end tests driving the grade off a declared linear `Π` type. ----------
    //
    // A bare `λ` has no grade, so to exercise the linear discipline through `infer` we
    // give a top-level definition a linear function *type* and let `lambda_grade` read
    // the grade off it.

    /// `linear_id : Π (x :¹ Res). Res := λ x. x` — the linear identity, used once: OK.
    #[test]
    fn linear_resource_used_once_accepted() {
        let mut k = Kernel::new();
        k.add_axiom("Res", 0, Term::typ(0)).unwrap();
        let ty = Term::pi_graded(Grade::One, cn("Res"), cn("Res"));
        let body = Term::lam(cn("Res"), Term::Var(0));
        // The kernel type-checks it (grades don't affect typing).
        k.add_definition("linear_id", 0, ty.clone(), body.clone()).unwrap();
        // And the usage pass accepts it: the linear binder is used exactly once.
        assert!(check_usage_against(k.env(), &body, &ty).is_ok());
    }

    /// A linear resource **dropped** is rejected: `λ (x :¹ Res). c` never uses `x`.
    #[test]
    fn linear_resource_dropped_rejected() {
        let mut k = Kernel::new();
        k.add_axiom("Res", 0, Term::typ(0)).unwrap();
        k.add_axiom("c", 0, cn("Res")).unwrap();
        // Type says the argument is linear, but the body ignores it.
        let ty = Term::pi_graded(Grade::One, cn("Res"), cn("Res"));
        let body = Term::lam(cn("Res"), cn("c"));
        k.add_definition("drop_it", 0, ty.clone(), body.clone()).unwrap();
        let err = check_usage_against(k.env(), &body, &ty).unwrap_err();
        assert!(matches!(err, GradeError::LinearUnused { .. }), "got {err}");
    }

    /// A linear resource **duplicated** is rejected: `λ (x :¹ Res). dup x x` uses `x` twice.
    #[test]
    fn linear_resource_duplicated_rejected() {
        let mut k = Kernel::new();
        k.add_axiom("Res", 0, Term::typ(0)).unwrap();
        // dup : Res → Res → Res  (both args unrestricted, so passing x twice = Many)
        k.add_axiom("dup", 0, Term::arrow(cn("Res"), Term::arrow(cn("Res"), cn("Res")))).unwrap();
        let ty = Term::pi_graded(Grade::One, cn("Res"), cn("Res"));
        let body = Term::lam(
            cn("Res"),
            Term::apps(cn("dup"), [Term::Var(0), Term::Var(0)]),
        );
        k.add_definition("dup_it", 0, ty.clone(), body.clone()).unwrap();
        let err = check_usage_against(k.env(), &body, &ty).unwrap_err();
        assert!(matches!(err, GradeError::UsageMismatch { .. }), "got {err}");
    }

    /// The erased fragment: a linear resource may appear in a **type** position without
    /// being counted as consumed. Here `x` is used only inside a `Π`-domain (a type),
    /// so its computational usage is `0` — and a `0`-graded binder tolerates that.
    #[test]
    fn erased_binder_usable_in_type_position() {
        let env = Env::new();
        // λ (x :⁰ Type0). x-appears-only-in-a-type : here the body is `Type0`, so `x` is
        // never used at all — trivially fits grade 0.
        // Build a term whose only occurrence of the binder is in a Π domain:
        //   λ (A :⁰ Type0). (Π (_ : A). A)          [A used only in a type]
        // grade of the λ is read from its inferred Π type; since the codomain `Π (_:A).A`
        // is a Type, the λ's own type is `Π (A : Type0). Type1`, grade ω — so to actually
        // test grade-0 we check the usage split directly.
        let mut g = Graded::new(&env);
        let body = Term::pi(Term::Var(0), Term::Var(1)); // Π (_ : A). A, under binder A
        let inner = g.under(&Term::typ(0), |s| s.infer(&body)).unwrap();
        let (u0, _) = inner.pop_binder();
        // A appears only in type position ⇒ usage 0 ⇒ fits an erased (grade-0) binder.
        assert_eq!(u0, Grade::Zero);
        assert!(g.check_binder(Grade::Zero, u0, "A").is_ok());
    }

    /// End-to-end erased discipline: a binder declared **erased** (grade 0) but used in
    /// a computationally-relevant position is rejected via the top-level entry.
    /// `erased_id : Π (x :⁰ Res). Res := λ x. x` — returns the ghost, so `x` is used at
    /// grade 1, which does not fit grade 0.
    #[test]
    fn erased_binder_used_relevantly_rejected() {
        let mut k = Kernel::new();
        k.add_axiom("Res", 0, Term::typ(0)).unwrap();
        let ty = Term::pi_graded(Grade::Zero, cn("Res"), cn("Res"));
        let body = Term::lam(cn("Res"), Term::Var(0));
        k.add_definition("erased_id", 0, ty.clone(), body.clone()).unwrap();
        let err = check_usage_against(k.env(), &body, &ty).unwrap_err();
        assert!(matches!(err, GradeError::UsageMismatch { .. }), "got {err}");
    }

    /// Ownership worked example — the structural counterpart of `separation.rv`'s
    /// theorem. A unique `&mut`/owned resource is modelled by a **linear** binder:
    /// `consume : Π (r :¹ Handle). Unit` typechecks iff the body uses `r` exactly once.
    /// Using it once (handing it to a consumer) is accepted; dropping or duplicating it
    /// is rejected — exactly the move discipline of a `&mut`.
    #[test]
    fn linear_mut_handle_move_discipline() {
        let mut k = Kernel::new();
        k.add_axiom("Handle", 0, Term::typ(0)).unwrap();
        k.add_axiom("Unit", 0, Term::typ(0)).unwrap();
        // close : Π (h :¹ Handle). Unit  (a *linear* consumer: takes the handle once)
        k.add_axiom("close", 0, Term::pi_graded(Grade::One, cn("Handle"), cn("Unit")))
            .unwrap();

        let ty = Term::pi_graded(Grade::One, cn("Handle"), cn("Unit"));

        // OK: consume the unique handle exactly once.
        let used_once = Term::lam(cn("Handle"), Term::app(cn("close"), Term::Var(0)));
        k.add_definition("consume", 0, ty.clone(), used_once.clone()).unwrap();
        assert!(check_usage_against(k.env(), &used_once, &ty).is_ok());

        // Rejected: dropping the unique handle (a leaked &mut).
        k.add_axiom("unit", 0, cn("Unit")).unwrap();
        let dropped = Term::lam(cn("Handle"), cn("unit"));
        assert!(matches!(
            check_usage_against(k.env(), &dropped, &ty),
            Err(GradeError::LinearUnused { .. })
        ));
    }

    /// Regression guard in miniature: ungraded (ω-default) terms of the shape the proof
    /// corpus is built from pass the usage pass unchanged — grades only *add*
    /// restrictions, never remove the acceptance of existing code. (The full corpus
    /// regression is covered by the untouched `rv-driver` proof-corpus tests.)
    #[test]
    fn ungraded_corpus_shapes_unaffected() {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("f", 0, Term::arrow(cn("A"), cn("A"))).unwrap();
        // λ (x : A). f (f x)  — a variable used twice under ω binders: perfectly fine.
        let term = Term::lam(cn("A"), Term::app(cn("f"), Term::app(cn("f"), Term::Var(0))));
        let ty = Term::arrow(cn("A"), cn("A"));
        assert!(check_usage_against(k.env(), &term, &ty).is_ok());
        assert!(check_usage(k.env(), &term).is_ok());
    }
}
