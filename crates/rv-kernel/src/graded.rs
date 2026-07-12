//! Quantitative (QTT) **usage checking**: the structural linearity/erasure discipline.
//!
//! The kernel's [`Grade`](rv_kernel_core::term::Grade)s (`0` erased, `1` linear, `ω`
//! unrestricted) form the standard Quantitative Type Theory semiring, and a `Π`
//! binder already carries the grade at which its argument may be consumed. The
//! trusted [`Checker`](rv_kernel_core::check) treats grades as *annotations* — ignoring them
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
//! ## Coverage: Σ / eliminators are ordinary applications
//!
//! The kernel has **no dedicated `Sigma`/pair `Term` constructor**: pairs, inductive
//! constructors, and eliminators (`Nat.rec`, `Quot.lift`, `Trunc.rec`, coinductive
//! destructors, …) are all [`Term::Const`]s with a declared `Π` type in the [`Env`],
//! applied via ordinary [`Term::App`]. The `App` arm of [`Graded::infer`] already
//! reads each argument position's declared grade off that `Π` (via [`Graded::head_type`])
//! and scales the argument's usage accordingly — so a linearly-graded constructor
//! field or a linearly-graded recursor "case"/minor-premise argument is checked by
//! the *same* mechanism as any other application, with no special-casing needed. This
//! also reaches *inside* a `λ` passed as an argument (e.g. a recursor's case), since
//! `infer` recurses into `Lam` wherever it appears in the spine. See
//! `linear_field_in_constructor_application` and
//! `linear_recursor_branch_consumes_field_once` below for the Σ-intro/eliminator
//! adversarial pairs. **Automatically-generated inductives are graded too**:
//! [`crate::generate::declare_inductive`] reads each constructor field's grade
//! straight off its own `Π` (`Grade::Many` for the ordinary [`rv_kernel_core::term::Term::pi`],
//! or whatever [`rv_kernel_core::term::Term::pi_graded`] declared) and re-emits that
//! grade on the corresponding synthesized recursor minor-premise binder — so a
//! *generated* inductive's linear/erased field is checked by this same mechanism, with
//! no special-casing: see `generated_recursor_linear_field_discipline`,
//! `generated_recursor_erased_field_relevant_use_rejected`, and the regression guard
//! `ungraded_generated_recursor_unaffected` below. Hand-built (`RawInductive`) or
//! hand-annotated declarations were already fully checked; this closes the residual
//! for the automatic elaborator.
//!
//! ## `let` is graded
//!
//! `Term::Let(grade, ty, value, body)` carries a [`Grade`] on the bound variable,
//! exactly like `Term::Pi`'s binder. [`Term::let_`] (the constructor every existing
//! call site — hand-built terms, `elab.rs`, `elab2.rs`, `unify.rs`'s zonker, …— already
//! used) defaults it to `Grade::Many` (unrestricted), so **every pre-existing `let` is
//! unaffected**: this pass's `Let` rule imposes no discipline unless a `let` was built
//! with the new [`Term::let_graded`] and a non-`ω` grade. The rule follows the standard
//! QTT let-elimination:
//! ```text
//! usage(let x :ᵖ ty := value in body) = usage(body ∖ x) + p · usage(value)
//! ```
//! i.e. `x`'s usage inside `body` must fit `p` (exactly once for `p = 1`), and the
//! *definiens* `value`'s own free-variable usages are scaled by `p` before being added
//! to the total — the same scaling the `App` rule applies to an argument passed at
//! grade `p`. `ty` remains in the erased fragment, as for every other binder's type.
//!
//! The analysis is deliberately a **usage skeleton**, independent of full type
//! inference: it walks the term's structure and consults declared `Π` grades (on
//! `λ` via an inferred expected type, and on application heads via the checker),
//! exactly as [`erase`](crate::erase) does. Where a `Π` grade is not available (e.g.
//! an open application head whose type cannot be found) it falls back to `ω`, which
//! can only *relax* — never tighten — so it stays sound.

use rv_kernel_core::check::{Checker, LocalCtx};
use rv_kernel_core::reduce::Reducer;
use rv_kernel_core::term::{Grade, Term};
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

            // `let (_ :ᵖ ty) := value in body`. Standard QTT let-rule:
            //   usage(let x :ᵖ ty := value in body) = usage(body minus x) + p · usage(value)
            // i.e. the bound variable's usage inside `body` must fit grade `p` (exactly
            // `1` for a linear `p`), and the *definiens*' own usages are scaled by `p`
            // before being added in — mirroring the `App`/`Π` rule where an argument
            // passed at grade `p` costs `p · usage(argument)`. The type is erased, as
            // for every other binder. Default `p = Grade::Many` (via `Term::let_`)
            // reproduces the old unrestricted, unchecked behaviour exactly.
            Term::Let(p, ty, value, body) => {
                let ut = self.infer(ty)?.scale(Grade::Zero);
                let uv = self.infer(value)?.scale(*p);
                let ub = self.under(ty, |s| s.infer(body))?;
                let (u0, urest) = ub.pop_binder();
                self.check_binder(*p, u0, "let")?;
                Ok(ut.add(&uv).add(&urest))
            }

            // An application spine `head a0 a1 …`: start from the head's usage, then for
            // each argument add its usage *scaled by the corresponding Π grade*.
            //
            // Each argument is checked with [`Graded::infer_checked`] against the
            // parameter's *known* domain type (from the head's `Π`), not the blind
            // structural [`Graded::infer`]. This matters precisely when an argument is
            // itself a `λ` (the shape every eliminator "case"/minor-premise argument
            // takes, e.g. `Nat.rec motive case_zero case_succ n`): a bare `λ`'s own
            // grade cannot be recovered by unification-free bidirectional inference
            // ([`Checker::infer`] on a `Lam` always synthesizes an unrestricted `Π`,
            // since ordinary type inference doesn't consult an expected type), so
            // without threading the parameter's declared domain down, a linearly-graded
            // case function's *internal* usage discipline would silently default to `ω`
            // and never be checked. Threading it through closes that gap.
            Term::App(..) => {
                let (head, args) = t.unfold_apps();
                let mut acc = self.infer(&head)?;
                let mut ty = self.reducer().whnf(&self.head_type(&head)?);
                for arg in &args {
                    let Term::Pi(p, dom, cod) = &ty else {
                        // Head type isn't a readable function type: treat the argument as
                        // unrestricted (the sound, never-tightening default).
                        let ua = self.infer(arg)?.scale(Grade::Many);
                        acc = acc.add(&ua);
                        continue;
                    };
                    let (p, dom, cod) = (*p, (**dom).clone(), (**cod).clone());
                    let ua = self.infer_checked(arg, &dom)?.scale(p);
                    acc = acc.add(&ua);
                    ty = self.reducer().whnf(&cod.instantiate(arg));
                }
                Ok(acc)
            }

            // Phase-1 cubical (see `rv_kernel_core::cubical`). `I`/`i0`/`i1` mention no
            // local variables (like `Sort`/`Const`). `PLam` reuses the ordinary `Var`
            // binder machinery (see `Term::PLam`'s doc comment) — it has no explicit
            // grade annotation of its own (unlike `Lam`'s `Π`-derived grade) because an
            // interval variable is never a linear *resource*: it only ever legally
            // occurs in a `PApp`'s interval-typed argument position (enforced by
            // `crate::check`), never consumed at runtime, so it is graded `Many`
            // (unrestricted — the always-safe, never-tightening default, same as an
            // unreadable application head's argument above). `PathP`'s family lives
            // under that same binder, and its two endpoints are ordinary (erased,
            // scale-0, since it's a type) subterms.
            Term::I | Term::IZero | Term::IOne => Ok(Usage::empty()),
            // Phase 3.5 (De Morgan interval, see `rv_kernel_core::cubical`): reversal
            // and the two connections are themselves interval expressions — like
            // `PApp`'s `r` argument below, any variable occurrence inside them is
            // interval-typed, never a runtime resource, so scaled to `0`.
            Term::INeg(r) => Ok(self.infer(r)?.scale(Grade::Zero)),
            Term::IMeet(r, s) | Term::IJoin(r, s) => {
                let ur = self.infer(r)?.scale(Grade::Zero);
                let us = self.infer(s)?.scale(Grade::Zero);
                Ok(ur.add(&us))
            }
            Term::PLam(body) => {
                let ub = self.under(&Term::I, |s| s.infer(body))?;
                let (u0, urest) = ub.pop_binder();
                self.check_binder(Grade::Many, u0, "path abstraction")?;
                Ok(urest)
            }
            Term::PApp(p, r) => {
                let up = self.infer(p)?;
                let ur = self.infer(r)?.scale(Grade::Zero);
                Ok(up.add(&ur))
            }
            Term::PathP(fam, a0, a1) => {
                let uf = self.under(&Term::I, |s| s.infer(fam))?.scale(Grade::Zero);
                let (_, uf) = uf.pop_binder();
                let u0 = self.infer(a0)?.scale(Grade::Zero);
                let u1 = self.infer(a1)?.scale(Grade::Zero);
                Ok(uf.add(&u0).add(&u1))
            }

            // Phase-2 cubical (see `rv_kernel_core::face`). `Partial φ A` is a type
            // (like `PathP`'s endpoints): erased, scale-0. A system's branches are
            // each *possibly* the one that runs (which branch fires isn't known
            // statically at usage-checking time, before whatever substitution would
            // decide `φ_i`) — conservatively sum every branch's usage rather than
            // picking one, so this never *under*-counts a variable's consumption
            // (it may over-restrict a genuinely-linear variable used identically in
            // every branch, but never accepts something that isn't safe).
            Term::Partial(_, a) => Ok(self.infer(a)?.scale(Grade::Zero)),
            Term::Sys(branches) => {
                let mut acc = Usage::empty();
                for (_, t) in branches {
                    acc = acc.add(&self.infer(t)?);
                }
                Ok(acc)
            }

            // Phase-3 cubical (see `rv_kernel_core::kan`): the family/type argument
            // is type-level (scale-0, like `PathP`'s family above); the transported
            // value / cap and the system line are genuine runtime data, so their
            // usage counts for real (not scaled away) — conservative, since it can
            // only over- not under-count a linear variable's consumption.
            Term::Transp(fam, _phi, a) => {
                let uf = self.under(&Term::I, |s| s.infer(fam))?.scale(Grade::Zero);
                let (_, uf) = uf.pop_binder();
                let ua = self.infer(a)?;
                Ok(uf.add(&ua))
            }
            Term::HComp(ty, _phi, u, u0) => {
                let ut = self.infer(ty)?.scale(Grade::Zero);
                let uu = self.under(&Term::I, |s| s.infer(u))?;
                let (_, uu) = uu.pop_binder();
                let u0u = self.infer(u0)?;
                Ok(ut.add(&uu).add(&u0u))
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
    use rv_kernel_core::kernel::Kernel;
    use rv_kernel_core::term::{name, Grade};

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

    // --- Constructors / eliminators (Σ-introduction, recursor branches). -------------
    //
    // The kernel has no dedicated `Sigma`/pair primitive: pairs, inductive
    // constructors, and eliminators (`Nat.rec`, `Quot.lift`, `Trunc.rec`, …) are all
    // ordinary [`Term::Const`]s applied via [`Term::App`], each with a declared `Π`
    // type in the [`Env`]. The `App` case of [`Graded::infer`] already reads that
    // declared `Π`'s grade and scales the argument's usage by it — so a linearly
    // graded constructor field, or a linearly graded recursor "case"/minor-premise
    // argument, is *already* covered by the existing generic rule, with **no code
    // change required**: usage-checking constructors and eliminators is the same
    // mechanism as usage-checking any other application. These tests pin that down.

    /// A "pair" constructor with a **linear** first field: `mk : Π (x :¹ Res). Pair`
    /// (the Σ-introduction analogue). Consuming `x` once to build a pair is accepted;
    /// building two pairs from the same linear `x` (using it twice) is rejected.
    #[test]
    fn linear_field_in_constructor_application() {
        let mut k = Kernel::new();
        k.add_axiom("Res", 0, Term::typ(0)).unwrap();
        k.add_axiom("Pair", 0, Term::typ(0)).unwrap();
        k.add_axiom("mk", 0, Term::pi_graded(Grade::One, cn("Res"), cn("Pair"))).unwrap();
        // dup2 : Res -> Pair -> Pair -> Pair, used to combine two separately-built pairs
        // so that the *same* x can be threaded into both without literally repeating a
        // variable at the top level of a single mk-application (which would already be
        // caught by the ordinary Var(i) accounting).
        k.add_axiom(
            "combine",
            0,
            Term::arrow(cn("Pair"), Term::arrow(cn("Pair"), cn("Pair"))),
        )
        .unwrap();

        let ty = Term::pi_graded(Grade::One, cn("Res"), cn("Pair"));

        // OK: x flows into exactly one `mk`.
        let once = Term::lam(cn("Res"), Term::app(cn("mk"), Term::Var(0)));
        k.add_definition("mk_once", 0, ty.clone(), once.clone()).unwrap();
        assert!(check_usage_against(k.env(), &once, &ty).is_ok());

        // Rejected: x flows into `mk` twice (two Σ-introductions of the same linear
        // resource), combined downstream — the usage discipline must see through the
        // application spine and reject the double consumption.
        let twice = Term::lam(
            cn("Res"),
            Term::apps(
                cn("combine"),
                [
                    Term::app(cn("mk"), Term::Var(0)),
                    Term::app(cn("mk"), Term::Var(0)),
                ],
            ),
        );
        let err = check_usage_against(k.env(), &twice, &ty).unwrap_err();
        assert!(matches!(err, GradeError::UsageMismatch { .. }), "got {err}");
    }

    /// A hand-built unary inductive `Box A` with a linear payload constructor and a
    /// recursor whose *case* (minor premise) is itself graded linear in its own
    /// argument — modelling a recursor branch that must consume its bound field
    /// exactly once. Exercises that `Graded::infer` correctly checks the usage
    /// discipline *inside* a lambda passed as an argument to another application (the
    /// shape every recursor invocation `Box.rec C case b` takes), not just at the
    /// top level of a definition.
    #[test]
    fn linear_recursor_branch_consumes_field_once() {
        let mut k = Kernel::new();
        k.add_axiom("Res", 0, Term::typ(0)).unwrap();
        k.add_axiom("Box", 0, Term::typ(0)).unwrap();
        k.add_axiom("mk", 0, Term::pi_graded(Grade::One, cn("Res"), cn("Box"))).unwrap();
        // rec : Π (case :¹ Π (x :¹ Res). Res) (b : Box). Res  — non-dependent motive,
        // the case itself demanded exactly once (it's the sole way to consume `b`),
        // and its own bound field demanded exactly once.
        let case_ty = Term::pi_graded(Grade::One, cn("Res"), cn("Res"));
        let rec_ty = Term::pi_graded(
            Grade::One,
            case_ty.clone(),
            Term::pi_graded(Grade::One, cn("Box"), cn("Res")),
        );
        k.add_axiom("rec", 0, rec_ty).unwrap();

        // caller : Π (b :¹ Box). Res := rec (λ x. x) b — the branch consumes its field
        // exactly once. Accepted.
        let good_branch = Term::lam(cn("Res"), Term::Var(0));
        let caller_ty = Term::pi_graded(Grade::One, cn("Box"), cn("Res"));
        let good_caller = Term::lam(
            cn("Box"),
            Term::apps(cn("rec"), [good_branch, Term::Var(0)]),
        );
        k.add_definition("caller_ok", 0, caller_ty.clone(), good_caller.clone()).unwrap();
        assert!(check_usage_against(k.env(), &good_caller, &caller_ty).is_ok());

        // Rejected: the branch drops its linear field (`λ x. res_const`) — a leaked
        // resource inside a recursor case.
        k.add_axiom("res_const", 0, cn("Res")).unwrap();
        let dropping_branch = Term::lam(cn("Res"), cn("res_const"));
        let bad_caller = Term::lam(
            cn("Box"),
            Term::apps(cn("rec"), [dropping_branch, Term::Var(0)]),
        );
        let err = check_usage_against(k.env(), &bad_caller, &caller_ty).unwrap_err();
        assert!(matches!(err, GradeError::LinearUnused { .. }), "got {err}");
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

    // --- `let`-binder grades. ---------------------------------------------------------
    //
    // `Term::let_graded(p, ty, value, body)` grades the let-bound variable exactly like
    // a `Π`: `usage(let x :ᵖ ty := value in body) = usage(body ∖ x) + p · usage(value)`.
    // `Term::let_` (the default constructor every pre-existing call site uses) grades
    // `ω`, so these tests exercise only the *new*, opt-in `let_graded` path.

    /// A linear `let` whose body consumes the bound variable exactly once: accepted.
    #[test]
    fn linear_let_used_once_accepted() {
        let env = Env::new();
        // let y :¹ Type0 := Type0 in y   (using Sort as a stand-in inhabitant so this
        // needs no axioms; only the usage skeleton is under test, not typing).
        let t = Term::let_graded(Grade::One, Term::typ(0), Term::typ(0), Term::Var(0));
        assert!(check_usage(&env, &t).is_ok());
    }

    /// A linear `let` whose body drops the bound variable: rejected (`LinearUnused`).
    #[test]
    fn linear_let_dropped_rejected() {
        let env = Env::new();
        let t = Term::let_graded(Grade::One, Term::typ(0), Term::typ(0), Term::typ(0));
        assert!(matches!(check_usage(&env, &t), Err(GradeError::LinearUnused { .. })));
    }

    /// A linear `let` whose body consumes the bound variable **twice**: rejected. This
    /// is "a linear resource consumed twice across a `let`" — the duplication happens
    /// entirely inside the let-body, so the let's own binder-discipline check (not the
    /// outer one) must catch it.
    #[test]
    fn linear_let_duplicated_in_body_rejected() {
        let mut k = Kernel::new();
        k.add_axiom("Res", 0, Term::typ(0)).unwrap();
        k.add_axiom("dup", 0, Term::arrow(cn("Res"), Term::arrow(cn("Res"), cn("Res")))).unwrap();
        // let y :¹ Res := <axiom witness> in dup y y
        k.add_axiom("r", 0, cn("Res")).unwrap();
        let t = Term::let_graded(
            Grade::One,
            cn("Res"),
            cn("r"),
            Term::apps(cn("dup"), [Term::Var(0), Term::Var(0)]),
        );
        let err = check_usage(k.env(), &t).unwrap_err();
        assert!(matches!(err, GradeError::UsageMismatch { .. }), "got {err}");
    }

    /// A linear **outer** resource consumed twice *across* two separate `let`s (not by
    /// repeating the variable within a single let-body): `λ (x :¹ Res). combine (let
    /// y1 := x in y1) (let y2 := x in y2)`. Each individual `let` only uses `x` once in
    /// its own definiens, but `x` is fed into two lets, so its total outer usage is `2`
    /// (saturating to `ω`), which does not fit the outer binder's linear grade — must be
    /// rejected even though no single `let`-body duplicates anything.
    #[test]
    fn linear_resource_consumed_twice_across_separate_lets_rejected() {
        let mut k = Kernel::new();
        k.add_axiom("Res", 0, Term::typ(0)).unwrap();
        k.add_axiom(
            "combine",
            0,
            Term::arrow(cn("Res"), Term::arrow(cn("Res"), cn("Res"))),
        )
        .unwrap();
        let ty = Term::pi_graded(Grade::One, cn("Res"), cn("Res"));
        let one_let = |v: Term| Term::let_graded(Grade::One, cn("Res"), v, Term::Var(0));
        let body = Term::apps(
            cn("combine"),
            [one_let(Term::Var(0)), one_let(Term::Var(0))],
        );
        let term = Term::lam(cn("Res"), body);
        k.add_definition("bad_double_let", 0, ty.clone(), term.clone()).unwrap();
        let err = check_usage_against(k.env(), &term, &ty).unwrap_err();
        assert!(matches!(err, GradeError::UsageMismatch { .. }), "got {err}");
    }

    /// The accepted counterpart: the same outer linear resource routed through a
    /// **single** `let`, used exactly once downstream — accepted.
    #[test]
    fn linear_resource_through_single_let_used_once_accepted() {
        let mut k = Kernel::new();
        k.add_axiom("Res", 0, Term::typ(0)).unwrap();
        let ty = Term::pi_graded(Grade::One, cn("Res"), cn("Res"));
        // λ (x :¹ Res). let y :¹ Res := x in y
        let term = Term::lam(
            cn("Res"),
            Term::let_graded(Grade::One, cn("Res"), Term::Var(0), Term::Var(0)),
        );
        k.add_definition("good_single_let", 0, ty.clone(), term.clone()).unwrap();
        assert!(check_usage_against(k.env(), &term, &ty).is_ok());
    }

    /// An **erased** (`0`) `let` binding used at a relevant (computational) position in
    /// its body is rejected; used only in erased/type position is fine.
    #[test]
    fn erased_let_used_relevantly_rejected() {
        let env = Env::new();
        let bad = Term::let_graded(Grade::Zero, Term::typ(0), Term::typ(0), Term::Var(0));
        assert!(matches!(
            check_usage(&env, &bad),
            Err(GradeError::UsageMismatch { .. })
        ));
        // Not used at all: fine (erased bindings may be dropped).
        let ok = Term::let_graded(Grade::Zero, Term::typ(0), Term::typ(0), Term::typ(0));
        assert!(check_usage(&env, &ok).is_ok());
    }

    /// A linear resource duplicated **across a recursor/match branch chain**: the
    /// dropping case of [`linear_recursor_branch_consumes_field_once`] shows a branch
    /// that leaks its field; this is the dual — a branch that consumes its bound field
    /// **twice**.
    #[test]
    fn linear_recursor_branch_duplicates_field_rejected() {
        let mut k = Kernel::new();
        k.add_axiom("Res", 0, Term::typ(0)).unwrap();
        k.add_axiom("Box", 0, Term::typ(0)).unwrap();
        k.add_axiom("mk", 0, Term::pi_graded(Grade::One, cn("Res"), cn("Box"))).unwrap();
        k.add_axiom("dup", 0, Term::arrow(cn("Res"), Term::arrow(cn("Res"), cn("Res")))).unwrap();
        let case_ty = Term::pi_graded(Grade::One, cn("Res"), cn("Res"));
        let rec_ty = Term::pi_graded(
            Grade::One,
            case_ty,
            Term::pi_graded(Grade::One, cn("Box"), cn("Res")),
        );
        k.add_axiom("rec", 0, rec_ty).unwrap();

        // λ (b :¹ Box). rec (λ x. dup x x) b — the branch consumes its field twice.
        let dup_branch =
            Term::lam(cn("Res"), Term::apps(cn("dup"), [Term::Var(0), Term::Var(0)]));
        let caller_ty = Term::pi_graded(Grade::One, cn("Box"), cn("Res"));
        let caller = Term::lam(cn("Box"), Term::apps(cn("rec"), [dup_branch, Term::Var(0)]));
        k.add_definition("caller_dup", 0, caller_ty.clone(), caller.clone()).unwrap();
        let err = check_usage_against(k.env(), &caller, &caller_ty).unwrap_err();
        assert!(matches!(err, GradeError::UsageMismatch { .. }), "got {err}");
    }

    /// Worked ownership-flavored example: a linear `Handle` threaded through a `let`
    /// *and* a recursor ("match") — accepted when consumed exactly once along the path,
    /// rejected if the branch duplicates it. Models `let h2 = h in match () { () => close
    /// h2 }` versus a branch that calls `close` twice.
    #[test]
    fn linear_handle_through_let_and_match_discipline() {
        let mut k = Kernel::new();
        k.add_axiom("Handle", 0, Term::typ(0)).unwrap();
        k.add_axiom("Unit", 0, Term::typ(0)).unwrap();
        k.add_axiom("close", 0, Term::pi_graded(Grade::One, cn("Handle"), cn("Unit")))
            .unwrap();
        // A trivial unary "match": rec : Π (case :¹ Π (h :¹ Handle). Unit) (b :¹ Handle). Unit
        let case_ty = Term::pi_graded(Grade::One, cn("Handle"), cn("Unit"));
        let rec_ty = Term::pi_graded(
            Grade::One,
            case_ty,
            Term::pi_graded(Grade::One, cn("Handle"), cn("Unit")),
        );
        k.add_axiom("rec", 0, rec_ty).unwrap();
        let ty = Term::pi_graded(Grade::One, cn("Handle"), cn("Unit"));

        // OK: let h2 :¹ Handle := h in rec (λ h3. close h3) h2 — a single consuming path.
        let good_branch = Term::lam(cn("Handle"), Term::app(cn("close"), Term::Var(0)));
        let good = Term::lam(
            cn("Handle"),
            Term::let_graded(
                Grade::One,
                cn("Handle"),
                Term::Var(0),
                Term::apps(cn("rec"), [good_branch, Term::Var(0)]),
            ),
        );
        k.add_definition("handle_ok", 0, ty.clone(), good.clone()).unwrap();
        assert!(check_usage_against(k.env(), &good, &ty).is_ok());

        // Rejected: the branch closes the handle twice.
        k.add_axiom(
            "close2",
            0,
            Term::arrow(cn("Handle"), Term::arrow(cn("Handle"), cn("Unit"))),
        )
        .unwrap();
        let dup_branch = Term::lam(
            cn("Handle"),
            Term::apps(cn("close2"), [Term::Var(0), Term::Var(0)]),
        );
        let bad = Term::lam(
            cn("Handle"),
            Term::let_graded(
                Grade::One,
                cn("Handle"),
                Term::Var(0),
                Term::apps(cn("rec"), [dup_branch, Term::Var(0)]),
            ),
        );
        let err = check_usage_against(k.env(), &bad, &ty).unwrap_err();
        assert!(matches!(err, GradeError::UsageMismatch { .. }), "got {err}");
    }

    // --- Per-field grades on *automatically generated* inductives (`declare_inductive`). --
    //
    // Everything above hand-builds its `Π`s. These tests close the residual documented
    // at the top of this module: `IndSpec`/`CtorSpec` field grades (read straight off a
    // constructor's own `Π`, via `Term::pi_graded`) are now threaded by
    // `crate::generate::declare_inductive` into the *synthesized* recursor's minor
    // premises, so a case handler for a generated inductive is subject to the same
    // linear/erased discipline as a hand-built one.

    use crate::generate::{declare_inductive, CtorSpec, IndSpec};
    use rv_kernel_core::level::Level;

    /// `GBox : Type0` with a single constructor `GBox.mk : Π (x :¹ Res). GBox` — a
    /// *generated* inductive whose sole field is declared **linear**. Returns the
    /// environment plus the recursor's `Π` type (needed to build well-typed case
    /// handlers against it).
    fn linear_gbox_env() -> Kernel {
        let mut k = Kernel::new();
        k.add_axiom("Res", 0, Term::typ(0)).unwrap();
        let spec = IndSpec {
            name: name("GBox"),
            num_levels: 0,
            ty: Term::typ(0),
            num_params: 0,
            ctors: vec![CtorSpec {
                name: name("GBox.mk"),
                // The field's own `Π` is graded linear — this is the only surface
                // needed to declare a linear field; no new `IndSpec` field required.
                ty: Term::pi_graded(Grade::One, cn("Res"), cn("GBox")),
            }],
            rec_name: name("GBox.rec"),
        };
        declare_inductive(k.env_mut(), spec).unwrap();
        k
    }

    /// `GBox.rec.{1} : Π (motive : GBox → Type1) (mk_case : Π (x :¹ Res). motive (GBox.mk x))
    ///                   (b : GBox), motive b`
    /// Build one application of `GBox.rec` to a non-dependent motive `λ_.Res` and the
    /// given `mk_case` handler, scrutinizing `Var(0)` (a bound `GBox`).
    fn gbox_rec_app(mk_case: Term) -> Term {
        Term::apps(
            Term::cnst(name("GBox.rec"), vec![Level::of_nat(1)]),
            [
                Term::lam(cn("GBox"), cn("Res")), // motive : GBox -> Res  (non-dependent target Res)
                mk_case,
                Term::Var(0),
            ],
        )
    }

    /// Worked/adversarial suite: a generated inductive's linear field is enforced by
    /// the usage pass through its synthesized recursor.
    #[test]
    fn generated_recursor_linear_field_discipline() {
        let k = linear_gbox_env();
        // The scrutinee `GBox` itself is passed to the recursor's (ungraded) major
        // premise, so the outer binder is unrestricted; it is the *field* inside the
        // case handler — threaded onto the minor premise — that is declared linear.
        let ty = Term::pi_graded(Grade::Many, cn("GBox"), cn("Res"));

        // ACCEPTED: the case handler uses the linear field exactly once (returns it).
        let used_once = Term::lam(cn("GBox"), gbox_rec_app(Term::lam(cn("Res"), Term::Var(0))));
        assert!(
            check_usage_against(k.env(), &used_once, &ty).is_ok(),
            "case handler consuming the linear field exactly once should be accepted"
        );

        // REJECTED: the case handler drops the linear field (ignores `x`, returns a
        // constant instead).
        let mut k2 = linear_gbox_env();
        k2.add_axiom("r0", 0, cn("Res")).unwrap();
        let dropped = Term::lam(cn("GBox"), gbox_rec_app(Term::lam(cn("Res"), cn("r0"))));
        let err = check_usage_against(k2.env(), &dropped, &ty).unwrap_err();
        assert!(
            matches!(err, GradeError::LinearUnused { .. }),
            "dropping the linear field should be rejected, got {err}"
        );

        // REJECTED: the case handler duplicates the linear field (`dup x x`).
        let mut k3 = linear_gbox_env();
        k3.add_axiom("dup", 0, Term::arrow(cn("Res"), Term::arrow(cn("Res"), cn("Res")))).unwrap();
        let duplicated = Term::lam(
            cn("GBox"),
            gbox_rec_app(Term::lam(cn("Res"), Term::apps(cn("dup"), [Term::Var(0), Term::Var(0)]))),
        );
        let err = check_usage_against(k3.env(), &duplicated, &ty).unwrap_err();
        assert!(
            matches!(err, GradeError::UsageMismatch { .. }),
            "duplicating the linear field should be rejected, got {err}"
        );
    }

    /// An **erased** generated field used in a computationally-relevant position is
    /// rejected: `GEBox.mk : Π (x :⁰ Res). GEBox` whose case handler returns `x`.
    #[test]
    fn generated_recursor_erased_field_relevant_use_rejected() {
        let mut k = Kernel::new();
        k.add_axiom("Res", 0, Term::typ(0)).unwrap();
        let spec = IndSpec {
            name: name("GEBox"),
            num_levels: 0,
            ty: Term::typ(0),
            num_params: 0,
            ctors: vec![CtorSpec {
                name: name("GEBox.mk"),
                ty: Term::pi_graded(Grade::Zero, cn("Res"), cn("GEBox")),
            }],
            rec_name: name("GEBox.rec"),
        };
        declare_inductive(k.env_mut(), spec).unwrap();

        let ty = Term::pi_graded(Grade::Many, cn("GEBox"), cn("Res"));
        let rec_app = |case: Term| {
            Term::apps(
                Term::cnst(name("GEBox.rec"), vec![Level::of_nat(1)]),
                [Term::lam(cn("GEBox"), cn("Res")), case, Term::Var(0)],
            )
        };
        // Relevantly returning the erased field: rejected.
        let relevant = Term::lam(cn("GEBox"), rec_app(Term::lam(cn("Res"), Term::Var(0))));
        let err = check_usage_against(k.env(), &relevant, &ty).unwrap_err();
        assert!(matches!(err, GradeError::UsageMismatch { .. }), "got {err}");

        // Never touching it (erased field simply dropped): accepted.
        k.add_axiom("r0", 0, cn("Res")).unwrap();
        let dropped = Term::lam(cn("GEBox"), rec_app(Term::lam(cn("Res"), cn("r0"))));
        assert!(check_usage_against(k.env(), &dropped, &ty).is_ok());
    }

    /// Regression guard: an inductive declared **without** any field grade (the entire
    /// pre-existing `IndSpec` corpus, e.g. `nat_spec`/`list_spec`) synthesizes exactly
    /// the same recursor shape as before — every field/minor-premise binder is still
    /// `Grade::Many`, so no case handler is newly restricted.
    #[test]
    fn ungraded_generated_recursor_unaffected() {
        let mut env = Env::new();
        declare_inductive(&mut env, crate::generate::nat_spec()).unwrap();
        declare_inductive(&mut env, crate::generate::list_spec()).unwrap();

        // Nat.rec's minor premises stay Grade::Many: check `Nat.succ`'s field/IH.
        let rec_ty = env.get("Nat.rec").unwrap().ty().clone();
        // Π motive. Π z. Π (n:Nat) (ih: motive n -> motive (succ n)). Π t. motive t
        // Walk down to the succ-case Π and confirm its binder grades are Many.
        fn all_pi_grades_many(t: &Term) -> bool {
            match t {
                Term::Pi(g, d, b) => *g == Grade::Many && all_pi_grades_many(d) && all_pi_grades_many(b),
                Term::Lam(d, b) => all_pi_grades_many(d) && all_pi_grades_many(b),
                Term::App(f, a) => all_pi_grades_many(f) && all_pi_grades_many(a),
                Term::Let(_, t, v, b) => all_pi_grades_many(t) && all_pi_grades_many(v) && all_pi_grades_many(b),
                _ => true,
            }
        }
        assert!(all_pi_grades_many(&rec_ty), "ungraded Nat.rec must have every Π at Grade::Many");

        let list_rec_ty = env.get("List.rec").unwrap().ty().clone();
        assert!(all_pi_grades_many(&list_rec_ty), "ungraded List.rec must have every Π at Grade::Many");

        // And the usage pass accepts an ordinary (non-linear) case handler unchanged,
        // exactly as `generated_list_recursion_computes` in `generate.rs` exercises
        // computationally.
        let nat = || cn("Nat");
        let length_ty = Term::pi(Term::app(cn("List"), nat()), nat());
        let length = Term::lam(
            Term::app(cn("List"), nat()),
            Term::apps(
                Term::cnst(name("List.rec"), vec![Level::of_nat(1)]),
                [
                    nat(),
                    Term::lam(Term::app(cn("List"), nat()), nat()),
                    cn("Nat.zero"),
                    Term::lam(
                        nat(),
                        Term::lam(
                            Term::app(cn("List"), nat()),
                            Term::lam(nat(), Term::app(cn("Nat.succ"), Term::Var(0))),
                        ),
                    ),
                    Term::Var(0),
                ],
            ),
        );
        assert!(check_usage_against(&env, &length, &length_ty).is_ok());
    }
}
