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
    /// the line), produces the composite at `i1`. Only the trivial (`φ = ⊤`) rule is
    /// implemented — see `crate::kan`.
    HComp(Rc<Term>, Rc<Cof>, Rc<Term>, Rc<Term>),
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
    /// `hcomp A φ u u0` (see [`Term::HComp`]).
    pub fn hcomp(ty: Term, phi: Cof, u: Term, u0: Term) -> Term {
        Term::HComp(Rc::new(ty), Rc::new(phi), Rc::new(u), Rc::new(u0))
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
        }
    }

    /// β/ζ/ι workhorse: replace the outermost bound variable (`Var(0)`) of a body
    /// with `arg`. `self` is the body living under exactly one binder.
    pub fn instantiate(&self, arg: &Term) -> Term {
        self.subst(0, arg)
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
            Term::PLam(b) => b.has_meta(),
            Term::PApp(p, r) => p.has_meta() || r.has_meta(),
            Term::PathP(fam, a0, a1) => fam.has_meta() || a0.has_meta() || a1.has_meta(),
            Term::Sys(branches) => branches.iter().any(|(p, t)| p.has_meta() || t.has_meta()),
            Term::Partial(p, a) => p.has_meta() || a.has_meta(),
            Term::Transp(fam, phi, a) => fam.has_meta() || phi.has_meta() || a.has_meta(),
            Term::HComp(ty, phi, u, u0) => {
                ty.has_meta() || phi.has_meta() || u.has_meta() || u0.has_meta()
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
    }
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
