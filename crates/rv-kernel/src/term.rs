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
/// identical to the ungraded system, hence sound); the separate [`crate::erase`]
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
    /// `let (_ : ty) := value in body` — `body` is under one binder.
    Let(Rc<Term>, Rc<Term>, Rc<Term>),
    /// An **elaboration-only** metavariable (a hole to be solved by unification). The
    /// trusted type-checker *rejects* any term still containing one; the elaborator
    /// solves and zonks all metas away before a term reaches the kernel. Atomic (its
    /// solution lives in the metacontext, not as subterms here).
    Meta(u32),
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
    pub fn let_(ty: Term, value: Term, body: Term) -> Term {
        Term::Let(Rc::new(ty), Rc::new(value), Rc::new(body))
    }

    /// Re-index free variables: add `amount` to every `Var(i)` with `i >= cutoff`.
    /// Used to move a term under `amount` new binders (`cutoff` counts the binders
    /// already crossed). `amount` may be negative to *remove* binders, valid only
    /// when no free variable in range `[cutoff, cutoff)` would underflow.
    pub fn lift(&self, amount: isize, cutoff: usize) -> Term {
        match self {
            Term::Sort(_) | Term::Const(..) | Term::Meta(_) => self.clone(),
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
            Term::Let(t, v, b) => {
                Term::let_(t.lift(amount, cutoff), v.lift(amount, cutoff), b.lift(amount, cutoff + 1))
            }
        }
    }

    /// Substitute `replacement` for the variable at de Bruijn `depth`, decrementing
    /// the free variables above it (they lose the binder being eliminated). The
    /// replacement is lifted by `depth` so its own free variables stay correct under
    /// the binders it now sits beneath.
    fn subst(&self, depth: usize, replacement: &Term) -> Term {
        match self {
            Term::Sort(_) | Term::Const(..) | Term::Meta(_) => self.clone(),
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
            Term::Let(t, v, b) => Term::let_(
                t.subst(depth, replacement),
                v.subst(depth, replacement),
                b.subst(depth + 1, replacement),
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
    fn subst_ctx_go(&self, images: &[Term], depth: usize) -> Term {
        match self {
            Term::Sort(_) | Term::Const(..) | Term::Meta(_) => self.clone(),
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
            Term::Let(t, v, b) => Term::let_(
                t.subst_ctx_go(images, depth),
                v.subst_ctx_go(images, depth),
                b.subst_ctx_go(images, depth + 1),
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
            Term::Var(_) | Term::Meta(_) => self.clone(),
            Term::Const(n, ls) => {
                Term::Const(n.clone(), ls.iter().map(|l| l.instantiate(args)).collect())
            }
            Term::App(f, a) => Term::app(f.instantiate_levels(args), a.instantiate_levels(args)),
            Term::Lam(d, b) => Term::lam(d.instantiate_levels(args), b.instantiate_levels(args)),
            Term::Pi(g, d, b) => {
                Term::pi_graded(*g, d.instantiate_levels(args), b.instantiate_levels(args))
            }
            Term::Let(t, v, b) => Term::let_(
                t.instantiate_levels(args),
                v.instantiate_levels(args),
                b.instantiate_levels(args),
            ),
        }
    }

    /// Does this term contain an (unsolved) metavariable — a [`Term::Meta`], or a
    /// [`Level::Meta`] inside a `Sort`/`Const`? The kernel uses this to reject any term
    /// that still carries elaboration holes, so nothing un-zonked is ever trusted.
    pub fn has_meta(&self) -> bool {
        match self {
            Term::Meta(_) => true,
            Term::Var(_) => false,
            Term::Sort(l) => l.has_meta(),
            Term::Const(_, ls) => ls.iter().any(|l| l.has_meta()),
            Term::App(f, a) => f.has_meta() || a.has_meta(),
            Term::Lam(d, b) => d.has_meta() || b.has_meta(),
            Term::Pi(_, d, b) => d.has_meta() || b.has_meta(),
            Term::Let(t, v, b) => t.has_meta() || v.has_meta() || b.has_meta(),
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
    /// unification errors). Unlike [`crate::verify::render`] — which is for *runtime
    /// values* and collapses functions to `<function>` — this shows the full term:
    /// de Bruijn variables get generated binder names (`a`, `b`, …), declaration and
    /// constructor names print directly, arrows collapse to `A -> B` when non-dependent,
    /// and unsolved metavariables show as `?n`.
    pub fn pretty(&self) -> String {
        self.pp(&mut Vec::new(), 0)
    }

    fn pp(&self, names: &mut Vec<String>, prec: u8) -> String {
        // prec: 0 = top-level, 2 = needs parens if a binder/arrow, 3 = atom (app argument).
        match self {
            Term::Sort(l) => format!("Sort {l:?}"),
            Term::Meta(m) => format!("?{m}"),
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
            Term::Let(ty, val, body) => {
                let nm = fresh_binder_name(names.len());
                let tys = ty.pp(names, 0);
                let vs = val.pp(names, 0);
                names.push(nm.clone());
                let bs = body.pp(names, 0);
                names.pop();
                paren_if(prec >= 2, format!("let {nm} : {tys} := {vs} in {bs}"))
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
fn mentions_var(t: &Term, k: usize) -> bool {
    match t {
        Term::Var(i) => *i == k,
        Term::App(f, a) => mentions_var(f, k) || mentions_var(a, k),
        Term::Lam(d, b) => mentions_var(d, k) || mentions_var(b, k + 1),
        Term::Pi(_, d, b) => mentions_var(d, k) || mentions_var(b, k + 1),
        Term::Let(ty, v, b) => mentions_var(ty, k) || mentions_var(v, k) || mentions_var(b, k + 1),
        Term::Sort(_) | Term::Const(..) | Term::Meta(_) => false,
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
