//! Erasure: turn a well-typed kernel term into the runtime program it compiles to,
//! by deleting everything at grade `0` (ghosts: proofs, specs, type arguments).
//!
//! This is the analysis that *uses* the [`Grade`](rv_kernel_core::term::Grade)s the
//! type-checker only carries. It is **type-directed**: the grade of an argument lives
//! on the function's `Π` type, so we follow declared types to decide what to drop. It
//! does two jobs at once:
//!
//! * **erase** — produce an untyped [`Erased`] runtime term with ghost arguments and
//!   binders removed (the de Bruijn indices are renumbered accordingly);
//! * **check the grade discipline** — if a grade-`0` (ghost) binder is ever used in a
//!   runtime-relevant position, that's an error. This is the property that justifies
//!   erasing it (Atkey's QTT erasure theorem in miniature): a sound `erase` means the
//!   ghost genuinely cannot influence the result.
//!
//! The spec/proof/exec distinction is exactly this: "proof"/"spec" = grade `0` (gone
//! after `erase`), "exec" = grade `1`/`ω` (kept). No keywords — the grades decide.

use rv_kernel_core::check::{Checker, LocalCtx};
use rv_kernel_core::env::Decl;
use rv_kernel_core::reduce::Reducer;
use rv_kernel_core::term::{Grade, Name, Term};
use crate::Env;

/// An untyped runtime term — what's left after ghosts are erased.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Erased {
    Var(usize),
    Lam(Box<Erased>),
    App(Box<Erased>, Box<Erased>),
    Const(Name),
    /// A position that was purely static (a type/sort) and carries no runtime value.
    Opaque,
}

impl Erased {
    pub fn app(f: Erased, a: Erased) -> Erased {
        Erased::App(Box::new(f), Box::new(a))
    }
    pub fn lam(b: Erased) -> Erased {
        Erased::Lam(Box::new(b))
    }
}

struct Eraser<'a> {
    env: &'a Env,
    /// Binder stack, innermost last: each binder's `(type, kept?)`.
    binders: Vec<(Term, bool)>,
}

impl<'a> Eraser<'a> {
    fn reducer(&self) -> Reducer<'a> {
        Reducer::new(self.env)
    }

    /// The local typing context (all binders, for occasional inference).
    fn ctx(&self) -> LocalCtx {
        let mut c = LocalCtx::new();
        for (ty, _) in &self.binders {
            c.push(ty.clone());
        }
        c
    }

    /// Type of `Var(i)`, re-indexed into the current context.
    fn var_type(&self, i: usize) -> Option<Term> {
        let n = self.binders.len();
        if i >= n {
            return None;
        }
        Some(self.binders[n - 1 - i].0.lift(i as isize + 1, 0))
    }

    /// Erased de Bruijn index of original `Var(i)`: how many *kept* binders are
    /// strictly inside it.
    fn erased_index(&self, i: usize) -> usize {
        let n = self.binders.len();
        (0..i).filter(|&k| self.binders[n - 1 - k].1).count()
    }

    /// Is `expected` a proposition — i.e. does its type normalize to `Prop` (`Sort 0`)?
    /// A term of such a type is proof-irrelevant and erases to nothing. Returns `false`
    /// if the sort cannot be inferred (then ordinary erasure proceeds), so this can only
    /// ever *drop* genuine proofs, never keep one that should be runtime.
    fn expected_is_prop(&self, expected: &Term) -> bool {
        match Checker::new(self.env).infer(&mut self.ctx(), expected) {
            Ok(sort) => {
                matches!(self.reducer().whnf(&sort), Term::Sort(l) if matches!(l.normalize(), crate::Level::Zero))
            }
            Err(_) => false,
        }
    }

    /// The grade-bearing type of a spine head.
    fn head_type(&self, head: &Term) -> Result<Term, String> {
        match head {
            Term::Const(n, ls) => self
                .env
                .get(n)
                .map(|d| d.ty().instantiate_levels(ls))
                .ok_or_else(|| format!("unknown constant '{n}' during erasure")),
            Term::Var(i) => {
                self.var_type(*i).ok_or_else(|| "unbound variable during erasure".to_string())
            }
            other => {
                // A λ in head position (a redex), etc.: fall back to inference.
                Checker::new(self.env).infer(&mut self.ctx(), other)
            }
        }
    }

    fn erase(&mut self, t: &Term, expected: &Term) -> Result<Erased, String> {
        // Proof irrelevance: if `t`'s type is a proposition (`expected : Prop`), then `t`
        // is a *proof* and carries no runtime content — erase it to nothing. This is the
        // QTT/`Prop` erasure rule: proofs (and proof-returning functions, whose Π-type
        // lands back in `Prop` by impredicativity) cost zero bytes at runtime, which is
        // what justifies checking them in the kernel and running only what is left.
        if self.expected_is_prop(expected) {
            return Ok(Erased::Opaque);
        }
        match t {
            // ζ: erase through a `let` by substitution.
            Term::Let(_, _, v, b) => self.erase(&b.instantiate(v), expected),

            // A λ: the binder's grade comes from the expected Π type.
            Term::Lam(dom, body) => {
                let exp = self.reducer().whnf(expected);
                let (grade, codom) = match &exp {
                    Term::Pi(g, _, b) => (*g, (**b).clone()),
                    // No Π available (shouldn't happen for well-typed code): keep it.
                    _ => (Grade::Many, Term::Sort(crate::Level::Zero)),
                };
                let keep = grade != Grade::Zero;
                self.binders.push(((**dom).clone(), keep));
                let inner = self.erase(body, &codom);
                self.binders.pop();
                let inner = inner?;
                Ok(if keep { Erased::lam(inner) } else { inner })
            }

            // Everything else is an application spine `head a0 a1 …` (possibly empty).
            _ => {
                let (head, args) = t.unfold_apps();
                if args.is_empty() {
                    return self.erase_atom(&head);
                }
                let mut acc = self.erase_atom(&head)?;
                let mut ty = self.reducer().whnf(&self.head_type(&head)?);
                for arg in &args {
                    let Term::Pi(g, dom, cod) = &ty else {
                        return Err(format!("erasure: applying a non-function, type {ty:?}"));
                    };
                    let (g, dom, cod) = (*g, (**dom).clone(), (**cod).clone());
                    if g != Grade::Zero {
                        acc = Erased::app(acc, self.erase(arg, &dom)?);
                    }
                    ty = self.reducer().whnf(&cod.instantiate(arg));
                }
                Ok(acc)
            }
        }
    }

    fn erase_atom(&mut self, head: &Term) -> Result<Erased, String> {
        match head {
            // Metas are elaboration-only; a well-formed term reaching erasure has none.
            Term::Meta(m) => Err(format!("unsolved metavariable ?{m} during erasure")),
            Term::Const(n, _) => Ok(Erased::Const(n.clone())),
            Term::Var(i) => {
                let n = self.binders.len();
                if !self.binders[n - 1 - i].1 {
                    return Err(
                        "grade-0 (ghost) variable used in a runtime-relevant position".to_string()
                    );
                }
                Ok(Erased::Var(self.erased_index(*i)))
            }
            // Sorts and Π are static — no runtime content. Phase-1 cubical (see
            // `rv_kernel_core::cubical`) is likewise all proof-layer: `I`/`i0`/`i1` are
            // interval-sort terms (never runtime data) and `PathP` is a type former.
            // Phase-2 cubical (see `rv_kernel_core::face`): `Partial φ A` is a type
            // former (static, no runtime content), same footing as `PathP`.
            Term::Sort(_)
            | Term::Pi(..)
            | Term::I
            | Term::IZero
            | Term::IOne
            | Term::PathP(..)
            | Term::Partial(..) => Ok(Erased::Opaque),
            // A system is check-only (see `rv_kernel_core::check::Checker::infer`'s
            // `Term::Sys` arm) — without a known `Partial φ A` expected type there is
            // nothing to erase it against.
            Term::Sys(..) => Err(
                "cannot erase a system [φ ↦ t, …] without a known `Partial φ A` expected type"
                    .to_string(),
            ),
            // Phase-3 cubical (see `rv_kernel_core::kan`): no surface syntax produces
            // these yet (mirrors `Term::Sys` above); treat as unsupported rather than
            // silently opaque, since — unlike `PathP`/`Partial` — they compute actual
            // runtime data, not a type former.
            Term::Transp(..) | Term::HComp(..) => {
                Err("erasure of `transp`/`hcomp` is not yet supported".to_string())
            }
            // A λ encountered as an atom: erase against its inferred type.
            Term::Lam(..) => {
                let ty = Checker::new(self.env).infer(&mut self.ctx(), head)?;
                self.erase(head, &ty)
            }
            // A path abstraction/application encountered as an atom (no expected type
            // supplied): infer its type the same way `Lam` does above.
            Term::PLam(..) | Term::PApp(..) => {
                let ty = Checker::new(self.env).infer(&mut self.ctx(), head)?;
                self.erase(head, &ty)
            }
            Term::App(..) | Term::Let(..) => self.erase(head, &Term::Sort(crate::Level::Zero)),
        }
    }
}

/// Erase a well-typed term against its declared type. Returns the runtime term, or an
/// error if the grade discipline is violated (a ghost used at runtime).
pub fn erase(env: &Env, term: &Term, ty: &Term) -> Result<Erased, String> {
    Eraser { env, binders: Vec::new() }.erase(term, ty)
}

/// Erase a top-level definition by name (uses its declared type and value).
pub fn erase_def(env: &Env, name: &str) -> Result<Erased, String> {
    match env.get(name) {
        Some(Decl::Def { ty, value, .. }) => erase(env, value, ty),
        _ => Err(format!("'{name}' is not a definition")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_kernel_core::term::name;

    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    /// The polymorphic identity carries its type argument at grade 0; erasure drops it,
    /// leaving the runtime identity `λx. x`.
    #[test]
    fn erases_type_argument() {
        let env = Env::new();
        // term: λ A. λ x. x      type: Π (A :⁰ Type). Π (x :ω A). A
        let term = Term::lam(Term::typ(0), Term::lam(Term::Var(0), Term::Var(0)));
        let ty = Term::pi_graded(
            Grade::Zero,
            Term::typ(0),
            Term::pi_graded(Grade::Many, Term::Var(0), Term::Var(1)),
        );
        let e = erase(&env, &term, &ty).unwrap();
        assert_eq!(e, Erased::lam(Erased::Var(0)), "runtime identity is λx. x");
    }

    /// A ghost (grade-0) argument at an application site is dropped.
    #[test]
    fn drops_ghost_argument_at_call() {
        let mut k = rv_kernel_core::kernel::Kernel::new();
        k.add_axiom("T", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("T")).unwrap();
        // id :  Π (A :⁰ Type). Π (x :ω A). A   :=  λ A x. x
        let id_ty = Term::pi_graded(
            Grade::Zero,
            Term::typ(0),
            Term::pi_graded(Grade::Many, Term::Var(0), Term::Var(1)),
        );
        k.add_definition("id", 0, id_ty, Term::lam(Term::typ(0), Term::lam(Term::Var(0), Term::Var(0))))
            .unwrap();
        // erase  (id T a)  ⇒  (id a)   — the type argument T is gone.
        let call = Term::apps(cn("id"), [cn("T"), cn("a")]);
        let e = erase(k.env(), &call, &cn("T")).unwrap();
        assert_eq!(e, Erased::app(Erased::Const(name("id")), Erased::Const(name("a"))));
    }

    /// A proof argument (grade 0) is erased even though the function is otherwise real.
    #[test]
    fn drops_proof_argument() {
        let env = Env::new();
        // λ (n :ω Type). λ (h :⁰ Type). n      (stand-in: `h` is a grade-0 "proof")
        let term = Term::lam(Term::typ(0), Term::lam(Term::typ(0), Term::Var(1)));
        let ty = Term::pi_graded(
            Grade::Many,
            Term::typ(0),
            Term::pi_graded(Grade::Zero, Term::typ(0), Term::Var(1)),
        );
        let e = erase(&env, &term, &ty).unwrap();
        // keeps `n`, drops `h`:  λn. n
        assert_eq!(e, Erased::lam(Erased::Var(0)));
    }

    /// The grade discipline is enforced: a ghost binder used at runtime is rejected.
    #[test]
    fn ghost_used_at_runtime_is_rejected() {
        let env = Env::new();
        // λ (x :⁰ Type). x   — claims `x` ghost but returns it.
        let term = Term::lam(Term::typ(0), Term::Var(0));
        let ty = Term::pi_graded(Grade::Zero, Term::typ(0), Term::typ(0));
        let err = erase(&env, &term, &ty).unwrap_err();
        assert!(err.contains("ghost"), "expected a grade-discipline error, got: {err}");
    }

    /// Erasure leaves ordinary (grade-ω) code intact.
    #[test]
    fn keeps_runtime_code() {
        let env = Env::new();
        let term = Term::lam(Term::typ(0), Term::lam(Term::Var(0), Term::Var(0)));
        let ty = Term::pi_graded(
            Grade::Many,
            Term::typ(0),
            Term::pi_graded(Grade::Many, Term::Var(0), Term::Var(1)),
        );
        let e = erase(&env, &term, &ty).unwrap();
        assert_eq!(e, Erased::lam(Erased::lam(Erased::Var(0))));
    }
}
