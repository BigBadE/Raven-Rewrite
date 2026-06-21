//! The trusted front door to the kernel.
//!
//! [`Kernel`] wraps an [`Env`] and is the *only* sanctioned way to grow it: every
//! addition is type-checked first, so a well-typed `Kernel` only ever contains
//! well-formed declarations. (The lower-level [`Env::insert`] and the Phase-1
//! `declare_raw` bypass these checks and are for bootstrapping/oracles.)
//!
//! Four ways to extend the environment:
//! * [`Kernel::add_axiom`] — a name and a type (which must be a well-formed type),
//!   trusted as stated.
//! * [`Kernel::add_definition`] — a name, type, and value, where the value is checked
//!   against the type. Unfolds by δ.
//! * [`Kernel::declare_inductive`] — an inductive family (positivity + recursor
//!   synthesis live in [`crate::generate`]).
//! * [`Kernel::check`] / [`Kernel::infer`] — type-check a term against the current
//!   environment (e.g. a candidate proof).

use crate::check::{Checker, LocalCtx};
use crate::env::{Decl, Env};
use crate::generate::{declare_inductive, IndSpec};
use crate::term::{name, Term};

/// Reject any term still carrying an elaboration hole (a term or level metavariable)
/// before it reaches the trusted checker — defence in depth, independent of the
/// elaborator zonking correctly.
fn reject_meta(t: &Term) -> Result<(), String> {
    if t.has_meta() {
        Err("term still contains an unsolved metavariable (elaboration incomplete)".to_string())
    } else {
        Ok(())
    }
}

/// A type-checked environment builder.
#[derive(Default)]
pub struct Kernel {
    env: Env,
}

impl Kernel {
    pub fn new() -> Self {
        Self { env: Env::new() }
    }

    /// Borrow the underlying environment (e.g. to build a [`Checker`] or reducer).
    pub fn env(&self) -> &Env {
        &self.env
    }

    /// A checker bound to the current environment.
    pub fn checker(&self) -> Checker<'_> {
        Checker::new(&self.env)
    }

    /// Add an axiom `name.{levels} : ty`. `ty` must be a well-formed type (its own
    /// type is a sort). The axiom is then trusted as stated.
    pub fn add_axiom(&mut self, n: &str, num_levels: u32, ty: Term) -> Result<(), String> {
        reject_meta(&ty).map_err(|e| format!("axiom '{n}': {e}"))?;
        {
            let chk = Checker::new(&self.env);
            chk.infer_sort(&mut LocalCtx::new(), &ty)
                .map_err(|e| format!("axiom '{n}': type is not well-formed: {e}"))?;
        }
        self.env.insert(name(n), Decl::Axiom { num_levels, ty })
    }

    /// Add a definition `name.{levels} : ty := value`, checking `value : ty`.
    pub fn add_definition(
        &mut self,
        n: &str,
        num_levels: u32,
        ty: Term,
        value: Term,
    ) -> Result<(), String> {
        reject_meta(&ty).map_err(|e| format!("definition '{n}': {e}"))?;
        reject_meta(&value).map_err(|e| format!("definition '{n}': {e}"))?;
        {
            let chk = Checker::new(&self.env);
            chk.infer_sort(&mut LocalCtx::new(), &ty)
                .map_err(|e| format!("definition '{n}': type is not well-formed: {e}"))?;
            chk.check(&mut LocalCtx::new(), &value, &ty)
                .map_err(|e| format!("definition '{n}': value does not match type: {e}"))?;
        }
        self.env.insert(name(n), Decl::Def { num_levels, ty, value })
    }

    /// Declare an inductive family.
    pub fn declare_inductive(&mut self, spec: IndSpec) -> Result<(), String> {
        declare_inductive(&mut self.env, spec)
    }

    /// Declare a **mutual** group of inductive families simultaneously.
    pub fn declare_mutual(&mut self, specs: Vec<IndSpec>) -> Result<(), String> {
        crate::mutual::declare_mutual(&mut self.env, specs)
    }

    /// Infer the type of a closed term against the current environment.
    pub fn infer(&self, t: &Term) -> Result<Term, String> {
        reject_meta(t)?;
        self.checker().infer_closed(t)
    }

    /// Check that closed term `t` has type `expected` (e.g. a proof against its goal).
    pub fn check(&self, t: &Term, expected: &Term) -> Result<(), String> {
        reject_meta(t)?;
        reject_meta(expected)?;
        self.checker().check(&mut LocalCtx::new(), t, expected)
    }

    /// Definitional equality of two closed terms in the current environment.
    pub fn def_eq(&self, a: &Term, b: &Term) -> bool {
        self.checker().def_eq(a, b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::level::Level;

    #[test]
    fn axiom_and_definition_roundtrip() {
        let mut k = Kernel::new();
        // axiom A : Type 0
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        // axiom a : A
        k.add_axiom("a", 0, Term::cnst(name("A"), vec![])).unwrap();
        // def id_A : A → A := λ x. x
        k.add_definition(
            "id_A",
            0,
            Term::arrow(Term::cnst(name("A"), vec![]), Term::cnst(name("A"), vec![])),
            Term::lam(Term::cnst(name("A"), vec![]), Term::Var(0)),
        )
        .unwrap();
        // id_A a : A, and it computes to a.
        let app = Term::app(Term::cnst(name("id_A"), vec![]), Term::cnst(name("a"), vec![]));
        k.check(&app, &Term::cnst(name("A"), vec![])).unwrap();
        assert!(k.def_eq(&app, &Term::cnst(name("a"), vec![])));
    }

    #[test]
    fn ill_typed_definition_rejected() {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        // def bad : A := Type 0   — Type 0 is not of type A.
        let err = k
            .add_definition("bad", 0, Term::cnst(name("A"), vec![]), Term::typ(0))
            .unwrap_err();
        assert!(err.contains("does not match"), "got: {err}");
    }

    #[test]
    fn polymorphic_definition_checks() {
        let mut k = Kernel::new();
        // def id.{u} : Π (A : Sort u). A → A := λ A x. x
        let u = Level::param(0);
        k.add_definition(
            "id",
            1,
            Term::pi(Term::Sort(u.clone()), Term::pi(Term::Var(0), Term::Var(1))),
            Term::lam(Term::Sort(u), Term::lam(Term::Var(0), Term::Var(0))),
        )
        .unwrap();
        assert!(k.env().contains("id"));
    }
}
