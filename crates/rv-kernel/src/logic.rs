//! The first sliver of the L1 library: propositional logic and the classical
//! axioms, declared *through* the trusted [`Kernel`] API.
//!
//! Everything here is ordinary kernel content — inductive `Prop`s, two `Def`s, and a
//! couple of axioms — not special kernel machinery. That's the point: the connectives
//! `True`/`False`/`And`/`Or`/`Exists` are inductive types, `Not`/`Iff` are
//! definitions, and `propext`/`Classical.em` are axioms. The tests then build real
//! proof terms (`And` commutativity; double-negation elimination from excluded
//! middle) and have the kernel check them — exercising generated recursors,
//! δ-unfolding, proof irrelevance, and axioms end-to-end.

use crate::generate::{eq_spec, CtorSpec, IndSpec};
use crate::kernel::Kernel;
use crate::level::Level;
use crate::term::{name, Term};

fn c(s: &str) -> Term {
    Term::cnst(name(s), vec![])
}

/// A nullary inductive proposition spec (`True`-like / `False`-like).
fn prop_inductive(nm: &str, rec: &str, ctors: Vec<CtorSpec>) -> IndSpec {
    IndSpec { name: name(nm), num_levels: 0, ty: Term::prop(), num_params: 0, ctors, rec_name: name(rec) }
}

/// A binary connective spec `_ : Prop → Prop → Prop`.
fn binary_connective(nm: &str, rec: &str, ctors: Vec<CtorSpec>) -> IndSpec {
    IndSpec {
        name: name(nm),
        num_levels: 0,
        ty: Term::pi(Term::prop(), Term::pi(Term::prop(), Term::prop())),
        num_params: 2,
        ctors,
        rec_name: name(rec),
    }
}

/// Declare the core connectives and equality: `True`, `False`, `And`, `Or`,
/// `Exists`, `Eq`, plus the definitions `Not` and `Iff`.
pub fn declare_logic(k: &mut Kernel) -> Result<(), String> {
    // True := one constructor.
    k.declare_inductive(prop_inductive(
        "True",
        "True.rec",
        vec![CtorSpec { name: name("True.intro"), ty: c("True") }],
    ))?;
    // False := no constructors.
    k.declare_inductive(prop_inductive("False", "False.rec", vec![]))?;

    // And a b := intro (ha : a) (hb : b).
    k.declare_inductive(binary_connective(
        "And",
        "And.rec",
        vec![CtorSpec {
            name: name("And.intro"),
            // Π (a b : Prop) (_ : a) (_ : b). And a b
            ty: Term::pi(
                Term::prop(),
                Term::pi(
                    Term::prop(),
                    Term::pi(
                        Term::Var(1),
                        Term::pi(Term::Var(1), Term::apps(c("And"), [Term::Var(3), Term::Var(2)])),
                    ),
                ),
            ),
        }],
    ))?;

    // Or a b := inl (ha : a) | inr (hb : b).
    k.declare_inductive(binary_connective(
        "Or",
        "Or.rec",
        vec![
            CtorSpec {
                name: name("Or.inl"),
                ty: Term::pi(
                    Term::prop(),
                    Term::pi(
                        Term::prop(),
                        Term::pi(Term::Var(1), Term::apps(c("Or"), [Term::Var(2), Term::Var(1)])),
                    ),
                ),
            },
            CtorSpec {
                name: name("Or.inr"),
                ty: Term::pi(
                    Term::prop(),
                    Term::pi(
                        Term::prop(),
                        Term::pi(Term::Var(0), Term::apps(c("Or"), [Term::Var(2), Term::Var(1)])),
                    ),
                ),
            },
        ],
    ))?;

    // Exists.{u} (A : Sort u) (P : A → Prop) := intro (a : A) (h : P a).
    let u = Level::param(0);
    k.declare_inductive(IndSpec {
        name: name("Exists"),
        num_levels: 1,
        // Π (A : Sort u) (P : A → Prop). Prop
        ty: Term::pi(
            Term::Sort(u.clone()),
            Term::pi(Term::arrow(Term::Var(0), Term::prop()), Term::prop()),
        ),
        num_params: 2,
        ctors: vec![CtorSpec {
            name: name("Exists.intro"),
            // Π (A : Sort u) (P : A → Prop) (a : A) (_ : P a). Exists A P
            ty: Term::pi(
                Term::Sort(u.clone()),
                Term::pi(
                    Term::arrow(Term::Var(0), Term::prop()),
                    Term::pi(
                        Term::Var(1),                              // a : A
                        Term::pi(
                            Term::app(Term::Var(1), Term::Var(0)), // P a
                            Term::apps(
                                Term::cnst(name("Exists"), vec![u.clone()]),
                                [Term::Var(3), Term::Var(2)],
                            ),
                        ),
                    ),
                ),
            ),
        }],
        rec_name: name("Exists.rec"),
    })?;

    // Eq (from the generator's spec).
    k.declare_inductive(eq_spec())?;

    // Not p := p → False.
    k.add_definition(
        "Not",
        0,
        Term::arrow(Term::prop(), Term::prop()),
        Term::lam(Term::prop(), Term::pi(Term::Var(0), c("False"))),
    )?;

    // Iff p q := And (p → q) (q → p).
    k.add_definition(
        "Iff",
        0,
        Term::pi(Term::prop(), Term::pi(Term::prop(), Term::prop())),
        Term::lam(
            Term::prop(),
            Term::lam(
                Term::prop(),
                Term::apps(
                    c("And"),
                    [
                        Term::arrow(Term::Var(1), Term::Var(0)), // p → q
                        Term::arrow(Term::Var(0), Term::Var(1)), // q → p
                    ],
                ),
            ),
        ),
    )?;

    Ok(())
}

/// Declare the classical axioms: propositional extensionality and excluded middle.
/// Requires [`declare_logic`] first (they mention `Iff`, `Eq`, `Or`, `Not`).
pub fn declare_classical(k: &mut Kernel) -> Result<(), String> {
    // propext : Π (p q : Prop), Iff p q → Eq.{1} Prop p q
    k.add_axiom(
        "propext",
        0,
        Term::pi(
            Term::prop(),
            Term::pi(
                Term::prop(),
                Term::arrow(
                    Term::apps(c("Iff"), [Term::Var(1), Term::Var(0)]),
                    Term::apps(
                        Term::cnst(name("Eq"), vec![Level::of_nat(1)]),
                        [Term::prop(), Term::Var(1), Term::Var(0)],
                    ),
                ),
            ),
        ),
    )?;

    // Classical.em : Π (p : Prop), Or p (Not p)
    k.add_axiom(
        "Classical.em",
        0,
        Term::pi(
            Term::prop(),
            Term::apps(c("Or"), [Term::Var(0), Term::app(c("Not"), Term::Var(0))]),
        ),
    )?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn logic_kernel() -> Kernel {
        let mut k = Kernel::new();
        declare_logic(&mut k).unwrap();
        k
    }

    /// `And` commutativity, proved by its recursor: a real proof term, type-checked.
    #[test]
    fn and_comm_proof_checks() {
        let k = logic_kernel();
        let and = |x: Term, y: Term| Term::apps(c("And"), [x, y]);

        // proof = λ (a b : Prop) (h : And a b).
        //           And.rec.{0} a b (λ _. And b a)
        //             (λ ha hb. And.intro b a hb ha) h
        // context inside the three λs: a=Var2, b=Var1, h=Var0.
        let motive = Term::lam(
            and(Term::Var(2), Term::Var(1)),           // _ : And a b
            and(Term::Var(2), Term::Var(3)),           // And b a   (b=Var2, a=Var3)
        );
        let minor = Term::lam(
            Term::Var(2),                               // ha : a
            Term::lam(
                Term::Var(2),                           // hb : b
                // And.intro b a hb ha  (a=Var4,b=Var3,ha=Var1,hb=Var0)
                Term::apps(
                    c("And.intro"),
                    [Term::Var(3), Term::Var(4), Term::Var(0), Term::Var(1)],
                ),
            ),
        );
        let body = Term::apps(
            Term::cnst(name("And.rec"), vec![Level::Zero]),
            [Term::Var(2), Term::Var(1), motive, minor, Term::Var(0)],
        );
        let proof = Term::lam(
            Term::prop(),
            Term::lam(Term::prop(), Term::lam(and(Term::Var(1), Term::Var(0)), body)),
        );

        // goal = Π (a b : Prop). And a b → And b a
        let goal = Term::pi(
            Term::prop(),
            Term::pi(
                Term::prop(),
                Term::arrow(and(Term::Var(1), Term::Var(0)), and(Term::Var(0), Term::Var(1))),
            ),
        );

        let ty = k.infer(&proof).expect("And.comm should type-check");
        assert!(k.def_eq(&ty, &goal), "got {ty:?}");
        // And the checker accepts it directly against the goal, too.
        k.check(&proof, &goal).unwrap();
    }

    /// Double-negation elimination `¬¬p → p`, proved *classically* from excluded
    /// middle. Exercises `Or.rec` (restricted to `Prop`), `False.rec`, the `Not`
    /// definition (δ-unfolding `nnp hnp : False`), and the `Classical.em` axiom.
    #[test]
    fn double_negation_elimination_from_em() {
        let mut k = logic_kernel();
        declare_classical(&mut k).unwrap();

        let not = |x: Term| Term::app(c("Not"), x);
        let or = |x: Term, y: Term| Term::apps(c("Or"), [x, y]);

        // dne = λ (p : Prop) (nnp : Not (Not p)).
        //   Or.rec p (Not p) (λ _. p)
        //     (λ hp. hp)                                    -- p case
        //     (λ hnp. False.rec.{0} (λ _. p) (nnp hnp))     -- ¬p case
        //     (Classical.em p)
        // context inside [p, nnp]: p=Var1, nnp=Var0.
        let motive = Term::lam(or(Term::Var(1), not(Term::Var(1))), Term::Var(2)); // λ _. p
        let minor_inl = Term::lam(Term::Var(1), Term::Var(0)); // λ hp. hp
        let minor_inr = {
            // λ (hnp : Not p). False.rec.{0} (λ _. p) (nnp hnp)
            // context [p, nnp, hnp]: p=Var2, nnp=Var1, hnp=Var0.
            let false_motive = Term::lam(c("False"), Term::Var(3)); // λ _:False. p
            let falsum = Term::app(Term::Var(1), Term::Var(0)); // nnp hnp : False
            let body =
                Term::apps(Term::cnst(name("False.rec"), vec![Level::Zero]), [false_motive, falsum]);
            Term::lam(not(Term::Var(1)), body)
        };
        let em_p = Term::app(c("Classical.em"), Term::Var(1));
        let or_rec = Term::apps(
            Term::cnst(name("Or.rec"), vec![]), // Or.rec is Prop-restricted: no level args
            [Term::Var(1), not(Term::Var(1)), motive, minor_inl, minor_inr, em_p],
        );
        let dne = Term::lam(Term::prop(), Term::lam(not(not(Term::Var(0))), or_rec));

        // goal = Π (p : Prop). Not (Not p) → p
        let goal = Term::pi(Term::prop(), Term::arrow(not(not(Term::Var(0))), Term::Var(0)));

        k.check(&dne, &goal).expect("DNE should check classically");
    }

    /// Sanity: the restricted `Or.rec` indeed has no universe parameter, while the
    /// subsingleton `And.rec` does.
    #[test]
    fn elimination_universes_as_expected() {
        let k = logic_kernel();
        assert_eq!(k.env().get("Or.rec").unwrap().num_levels(), 0);
        assert_eq!(k.env().get("And.rec").unwrap().num_levels(), 1);
        assert_eq!(k.env().get("False.rec").unwrap().num_levels(), 1); // 0 ctors ⇒ large elim
    }
}
