//! Inductive families.
//!
//! ## Phase 1 — hand-built inductives
//!
//! The low-level API ([`RawInductive`] / [`declare_raw`]) inserts a fully-formed
//! inductive bundle — type former, constructors, and a recursor with its ι-rules —
//! into an [`Env`]. Phase 1 uses it to build `Nat` and `Eq` *by hand*, which
//! validates the recursor representation and the ι-reduction in [`crate::reduce`]
//! before any automation exists. [`declare_nat`] and [`declare_eq`] are those
//! hand-builds; the integration tests drive a real induction proof through them.
//!
//! ## Phase 2 — the general elaborator
//!
//! `rv_kernel::generate::declare_inductive` takes a high-level `IndSpec` (a type former plus
//! constructor types) and *computes* the recursor type and ι-rules itself, after
//! checking well-formedness and **strict positivity**. The Phase-1 hand-builds then
//! become oracles: the generator must reproduce them.

use crate::check::{Checker, LocalCtx};
use crate::env::{Constructor, Decl, Env, Inductive, RecRule, Recursor};
use crate::level::Level;
use crate::term::{name, Name, Term};
use std::collections::HashMap;
use std::rc::Rc;

/// Build `n` nested lambdas around `body`. Binder domains are irrelevant to
/// reduction (β ignores them), so recursor right-hand sides use a placeholder.
fn lams(n: usize, body: Term) -> Term {
    let mut t = body;
    for _ in 0..n {
        t = Term::lam(Term::prop(), t);
    }
    t
}

/// A fully-formed inductive bundle ready to insert verbatim.
pub struct RawInductive {
    pub ind_name: Name,
    pub inductive: Inductive,
    pub ctors: Vec<(Name, Constructor)>,
    pub rec_name: Name,
    pub recursor: Recursor,
}

/// Insert a fully-formed inductive bundle (Phase-1 path). Does **not** recompute or
/// re-check the recursor; the caller is trusted to have built it correctly.
pub fn declare_raw(env: &mut Env, raw: RawInductive) -> Result<(), String> {
    env.insert(raw.ind_name, Decl::Inductive(Rc::new(raw.inductive)))?;
    for (cn, c) in raw.ctors {
        env.insert(cn, Decl::Constructor(Rc::new(c)))?;
    }
    env.insert(raw.rec_name, Decl::Recursor(Rc::new(raw.recursor)))?;
    Ok(())
}

/// Declare `Nat : Type 0` with `zero`, `succ`, and `Nat.rec` (one motive universe
/// parameter). Hand-built.
pub fn declare_nat(env: &mut Env) -> Result<(), String> {
    let nat = || Term::cnst(name("Nat"), vec![]);
    let zero = || Term::cnst(name("Nat.zero"), vec![]);
    let succ = |x: Term| Term::app(Term::cnst(name("Nat.succ"), vec![]), x);

    let inductive = Inductive {
        num_levels: 0,
        ty: Term::typ(0),
        num_params: 0,
        num_indices: 0,
        ctors: vec![name("Nat.zero"), name("Nat.succ")],
        recursor: name("Nat.rec"),
        group: vec![name("Nat")],
    };
    let ctor_zero = Constructor {
        num_levels: 0,
        ty: nat(),
        ind: name("Nat"),
        index: 0,
        num_fields: 0,
    };
    let ctor_succ = Constructor {
        num_levels: 0,
        ty: Term::arrow(nat(), nat()),
        ind: name("Nat"),
        index: 1,
        num_fields: 1,
    };

    // Nat.rec.{u} : Π (motive : Nat → Sort u)
    //                 (z : motive Nat.zero)
    //                 (s : Π (n : Nat), motive n → motive (Nat.succ n))
    //                 (t : Nat), motive t
    let u = Level::param(0);
    let motive_ty = Term::arrow(nat(), Term::Sort(u));
    // Under [motive]: motive Nat.zero
    let z_ty = Term::app(Term::Var(0), zero());
    // Under [motive, z]: Π (n:Nat), motive n → motive (succ n).
    //   After binding n: motive=Var2, n=Var0  ⇒ domain `motive n` = App(Var2, Var0).
    //   After binding the `motive n` hypothesis: motive=Var3, n=Var1
    //                                          ⇒ body `motive (succ n)` = App(Var3, succ Var1).
    let s_ty = Term::pi(
        nat(),
        Term::pi(
            Term::app(Term::Var(2), Term::Var(0)),
            Term::app(Term::Var(3), succ(Term::Var(1))),
        ),
    );
    // Under [motive, z, s, t]: motive t ; motive=Var(3), t=Var(0)
    let result = Term::app(Term::Var(3), Term::Var(0));
    let rec_ty = Term::pi(
        motive_ty,
        Term::pi(z_ty, Term::pi(s_ty, Term::pi(nat(), result))),
    );

    // ι-rules. rhs is applied to [params…, motive, minors…, fields…].
    // zero: applied to [motive, z, s] ↦ z  (z = Var(1) under λmotive λz λs)
    let rule_zero = RecRule {
        ctor: name("Nat.zero"),
        num_fields: 0,
        rhs: lams(3, Term::Var(1)),
    };
    // succ: applied to [motive, z, s, n] ↦ s n (Nat.rec.{u} motive z s n)
    //   under λmotive λz λs λn : motive=Var3, z=Var2, s=Var1, n=Var0
    let rec_call = Term::apps(
        Term::cnst(name("Nat.rec"), vec![Level::param(0)]),
        [Term::Var(3), Term::Var(2), Term::Var(1), Term::Var(0)],
    );
    let succ_body = Term::apps(Term::Var(1), [Term::Var(0), rec_call]);
    let rule_succ = RecRule {
        ctor: name("Nat.succ"),
        num_fields: 1,
        rhs: lams(4, succ_body),
    };

    let mut rules = HashMap::new();
    rules.insert(name("Nat.zero"), rule_zero);
    rules.insert(name("Nat.succ"), rule_succ);

    let recursor = Recursor {
        num_levels: 1,
        ty: rec_ty,
        ind: name("Nat"),
        num_params: 0,
        num_motives: 1,
        num_indices: 0,
        num_minors: 2,
        rules,
    };

    declare_raw(
        env,
        RawInductive {
            ind_name: name("Nat"),
            inductive,
            ctors: vec![(name("Nat.zero"), ctor_zero), (name("Nat.succ"), ctor_succ)],
            rec_name: name("Nat.rec"),
            recursor,
        },
    )
}

/// Declare `Eq.{u} : Π (A : Sort u) (a : A), A → Prop` with `Eq.refl` and `Eq.rec`.
/// Parameters are `A` and `a`; the right-hand side is an index. Hand-built.
pub fn declare_eq(env: &mut Env) -> Result<(), String> {
    let u = || Level::param(0);
    let a_sort = || Term::Sort(u());
    let eq = |args: [Term; 3]| Term::apps(Term::cnst(name("Eq"), vec![u()]), args);
    let refl = |a: Term, x: Term| Term::apps(Term::cnst(name("Eq.refl"), vec![u()]), [a, x]);

    // Eq : Π (A : Sort u) (a : A) (b : A), Prop
    let ind_ty = Term::pi(
        a_sort(),
        Term::pi(Term::Var(0), Term::pi(Term::Var(1), Term::prop())),
    );
    let inductive = Inductive {
        num_levels: 1,
        ty: ind_ty,
        num_params: 2,
        num_indices: 1,
        ctors: vec![name("Eq.refl")],
        recursor: name("Eq.rec"),
        group: vec![name("Eq")],
    };
    // Eq.refl : Π (A : Sort u) (a : A), Eq A a a
    let refl_ty = Term::pi(
        a_sort(),
        Term::pi(Term::Var(0), eq([Term::Var(1), Term::Var(0), Term::Var(0)])),
    );
    let ctor_refl = Constructor {
        num_levels: 1,
        ty: refl_ty,
        ind: name("Eq"),
        index: 0,
        num_fields: 0,
    };

    // Eq.rec.{u v} : Π (A : Sort u) (a : A)
    //                  (motive : Π (b : A), Eq A a b → Sort v)
    //                  (refl_case : motive a (Eq.refl A a))
    //                  (b : A) (h : Eq A a b), motive b h
    let v = Level::param(1);
    // Under [A, a]: motive : Π (b:A), Eq A a b → Sort v   (A=Var1, a=Var0)
    let motive_ty = {
        // bind b (Var0): A=Var2, a=Var1
        let eq_a_b = eq([Term::Var(2), Term::Var(1), Term::Var(0)]);
        Term::pi(Term::Var(1), Term::arrow(eq_a_b, Term::Sort(v.clone())))
    };
    // Under [A, a, motive]: refl_case : motive a (Eq.refl A a)
    //   A=Var2, a=Var1, motive=Var0
    let refl_case_ty = Term::apps(Term::Var(0), [Term::Var(1), refl(Term::Var(2), Term::Var(1))]);
    // Under [A, a, motive, refl_case]: Π (b:A) (h: Eq A a b), motive b h
    //   A=Var3, a=Var2, motive=Var1
    let tail = {
        // bind b (Var0): A=Var4, a=Var3, motive=Var2
        let eq_a_b = eq([Term::Var(4), Term::Var(3), Term::Var(0)]);
        // bind h: motive=Var3, b=Var1, h=Var0
        let result = Term::apps(Term::Var(3), [Term::Var(1), Term::Var(0)]);
        Term::pi(Term::Var(3), Term::pi(eq_a_b, result))
    };
    let rec_ty = Term::pi(
        a_sort(),
        Term::pi(Term::Var(0), Term::pi(motive_ty, Term::pi(refl_case_ty, tail))),
    );

    // ι-rule for refl: rhs applied to [A, a, motive, refl_case] ↦ refl_case
    //   under λA λa λmotive λrefl_case : refl_case = Var(0)
    let rule_refl = RecRule {
        ctor: name("Eq.refl"),
        num_fields: 0,
        rhs: lams(4, Term::Var(0)),
    };
    let mut rules = HashMap::new();
    rules.insert(name("Eq.refl"), rule_refl);

    let recursor = Recursor {
        num_levels: 2,
        ty: rec_ty,
        ind: name("Eq"),
        num_params: 2,
        num_motives: 1,
        num_indices: 1,
        num_minors: 1,
        rules,
    };

    declare_raw(
        env,
        RawInductive {
            ind_name: name("Eq"),
            inductive,
            ctors: vec![(name("Eq.refl"), ctor_refl)],
            rec_name: name("Eq.rec"),
            recursor,
        },
    )
}

/// Type-check every declaration's stated type in `env` (a sanity pass: each
/// declaration's type must itself be a well-formed type under the env's universe
/// arity). Returns the first failure.
pub fn check_env_types(env: &Env, decls: &[(&str, u32)]) -> Result<(), String> {
    let chk = Checker::new(env);
    for (n, num_levels) in decls {
        let decl = env.get(n).ok_or_else(|| format!("missing '{n}'"))?;
        // Type-check the declared type in the empty local context; universe params
        // are treated as opaque `Param`s, which `infer_sort` handles.
        let _ = num_levels;
        let mut ctx = LocalCtx::new();
        chk.infer(&mut ctx, decl.ty()).map_err(|e| format!("'{n}': {e}"))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reduce::Reducer;

    fn nat_env() -> Env {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        env
    }

    fn lit(n: u32) -> Term {
        let mut t = Term::cnst(name("Nat.zero"), vec![]);
        for _ in 0..n {
            t = Term::app(Term::cnst(name("Nat.succ"), vec![]), t);
        }
        t
    }

    /// The hand-built recursor types check.
    #[test]
    fn nat_and_eq_types_wellformed() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_eq(&mut env).unwrap();
        check_env_types(
            &env,
            &[("Nat", 0), ("Nat.zero", 0), ("Nat.succ", 0), ("Nat.rec", 1),
              ("Eq", 1), ("Eq.refl", 1), ("Eq.rec", 2)],
        )
        .unwrap();
    }

    /// ι-reduction computes: `Nat.rec` defines addition and `2 + 3` reduces to `5`.
    #[test]
    fn addition_computes_by_iota() {
        let env = nat_env();
        let r = Reducer::new(&env);
        // add = λ m n. Nat.rec.{1} (λ_. Nat) n (λ p ih. succ ih) m
        let nat = Term::cnst(name("Nat"), vec![]);
        let succ = |x: Term| Term::app(Term::cnst(name("Nat.succ"), vec![]), x);
        let add = |m: Term, n: Term| {
            Term::apps(
                Term::cnst(name("Nat.rec"), vec![Level::of_nat(1)]),
                [
                    Term::lam(nat.clone(), nat.clone()), // motive λ_. Nat
                    n,                                   // zero-case = n
                    Term::lam(nat.clone(), Term::lam(nat.clone(), succ(Term::Var(0)))), // succ-case
                    m,                                   // scrutinee
                ],
            )
        };
        let two_plus_three = add(lit(2), lit(3));
        assert!(r.is_def_eq(&two_plus_three, &lit(5)), "2+3 should reduce to 5");
        // add 0 n ≡ n definitionally (recursion on first arg).
        assert!(r.is_def_eq(&add(lit(0), lit(4)), &lit(4)));
    }

    /// The Phase-1 milestone: prove `∀ n, add n 0 = n` by induction. Needs `Eq`,
    /// `Eq.refl`, congruence (`ap`), and `Nat.rec` as the induction principle — the
    /// whole machinery end-to-end. We build the proof term and type-check it.
    #[test]
    fn add_n_zero_eq_n_by_induction() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_eq(&mut env).unwrap();
        let chk = Checker::new(&env);
        let (proof, goal) = add_n_zero_proof();
        let ty = chk.infer_closed(&proof).expect("induction proof should type-check");
        let r = Reducer::new(&env);
        assert!(r.is_def_eq(&ty, &goal), "proof has type {ty:?}");
    }
}

/// Build `(proof, goal)` for `∀ n, add n 0 = n`, proved by induction over `Nat` with
/// congruence (`ap` via `Eq.rec`). Constructed purely from the standard declaration
/// *names* (`Nat`, `Nat.rec`, `Eq`, `Eq.rec`, …), so it type-checks against **any**
/// environment that provides them — whether hand-built here or generated by
/// `rv_kernel::generate` (Phase 2). `pub` (not test-gated) because it is a test
/// fixture shared across the `rv-kernel-core`/`rv-kernel` crate split, not just
/// within this crate.
pub fn add_n_zero_proof() -> (Term, Term) {
    let nat = || Term::cnst(name("Nat"), vec![]);
    let zero = || Term::cnst(name("Nat.zero"), vec![]);
    let succ = |x: Term| Term::app(Term::cnst(name("Nat.succ"), vec![]), x);
    let eqn =
        |x: Term, y: Term| Term::apps(Term::cnst(name("Eq"), vec![Level::of_nat(1)]), [nat(), x, y]);
    let refl =
        |x: Term| Term::apps(Term::cnst(name("Eq.refl"), vec![Level::of_nat(1)]), [nat(), x]);
    // add m n = Nat.rec.{1} (λ_.Nat) n (λp ih. succ ih) m
    let add = |m: Term, n: Term| {
        Term::apps(
            Term::cnst(name("Nat.rec"), vec![Level::of_nat(1)]),
            [
                Term::lam(nat(), nat()),
                n,
                Term::lam(nat(), Term::lam(nat(), succ(Term::Var(0)))),
                m,
            ],
        )
    };

    let motive = Term::lam(nat(), eqn(add(Term::Var(0), zero()), Term::Var(0)));
    let base = refl(zero());
    let step = {
        let ih_dom = eqn(add(Term::Var(0), zero()), Term::Var(0));
        let n = Term::Var(1);
        let ih = Term::Var(0);
        let x = add(n.clone(), zero());
        let eqrec_motive = Term::lam(
            nat(),
            Term::lam(
                eqn(x.lift(1, 0), Term::Var(0)),
                eqn(succ(x.lift(2, 0)), succ(Term::Var(1))),
            ),
        );
        let ap = Term::apps(
            Term::cnst(name("Eq.rec"), vec![Level::of_nat(1), Level::Zero]),
            [nat(), x.clone(), eqrec_motive, refl(succ(x.clone())), n.clone(), ih.clone()],
        );
        Term::lam(nat(), Term::lam(ih_dom, ap))
    };
    let proof = Term::lam(
        nat(),
        Term::apps(
            Term::cnst(name("Nat.rec"), vec![Level::Zero]),
            [motive, base, step, Term::Var(0)],
        ),
    );
    let goal = Term::pi(nat(), eqn(add(Term::Var(0), zero()), Term::Var(0)));
    (proof, goal)
}
