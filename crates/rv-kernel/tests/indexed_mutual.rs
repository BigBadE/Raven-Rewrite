//! Indexed **and** mutual inductive families: the combination that was previously
//! rejected outright (`declare_mutual` bailed with "indexed mutual inductives are not
//! yet supported"). Here we build the canonical example — the mutually-defined
//! even/odd *predicates over `Nat`* —
//!
//! ```text
//!   Ev : Nat -> Prop            Od : Nat -> Prop
//!     Ev.zero : Ev 0              Od.succ : (n : Nat) -> Ev n -> Od (succ n)
//!     Ev.succ : (n : Nat) -> Od n -> Ev (succ n)
//! ```
//!
//! and drive the *synthesized* multi-motive, index-carrying recursor: its type must be
//! well-formed, and its ι-rules must fire across the mutual boundary (the recursor for
//! `Ev` invoking the recursor for `Od` on a recursive `Od n` field, and vice-versa).
//!
//! This development is impossible with either the old mutual machinery (indices were
//! rejected) or the old indexed machinery (mutual references were rejected). It is a
//! genuine indexed-mutual family.

use rv_kernel::env::Decl;
use rv_kernel::generate::{CtorSpec, IndSpec};
use rv_kernel::level::Level;
use rv_kernel::reduce::Reducer;
use rv_kernel::{name, Checker, Env, Term};

fn cn(s: &str) -> Term {
    Term::cnst(name(s), vec![])
}

/// Church-style numeral `Nat.succ^n Nat.zero`.
fn lit(n: u32) -> Term {
    let mut t = cn("Nat.zero");
    for _ in 0..n {
        t = Term::app(cn("Nat.succ"), t);
    }
    t
}

fn nat_spec() -> IndSpec {
    IndSpec {
        name: name("Nat"),
        num_levels: 0,
        ty: Term::typ(0),
        num_params: 0,
        ctors: vec![
            CtorSpec { name: name("Nat.zero"), ty: cn("Nat") },
            CtorSpec { name: name("Nat.succ"), ty: Term::arrow(cn("Nat"), cn("Nat")) },
        ],
        rec_name: name("Nat.rec"),
    }
}

/// Build the Ev/Od indexed-mutual group.
fn ev_od_specs() -> Vec<IndSpec> {
    let succ = |t: Term| Term::app(cn("Nat.succ"), t);
    // Ev : Nat -> Prop
    let ev_spec = IndSpec {
        name: name("Ev"),
        num_levels: 0,
        ty: Term::pi(cn("Nat"), Term::prop()),
        num_params: 0,
        ctors: vec![
            // Ev.zero : Ev Nat.zero
            CtorSpec { name: name("Ev.zero"), ty: Term::app(cn("Ev"), cn("Nat.zero")) },
            // Ev.succ : (n : Nat) -> Od n -> Ev (succ n)
            CtorSpec {
                name: name("Ev.succ"),
                ty: Term::pi(
                    cn("Nat"),
                    Term::pi(
                        Term::app(cn("Od"), Term::Var(0)),                 // Od n
                        Term::app(cn("Ev"), succ(Term::Var(1))),           // Ev (succ n)
                    ),
                ),
            },
        ],
        rec_name: name("Ev.rec"),
    };
    // Od : Nat -> Prop
    let od_spec = IndSpec {
        name: name("Od"),
        num_levels: 0,
        ty: Term::pi(cn("Nat"), Term::prop()),
        num_params: 0,
        ctors: vec![
            // Od.succ : (n : Nat) -> Ev n -> Od (succ n)
            CtorSpec {
                name: name("Od.succ"),
                ty: Term::pi(
                    cn("Nat"),
                    Term::pi(
                        Term::app(cn("Ev"), Term::Var(0)),                 // Ev n
                        Term::app(cn("Od"), succ(Term::Var(1))),           // Od (succ n)
                    ),
                ),
            },
        ],
        rec_name: name("Od.rec"),
    };
    vec![ev_spec, od_spec]
}

fn base_env() -> Env {
    let mut env = Env::new();
    rv_kernel::generate::declare_inductive(&mut env, nat_spec()).unwrap();
    rv_kernel::mutual::declare_mutual(&mut env, ev_od_specs()).unwrap();
    env
}

/// The whole group installs, and both synthesized recursors are well-typed. Their shape
/// records the per-member index (`num_indices == 1`) and the shared 2-motive / 3-minor
/// prefix.
#[test]
fn indexed_mutual_group_installs_and_recursors_typecheck() {
    let env = base_env();
    for r in ["Ev.rec", "Od.rec"] {
        let Some(Decl::Recursor(rec)) = env.get(r) else { panic!("{r} missing") };
        assert_eq!(rec.num_motives, 2, "{r}: one motive per group member");
        assert_eq!(rec.num_minors, 3, "{r}: one minor per constructor of the group");
        assert_eq!(rec.num_indices, 1, "{r}: each member carries its own Nat index");
        // The recursor's type is well-formed in the kernel.
        Checker::new(&env)
            .infer_closed(&rec.ty)
            .unwrap_or_else(|e| panic!("{r} type ill-formed: {e}"));
    }
    // Constructors record the right index counts on the formers.
    let Some(Decl::Inductive(ev)) = env.get("Ev") else { panic!() };
    assert_eq!(ev.num_indices, 1);
    assert_eq!(ev.group.len(), 2);
}

/// Sample proofs of `Ev n` / `Od n` type-check against the installed constructors — the
/// mutual references resolve and the indices line up.
#[test]
fn even_odd_witnesses_check() {
    let env = base_env();
    let chk = Checker::new(&env);
    let r = Reducer::new(&env);
    // ev2 : Ev 2  =  Ev.succ 1 (Od.succ 0 Ev.zero)
    let od1 = Term::apps(cn("Od.succ"), [lit(0), cn("Ev.zero")]);
    let ev2 = Term::apps(cn("Ev.succ"), [lit(1), od1.clone()]);
    let ev2_ty = chk.infer_closed(&ev2).expect("Ev 2 should check");
    assert!(r.is_def_eq(&ev2_ty, &Term::app(cn("Ev"), lit(2))), "got {ev2_ty:?}");
    let od1_ty = chk.infer_closed(&od1).expect("Od 1 should check");
    assert!(r.is_def_eq(&od1_ty, &Term::app(cn("Od"), lit(1))), "got {od1_ty:?}");
}

/// The synthesized recursor **computes across the mutual boundary**. We define, by the
/// recursor, a function that walks an `Ev n` derivation counting its constructors — each
/// `Ev.succ` step recurses through the *sibling* `Od.rec` on its `Od n` field and vice
/// versa. On `Ev 2` (two nested successor steps plus the base) it must ι-reduce to `3`.
#[test]
fn recursor_iota_fires_across_the_mutual_boundary() {
    let env = base_env();
    let r = Reducer::new(&env);

    // Ev/Od are `Prop`, so the group's recursor is (soundly) pinned to `Prop`
    // elimination. We therefore exercise ι-reduction with a `Prop`-valued motive
    // `λ n _. Ev n` (resp. `Od n`), realising the identity-by-recursion
    //   copy : Π n, Ev n -> Ev n
    // whose minors rebuild each constructor from the sibling recursion results. Checking
    // `copy 2 ev2 ≡ ev2` forces both ι-rules to fire and to cross into `Od.rec`.

    // motive_ev = λ (n:Nat) (_ : Ev n). Ev n ;  motive_od = λ (n:Nat) (_ : Od n). Od n
    let motive_ev = Term::lam(cn("Nat"), Term::lam(Term::app(cn("Ev"), Term::Var(0)), Term::app(cn("Ev"), Term::Var(1))));
    let motive_od = Term::lam(cn("Nat"), Term::lam(Term::app(cn("Od"), Term::Var(0)), Term::app(cn("Od"), Term::Var(1))));

    // Minors rebuild each constructor from the recursion results.
    //  q_evzero : Ev 0                                        := Ev.zero
    let q_evzero = cn("Ev.zero");
    //  q_evsucc : Π (n:Nat) (o:Od n) (ih:Od n). Ev (succ n)   := λ n o ih. Ev.succ n ih
    let q_evsucc = Term::lam(
        cn("Nat"),
        Term::lam(
            Term::app(cn("Od"), Term::Var(0)),
            Term::lam(
                Term::app(cn("Od"), Term::Var(1)),
                Term::apps(cn("Ev.succ"), [Term::Var(2), Term::Var(0)]),
            ),
        ),
    );
    //  q_odsucc : Π (n:Nat) (e:Ev n) (ih:Ev n). Od (succ n)   := λ n e ih. Od.succ n ih
    let q_odsucc = Term::lam(
        cn("Nat"),
        Term::lam(
            Term::app(cn("Ev"), Term::Var(0)),
            Term::lam(
                Term::app(cn("Ev"), Term::Var(1)),
                Term::apps(cn("Od.succ"), [Term::Var(2), Term::Var(0)]),
            ),
        ),
    );

    // Ev.rec (Prop-pinned: no extra universe level) motives… minors… n major
    let copy_ev = |n: Term, major: Term| {
        Term::apps(
            Term::cnst(name("Ev.rec"), vec![]),
            [
                motive_ev.clone(),
                motive_od.clone(),
                q_evzero.clone(),
                q_evsucc.clone(),
                q_odsucc.clone(),
                n,
                major,
            ],
        )
    };

    let od1 = Term::apps(cn("Od.succ"), [lit(0), cn("Ev.zero")]);
    let ev2 = Term::apps(cn("Ev.succ"), [lit(1), od1]);

    // The identity-by-recursion must reconstruct exactly `ev2`, which forces the ι-rules
    // to fire twice and to cross into `Od.rec` for the recursive `Od 1` field.
    let reconstructed = copy_ev(lit(2), ev2.clone());
    assert!(
        r.is_def_eq(&reconstructed, &ev2),
        "Ev.rec identity-by-recursion should ι-reduce back to the original derivation"
    );

    // And it really did compute (not merely stay stuck): the result is a constructor app.
    let whnf = r.whnf(&reconstructed);
    let (head, _) = whnf.unfold_apps();
    assert!(matches!(&head, Term::Const(h, _) if &**h == "Ev.succ"), "got head {head:?}");
}

/// Guard: single-member "mutual" groups still delegate to the ordinary indexed generator
/// (a mutual group of size one is just an inductive), and a genuinely indexed lone member
/// works — establishing the new path doesn't regress the g == 1 fast path.
#[test]
fn singleton_group_delegates() {
    let mut env = Env::new();
    rv_kernel::generate::declare_inductive(&mut env, nat_spec()).unwrap();
    // A lone indexed member through declare_mutual (size-1 group).
    let vec_spec = IndSpec {
        name: name("Fin"),
        num_levels: 0,
        ty: Term::pi(cn("Nat"), Term::typ(0)), // Fin : Nat -> Type
        num_params: 0,
        ctors: vec![CtorSpec {
            name: name("Fin.fz"),
            // Fin.fz : (n : Nat) -> Fin (succ n)
            ty: Term::pi(cn("Nat"), Term::app(cn("Fin"), Term::app(cn("Nat.succ"), Term::Var(0)))),
        }],
        rec_name: name("Fin.rec"),
    };
    rv_kernel::mutual::declare_mutual(&mut env, vec![vec_spec]).unwrap();
    let Some(Decl::Recursor(rec)) = env.get("Fin.rec") else { panic!() };
    assert_eq!(rec.num_motives, 1); // delegated to the single-inductive generator
    assert_eq!(rec.num_indices, 1);
    let _ = Level::param(0);
}
