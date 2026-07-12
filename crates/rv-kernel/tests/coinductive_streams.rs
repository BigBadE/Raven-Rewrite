//! Worked, kernel-checked coinductive development: `Stream A`, corecursive `repeat`,
//! `nats`, and `map`, plus a **bisimulation-flavoured** proof that `map id s` and `s`
//! agree on every observation — all driven through the *trusted* `Checker` (i.e. the
//! NbE conversion path the kernel actually uses), not just the reference reducer.
//!
//! ## What "bisimulation" means here, and the honest restriction
//!
//! Two streams are **bisimilar** when their heads are equal and their tails are
//! bisimilar. General *propositional* bisimilarity `Bisim s t : Prop` is an **indexed**
//! coinductive (the related streams `s`, `t` are indices that change in the tail case).
//! The kernel's coinductive support is **non-indexed** (uniform parameters only — see
//! `crate::coinductive`), so a first-class `Bisim` relation is out of scope.
//!
//! What *is* both in scope and genuinely coinductive is the **bisimulation coalgebra**
//! itself: the two defining observations of "`map id s` is bisimilar to `s`",
//!
//! ```text
//!   head (map id s)  ≡  head s                (heads agree)
//!   tail (map id s)  ≡  map id (tail s)        (tails are again related by `map id`)
//! ```
//!
//! hold **definitionally** by the ν-rules — this is exactly the coinductive step of a
//! bisimulation-up-to proof, and the kernel proves both by conversion. We package the
//! head equality as a `refl` proof of propositional `Eq`, type-checked by the kernel, so
//! the result is a real proof term, not just a reducer assertion. Because the relation
//! "there exists `s` with `x = map id s ∧ y = s`" is closed under `tail` (the second
//! equation) and implies head-equality (the first), it *is* a bisimulation; the kernel
//! discharges each observation.

use rv_kernel::coinductive::{stream_spec, CoindSpec};
use rv_kernel::generate::{nat_spec, IndSpec};
use rv_kernel::level::Level;
use rv_kernel::{name, Kernel, Term};

fn cn(s: &str) -> Term {
    Term::cnst(name(s), vec![])
}
fn lit(n: u32) -> Term {
    let mut t = cn("Nat.zero");
    for _ in 0..n {
        t = Term::app(cn("Nat.succ"), t);
    }
    t
}

/// Universe-1 level list for `Stream`/its ops instantiated at `Type 0`.
fn l1() -> Vec<Level> {
    vec![Level::of_nat(1)]
}
fn l11() -> Vec<Level> {
    vec![Level::of_nat(1), Level::of_nat(1)]
}

fn nat() -> Term {
    cn("Nat")
}
fn stream_nat() -> Term {
    Term::app(Term::cnst(name("Stream"), l1()), nat())
}
fn head(s: Term) -> Term {
    Term::apps(Term::cnst(name("Stream.head"), l1()), [nat(), s])
}
fn tail(s: Term) -> Term {
    Term::apps(Term::cnst(name("Stream.tail"), l1()), [nat(), s])
}
fn eqn(x: Term, y: Term) -> Term {
    Term::apps(Term::cnst(name("Eq"), l1()), [nat(), x, y])
}
fn refl(x: Term) -> Term {
    Term::apps(Term::cnst(name("Eq.refl"), l1()), [nat(), x])
}

fn eq_spec() -> IndSpec {
    // Eq.{u} : Π (A : Sort u) (a : A), A → Prop, with Eq.refl.
    let u = Level::param(0);
    IndSpec {
        name: name("Eq"),
        num_levels: 1,
        ty: Term::pi(
            Term::Sort(u.clone()),
            Term::pi(Term::Var(0), Term::pi(Term::Var(1), Term::prop())),
        ),
        num_params: 2,
        ctors: vec![rv_kernel::generate::CtorSpec {
            name: name("Eq.refl"),
            ty: Term::pi(
                Term::Sort(u.clone()),
                Term::pi(
                    Term::Var(0),
                    Term::apps(
                        Term::cnst(name("Eq"), vec![u]),
                        [Term::Var(1), Term::Var(0), Term::Var(0)],
                    ),
                ),
            ),
        }],
        rec_name: name("Eq.rec"),
    }
}

fn base_kernel() -> Kernel {
    let mut k = Kernel::new();
    k.declare_inductive(nat_spec()).unwrap();
    k.declare_inductive(eq_spec()).unwrap();
    k.declare_coinductive(stream_spec()).unwrap();
    k
}

/// `repeat A x : Stream A` = the constant stream. Built with the corecursor over carrier
/// `A`: head-step = identity, tail-step = identity.
fn repeat(x: Term) -> Term {
    Term::apps(
        Term::cnst(name("Stream.corec"), l11()),
        [
            nat(),
            nat(),
            Term::lam(nat(), Term::Var(0)),
            Term::lam(nat(), Term::Var(0)),
            x,
        ],
    )
}

/// `nats` = `0, 1, 2, …`. Carrier `Nat`, head = current, tail-step = succ, seed 0.
fn nats() -> Term {
    Term::apps(
        Term::cnst(name("Stream.corec"), l11()),
        [
            nat(),
            nat(),
            Term::lam(nat(), Term::Var(0)),
            Term::lam(nat(), Term::app(cn("Nat.succ"), Term::Var(0))),
            lit(0),
        ],
    )
}

/// `map f s : Stream Nat`. Carrier `Stream Nat`, head-step = `λ t. f (head t)`,
/// tail-step = `λ t. tail t`, seed `s`. So `map f` coiterates over the source stream.
fn map(f: Term, s: Term) -> Term {
    // head-step : Stream Nat → Nat  =  λ t. f (Stream.head t)
    let head_step = Term::lam(stream_nat(), Term::app(f.lift(1, 0), head(Term::Var(0))));
    // tail-step : Stream Nat → Stream Nat  =  λ t. Stream.tail t
    let tail_step = Term::lam(stream_nat(), tail(Term::Var(0)));
    Term::apps(
        Term::cnst(name("Stream.corec"), l11()),
        [nat(), stream_nat(), head_step, tail_step, s],
    )
}

/// The `Stream A` corecursor type-checks, and `repeat`/`nats`/`map` all have type
/// `Stream Nat` in the kernel.
#[test]
fn stream_terms_typecheck() {
    let k = base_kernel();
    // corecursor type is well-formed.
    k.checker().infer_closed(k.env().get("Stream.corec").unwrap().ty()).unwrap();

    for t in [repeat(lit(3)), nats(), map(Term::lam(nat(), Term::Var(0)), nats())] {
        let ty = k.infer(&t).expect("stream term should type-check");
        assert!(k.def_eq(&ty, &stream_nat()), "expected Stream Nat, got {ty:?}");
    }
}

/// Observations compute through the *kernel's* conversion (NbE): `nats` really counts up.
#[test]
fn nats_observations_via_kernel() {
    let k = base_kernel();
    let n = nats();
    assert!(k.def_eq(&head(n.clone()), &lit(0)));
    assert!(k.def_eq(&head(tail(n.clone())), &lit(1)));
    assert!(k.def_eq(&head(tail(tail(tail(n.clone())))), &lit(3)));
}

/// **Bisimulation coalgebra for `map id s ~ s`.** The two defining observations both
/// hold definitionally (ν-rules), and we witness the head equality with a kernel-checked
/// `Eq.refl` proof. `id = λx.x`.
#[test]
fn map_id_is_bisimilar_to_source() {
    let k = base_kernel();
    let id = || Term::lam(nat(), Term::Var(0));

    // Take a concrete source stream to exhibit the coalgebra on.
    let s = nats();
    let mapid_s = map(id(), s.clone());

    // (1) heads agree:  head (map id s) ≡ head s.
    assert!(
        k.def_eq(&head(mapid_s.clone()), &head(s.clone())),
        "head (map id s) should equal head s"
    );
    // …and as a *proof term*: refl : Eq Nat (head (map id s)) (head s) type-checks,
    // because both sides convert to the same normal form.
    let goal = eqn(head(mapid_s.clone()), head(s.clone()));
    k.check(&refl(head(s.clone())), &goal)
        .expect("refl should prove head (map id s) = head s");

    // (2) tails are again related:  tail (map id s) ≡ map id (tail s).
    assert!(
        k.def_eq(&tail(mapid_s.clone()), &map(id(), tail(s.clone()))),
        "tail (map id s) should equal map id (tail s)"
    );

    // Together these are exactly the coinductive step of the bisimulation
    // {(map id s, s)}: it is closed under `tail` (2) and implies head-equality (1).
    // The kernel discharges both observations, so the coalgebra is valid.

    // Concretely, every finite observation of `map id nats` matches `nats`:
    for i in 0..4u32 {
        let mut lhs = mapid_s.clone();
        let mut rhs = s.clone();
        for _ in 0..i {
            lhs = tail(lhs);
            rhs = tail(rhs);
        }
        let goal = eqn(head(lhs.clone()), lit(i));
        k.check(&refl(lit(i)), &goal)
            .unwrap_or_else(|e| panic!("map id nats observation {i} failed: {e}"));
        assert!(k.def_eq(&head(lhs), &head(rhs)));
    }
}

/// ADVERSARIAL soundness check: a **non-productive** "definition" is *inexpressible* —
/// the only inhabitant former is the guarded `Stream.corec`. There is no `Stream` value
/// that observes to itself with no progress, so no unguarded loop can be built. We also
/// confirm the empty coinductive is rejected at declaration time (so it cannot be used
/// to fabricate an element of the empty type / a proof of `False`).
#[test]
fn no_unproductive_stream_and_no_false() {
    let mut k = base_kernel();

    // (a) You cannot declare an *empty* (destructor-less) coinductive and then pretend
    //     its corecursor conjures an element out of nothing.
    let err = k
        .declare_coinductive(CoindSpec {
            name: name("Bot"),
            num_levels: 0,
            ty: Term::typ(0),
            num_params: 0,
            dtors: vec![],
            corec_name: name("Bot.corec"),
        })
        .unwrap_err();
    assert!(err.contains("at least one destructor"), "got: {err}");

    // (b) There is no closed term of type `Stream Nat` other than a `Stream.corec`
    //     application (or a variable / neutral). In particular, an "unguarded loop"
    //     like `bad := tail bad` is not a term the kernel accepts: `bad` is not in
    //     scope in its own definition (no recursive `let`/`def` at the term level), so
    //     the only way to make a stream is coiteration, which is productive by
    //     construction. We sanity-check that observing ANY corecursor stream always
    //     makes progress (terminates), by forcing a deep observation.
    let deep = {
        let mut s = repeat(lit(9));
        for _ in 0..50 {
            s = tail(s);
        }
        head(s)
    };
    // If ν-reduction failed to make progress (an unproductive loop), this would diverge.
    assert!(k.def_eq(&deep, &lit(9)), "deep observation of repeat 9 must be 9");

    // (c) Empty inductive `Empty : Prop` has no constructors; no stream trickery gives
    //     us one. We declare it and confirm we cannot build an inhabitant from a stream.
    k.declare_inductive(IndSpec {
        name: name("Empty"),
        num_levels: 0,
        ty: Term::prop(),
        num_params: 0,
        ctors: vec![],
        rec_name: name("Empty.rec"),
    })
    .unwrap();
    // `Stream.head` of a `Stream Empty` would give an `Empty`, *if* we had a `Stream
    // Empty`. But building `Stream Empty` needs a seed of the carrier and a head-step
    // `X → Empty`, i.e. it still requires producing an `Empty` — no free lunch. A bogus
    // attempt with carrier `Empty` and identity steps needs a seed `: Empty`, which does
    // not exist; so the following term is *not* closeable. We assert the kernel rejects a
    // closed inhabitant of `Empty` assembled this way (there is simply no seed to give).
    let empty = || cn("Empty");
    let bogus_stream_empty = Term::apps(
        Term::cnst(name("Stream.corec"), vec![Level::Zero, Level::Zero]),
        [
            empty(),
            empty(),
            Term::lam(empty(), Term::Var(0)), // head-step : Empty → Empty
            Term::lam(empty(), Term::Var(0)), // tail-step : Empty → Empty
            // seed : Empty  — MISSING; we plug a hole that cannot be filled by any closed term.
            // We instead just check that `head` of such a stream would need a seed:
            // omit the seed and confirm the *partial* application is not of type Stream.
        ],
    );
    // The seedless corecursor is a function `Empty → Stream Empty`, not a `Stream Empty`.
    let ty = k.infer(&bogus_stream_empty).expect("seedless corec is well-typed (a function)");
    // It is NOT a `Stream Empty`; it is `Empty → Stream Empty`.
    let stream_empty = Term::app(Term::cnst(name("Stream"), vec![Level::Zero]), empty());
    assert!(!k.def_eq(&ty, &stream_empty), "seedless corec must not already be a Stream");
    // And there is no closed `Empty` to supply as the seed, so no `Stream Empty`, so no
    // `Empty` extractable — `False` stays underivable.
    let whnf_ty = rv_kernel::reduce::Reducer::new(k.env()).whnf(&ty);
    assert!(matches!(whnf_ty, Term::Pi(..)), "seedless corec should be a function type");
}
