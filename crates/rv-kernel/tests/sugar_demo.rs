//! End-to-end tests for the surface sugar (`calc`, `rewrite`, `structure`, `by_cases`,
//! `congrArg`) — against a tiny self-contained Rust-like prelude (`mod common`), no corpus.
mod common;

#[test]
fn calc_chain_elaborates() {
    let mut s = common::session();
    s.run("fn x() -> Nat { Nat::Zero }").unwrap();
    s.run("fn y() -> Nat { Nat::Zero }").unwrap();
    s.run("fn z() -> Nat { Nat::Zero }").unwrap();
    // Two-step calc → Eq.trans of two (refl) proofs; endpoints x,y,z inferred from holes.
    s.run(
        "fn chain() -> x == z { \
           calc x \
             == y := Eq::refl(Nat, Nat::Zero) \
             == z := Eq::refl(Nat, Nat::Zero) }",
    )
    .expect("calc chain should elaborate");
    assert!(s.k.env().contains("chain"));
}

#[test]
fn rewrite_rewrites_the_goal() {
    let mut s = common::session();
    s.run("fn x() -> Nat { Nat::Zero }").unwrap();
    s.run("fn y() -> Nat { Nat::Zero }").unwrap();
    s.run("fn h() -> x == y { Eq::refl(Nat, Nat::Zero) }").unwrap();
    // Goal `x == x`; `rewrite h` replaces x with y, leaving goal `y == y`.
    s.run("fn goal() -> x == x { rewrite h => Eq::refl(Nat, y) }")
        .expect("rewrite should discharge via Eq.subst");
    assert!(s.k.env().contains("goal"));
}

#[test]
fn rewrite_needs_checking_position() {
    let mut s = common::session();
    s.run("fn x() -> Nat { Nat::Zero }").unwrap();
    s.run("fn h() -> x == x { Eq::refl(Nat, x) }").unwrap();
    // `check` has no expected type → rewrite should report it can't run here.
    let err = s.run("check rewrite h => Eq::refl(Nat, x)").unwrap_err();
    assert!(err.contains("checking position"), "got: {err}");
}

#[test]
fn structure_pair_projections() {
    let mut s = common::session();
    s.run("structure Pair (A : Type) (B : Type) where fst : A, snd : B")
        .expect("structure should desugar to inductive + projections");
    s.run("fn p() -> Pair Nat Nat { Pair::mk(Nat, Nat, Nat::Zero, Nat::Succ(Nat::Zero)) }").unwrap();
    s.run("fn f() -> Nat { Pair::fst(Nat, Nat, p) }").unwrap();
    s.run("fn g() -> Nat { Pair::snd(Nat, Nat, p) }").unwrap();
    // Projections compute: fst = 0, snd = 1.
    assert_eq!(s.run_entry("f").unwrap(), "Nat.Zero");
    assert_eq!(s.run_entry("g").unwrap(), "Nat.Succ Nat.Zero");
}

#[test]
fn generic_congruences_work() {
    let mut s = common::session();
    s.run("fn x() -> Nat { Nat::Zero }").unwrap();
    s.run("fn h() -> x == x { Eq::refl(Nat, x) }").unwrap();
    // congrArg replaces a hand-written `succ_cong`: f := Nat::Succ.
    s.run("fn succ_eq() -> Nat::Succ(x) == Nat::Succ(x) { congrArg(Nat, Nat, fun (n: Nat) => Nat::Succ(n), x, x, h) }")
        .expect("congrArg should derive the successor congruence");
    // congrArg2 replaces a hand-written binary `…_cong`: f := add.
    s.run("fn add_eq() -> add(x)(x) == add(x)(x) { congrArg2(Nat, Nat, Nat, add, x, x, x, x, h, h) }")
        .expect("congrArg2 should derive a binary congruence");
    assert!(s.k.env().contains("succ_eq") && s.k.env().contains("add_eq"));
}

#[test]
fn by_cases_pushes_function_through_stuck_match() {
    let mut s = common::session();
    s.run("fn bump(k: Nat) -> Nat { Nat::Succ(k) }").unwrap();
    // The classic stuck-match goal: a function does NOT distribute over a stuck `match`
    // definitionally. `by_cases` splits the scrutinee so each branch reduces to `refl`.
    s.run(
        "fn push(b: Bool, x: Nat, y: Nat) -> \
           bump(match b { | Bool::true => x | Bool::false => y }) == \
           (match b { | Bool::true => bump(x) | Bool::false => bump(y) }) \
         { by_cases b => Eq::refl(Nat, bump(x)) | Eq::refl(Nat, bump(y)) }",
    )
    .expect("by_cases should discharge the stuck-match congruence");
    assert!(s.k.env().contains("push"));
}
