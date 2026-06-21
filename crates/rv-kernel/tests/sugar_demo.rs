//! End-to-end tests for the new surface sugar: `calc` chains and `rewrite`.
use rv_kernel::systemf;

#[test]
fn calc_chain_elaborates() {
    let mut s = systemf::lang_session().unwrap();
    s.run("def x : Nat := Nat.zero").unwrap();
    s.run("def y : Nat := Nat.zero").unwrap();
    s.run("def z : Nat := Nat.zero").unwrap();
    // Two-step calc → Eq.trans of two (refl) proofs; endpoints x,y,z inferred from holes.
    s.run(
        "def chain : Eq.{1} Nat x z := \
           calc x \
             == y := Eq.refl.{1} Nat Nat.zero \
             == z := Eq.refl.{1} Nat Nat.zero",
    )
    .expect("calc chain should elaborate");
    assert!(s.k.env().contains("chain"));
}

#[test]
fn rewrite_rewrites_the_goal() {
    let mut s = systemf::lang_session().unwrap();
    s.run("def x : Nat := Nat.zero").unwrap();
    s.run("def y : Nat := Nat.zero").unwrap();
    s.run("def h : Eq.{1} Nat x y := Eq.refl.{1} Nat Nat.zero").unwrap();
    // Goal `Eq Nat x x`; `rewrite h` replaces x with y, leaving goal `Eq Nat y y`.
    s.run("def goal : Eq.{1} Nat x x := rewrite h => Eq.refl.{1} Nat y")
        .expect("rewrite should discharge via Eq.subst");
    assert!(s.k.env().contains("goal"));
}

#[test]
fn rewrite_needs_checking_position() {
    let mut s = systemf::lang_session().unwrap();
    s.run("def x : Nat := Nat.zero").unwrap();
    s.run("def h : Eq.{1} Nat x x := Eq.refl.{1} Nat x").unwrap();
    // `check` has no expected type → rewrite should report it can't run here.
    let err = s.run("check rewrite h => Eq.refl.{1} Nat x").unwrap_err();
    assert!(err.contains("checking position"), "got: {err}");
}

#[test]
fn structure_pair_projections() {
    let mut s = systemf::lang_session().unwrap();
    s.run("structure Pair (A : Type) (B : Type) where fst : A, snd : B")
        .expect("structure should desugar to inductive + projections");
    s.run("def p : Pair Nat Nat := Pair.mk Nat Nat Nat.zero (Nat.succ Nat.zero)").unwrap();
    s.run("def f : Nat := Pair.fst Nat Nat p").unwrap();
    s.run("def g : Nat := Pair.snd Nat Nat p").unwrap();
    // Projections compute: fst = 0, snd = 1.
    assert_eq!(s.run_entry("f").unwrap(), "0");
    assert_eq!(s.run_entry("g").unwrap(), "1");
}

#[test]
fn generic_congruences_work() {
    // congrArg/congrArg2 live in the shared standard library.
    let mut s = rv_kernel::stdlib::session().unwrap();
    s.run("def x : Nat := Nat.zero").unwrap();
    s.run("def h : Eq.{1} Nat x x := Eq.refl.{1} Nat x").unwrap();
    // congrArg replaces a hand-written `succ_cong`: f := Nat.succ.
    s.run(
        "def succ_eq : Eq.{1} Nat (Nat.succ x) (Nat.succ x) := \
           congrArg.{1, 1} Nat Nat (fun (n : Nat) => Nat.succ n) x x h",
    )
    .expect("congrArg should derive the successor congruence");
    // congrArg2 replaces a hand-written binary `…_cong`: f := add.
    s.run(
        "def add_eq : Eq.{1} Nat (add x x) (add x x) := \
           congrArg2.{1, 1, 1} Nat Nat Nat (fun (m : Nat) => fun (n : Nat) => add m n) x x x x h h",
    )
    .expect("congrArg2 should derive a binary congruence");
    assert!(s.k.env().contains("succ_eq") && s.k.env().contains("add_eq"));
}

#[test]
fn by_cases_pushes_function_through_stuck_match() {
    let mut s = rv_kernel::stdlib::session().unwrap();
    s.run("def bump (k : Nat) : Nat := Nat.succ k").unwrap();
    // The classic stuck-match goal: a function does NOT distribute over a stuck `match`
    // definitionally. `by_cases` splits the scrutinee so each branch reduces to `refl`.
    s.run(
        "def push (b : Bool) (x : Nat) (y : Nat) : \
           Eq.{1} Nat (bump (match b { | Bool.true => x | Bool.false => y })) \
                      (match b { | Bool.true => bump x | Bool.false => bump y }) := \
           by_cases b => Eq.refl.{1} Nat (bump x) | Eq.refl.{1} Nat (bump y)",
    )
    .expect("by_cases should discharge the stuck-match congruence");
    assert!(s.k.env().contains("push"));
}
