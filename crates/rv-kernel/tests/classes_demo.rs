use rv_kernel::systemf;

#[test]
fn type_class_resolution() {
    let mut s = systemf::lang_session().unwrap(); // has Nat, Bool
    s.run("class Show (A : Type) where show : A -> Nat").expect("class");
    s.run("instance showBool : Show Bool := Show.mk Bool (fun (b : Bool) => Nat.zero)")
        .expect("instance");
    // {A}{d : Show A} are implicit; d must be resolved from the instance table.
    s.run("def useShow {A : Type} {d : Show A} (x : A) : Nat := Show.show A d x")
        .expect("def using a class method");
    s.run("def r : Nat := useShow Bool.true").expect("instance resolved at the use site");
    assert_eq!(s.run_entry("r").unwrap(), "0");
}

#[test]
fn missing_instance_errors() {
    let mut s = systemf::lang_session().unwrap();
    s.run("class Show (A : Type) where show : A -> Nat").unwrap();
    s.run("def useShow {A : Type} {d : Show A} (x : A) : Nat := Show.show A d x").unwrap();
    // No instance for `Show Nat` registered → resolution fails with a clear message.
    let err = s.run("def r : Nat := useShow Nat.zero").unwrap_err();
    assert!(err.contains("no instance found"), "got: {err}");
}

/// omega-lite: a verified decidable Nat-equality instance + `decide` proving a closed goal
/// by reflection (no hand proof).
const NAT_DEC: &str = include_str!("fixtures/classes_demo_nat_dec.rvk");

#[test]
fn decide_proves_closed_nat_equality() {
    let mut s = rv_kernel::verify::Session::new();
    // Load Decidable/decide/of_decide_eq_true via the kernel path, then layer Nat on top.
    rv_kernel::reflect::declare_reflection(&mut s.k).expect("reflection prelude");
    s.run(NAT_DEC).expect("verified decEqNat + instance");
    // `2 == 2` proved entirely by reflection — no manual proof term.
    s.run(
        "def two_eq_two : Eq.{1} Nat (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero)) := by_decide",
    )
    .expect("by_decide should prove a true closed Nat equality");
    // A FALSE goal: decide computes to `false`, so the reflection proof is rejected.
    let err = s
        .run("def bad : Eq.{1} Nat Nat.zero (Nat.succ Nat.zero) := by_decide")
        .unwrap_err();
    assert!(err.contains("bad"), "false goal should be rejected: {err}");
    assert!(s.k.env().contains("two_eq_two"));
}
