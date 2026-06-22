//! Type-class resolution as a kernel feature — tested against a tiny self-contained Rust-like
//! prelude (`mod common`), not the object-language corpus. (`decide`/`by_decide` reflection is
//! covered in Rust-like by `examples/proofs/reflect.rv`.)
mod common;

#[test]
fn type_class_resolution() {
    let mut s = common::session();
    s.run("class Show (A : Type) where show : A -> Nat").expect("class");
    s.run("instance showBool : Show Bool := Show::mk(Bool, fun (b: Bool) => Nat::Zero)")
        .expect("instance");
    // {A}{d : Show A} are implicit; d must be resolved from the instance table.
    s.run("fn useShow {A: Type} {d: Show A} (x: A) -> Nat { Show::show(A, d, x) }")
        .expect("fn using a class method");
    s.run("fn r() -> Nat { useShow(Bool::true) }").expect("instance resolved at the use site");
    assert_eq!(s.run_entry("r").unwrap(), "Nat.Zero");
}

#[test]
fn missing_instance_errors() {
    let mut s = common::session();
    s.run("class Show (A : Type) where show : A -> Nat").unwrap();
    s.run("fn useShow {A: Type} {d: Show A} (x: A) -> Nat { Show::show(A, d, x) }").unwrap();
    // No instance for `Show Nat` registered → resolution fails with a clear message.
    let err = s.run("fn r() -> Nat { useShow(Nat::Zero) }").unwrap_err();
    assert!(err.contains("no instance found"), "got: {err}");
}
