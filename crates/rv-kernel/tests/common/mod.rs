//! A tiny self-contained Rust-like prelude for kernel-feature tests (type classes, surface
//! sugar, diagnostics) — replacing the old habit of borrowing the big object-language corpus
//! just to get `Nat`/`Bool` in scope. No Lean-like syntax, no corpus dependency.
use rv_kernel::verify::Session;

/// The shared prelude source (Rust-like `enum`/`fn`): Bool, Nat, and `congrArg`.
pub const MINI: &str = "\
fn subst(A: Type, P: A -> Prop, a: A, b: A, h: a == b, pa: P(a)) -> P(b) {
    Eq::rec(A, a, fun (x: A) (p: a == x) => P(x), pa, b, h)
}
fn symm(A: Type, a: A, b: A, h: a == b) -> b == a {
    subst(A, fun (x: A) => x == a, a, b, h, Eq::refl(A, a))
}
fn trans(A: Type, a: A, b: A, c: A, h1: a == b, h2: b == c) -> a == c {
    subst(A, fun (x: A) => a == x, b, c, h2, h1)
}
enum Bool { false, true }
enum Nat { Zero, Succ(Nat) }
fn add(a: Nat) -> (Nat -> Nat) {
    match a { | Nat::Zero => fun (b: Nat) => b | Nat::Succ(k) => fun (b: Nat) => Nat::Succ(add(k)(b)) }
}
fn congrArg(A: Type, B: Type, f: A -> B, a: A, b: A, h: a == b) -> f(a) == f(b) {
    subst(A, fun (x: A) => f(a) == f(x), a, b, h, Eq::refl(B, f(a)))
}
fn congrArg2(A: Type, B: Type, C: Type, f: A -> (B -> C), a: A, a2: A, b: B, b2: B, ha: a == a2, hb: b == b2)
  -> f(a)(b) == f(a2)(b2) {
    subst(B, fun (y: B) => f(a)(b) == f(a2)(y), b, b2, hb,
      subst(A, fun (x: A) => f(a)(b) == f(x)(b), a, a2, ha, Eq::refl(C, f(a)(b))))
}
";

/// A fresh session with the logic prelude + the mini Rust-like prelude loaded.
pub fn session() -> Session {
    let mut s = Session::new();
    rv_kernel::logic::declare_logic(&mut s.k).expect("logic prelude");
    s.run(MINI).expect("mini prelude should check");
    s
}
