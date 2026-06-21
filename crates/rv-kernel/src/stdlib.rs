//! A small **standard library, written in the Raven surface syntax** and checked by the
//! kernel — the first slice of the "L1" layer the kernel+core plan always pointed to.
//!
//! Nothing here is primitive: every type is an ordinary `inductive`, every function is
//! a `match`-defined `fn` compiled to a recursor, and the whole prelude is
//! elaborated and type-checked through [`Session`] exactly like user code. So the
//! library is *verified Raven*, not trusted Rust — it grows the system's vocabulary
//! without growing its trust base.
//!
//! [`STDLIB`] is the source; [`load`] runs it into a session.

use crate::verify::Session;

/// The standard prelude source: core datatypes (`Bool`, `Nat`, `List`, `Option`, the
/// logical connectives, `Eq`) and their basic operations, all in surface syntax.
pub const STDLIB: &str = r#"
    -- Logical connectives.
    inductive True : Prop | intro : True
    inductive False : Prop
    inductive And (a : Prop) (b : Prop) : Prop | intro : a -> b -> And a b
    inductive Or  (a : Prop) (b : Prop) : Prop | inl : a -> Or a b | inr : b -> Or a b

    -- Propositional equality, with symmetry and substitution (the rewrite tactic uses
    -- `Eq.symm`/`Eq.subst`, both proven here via the `Eq` recursor).
    inductive Eq.{u} (A : Sort u) (a : A) : A -> Prop | refl : Eq A a a

    def Eq.symm.{u} (A : Sort u) (a : A) (b : A) (h : Eq A a b) : Eq A b a :=
      Eq.rec.{u, 0} A a (fun (x : A) (p : Eq A a x) => Eq A x a) (Eq.refl.{u} A a) b h

    def Eq.subst.{u} (A : Sort u) (P : A -> Prop) (a : A) (b : A) (h : Eq A a b) (pa : P a)
      : P b := Eq.rec.{u, 0} A a (fun (x : A) (p : Eq A a x) => P x) pa b h

    -- Generic congruences: equal arguments give equal results. These subsume the
    -- per-constructor `…_cong` lemmas one otherwise hand-writes (e.g. `f a = f b` from
    -- `a = b`), so a development needs to prove congruence only once, generically.
    def congrArg.{u, v} (A : Sort u) (B : Sort v) (f : A -> B) (a : A) (b : A) (h : Eq A a b)
      : Eq.{v} B (f a) (f b) :=
      Eq.subst.{u} A (fun (x : A) => Eq.{v} B (f a) (f x)) a b h (Eq.refl.{v} B (f a))

    def congrArg2.{u, v, w} (A : Sort u) (B : Sort v) (C : Sort w) (f : A -> (B -> C))
        (a : A) (a2 : A) (b : B) (b2 : B) (ha : Eq A a a2) (hb : Eq B b b2)
      : Eq.{w} C (f a b) (f a2 b2) :=
      Eq.subst.{v} B (fun (y : B) => Eq.{w} C (f a b) (f a2 y)) b b2 hb
        (Eq.subst.{u} A (fun (x : A) => Eq.{w} C (f a b) (f x b)) a a2 ha (Eq.refl.{w} C (f a b)))

    -- Booleans.
    inductive Bool : Type | false : Bool | true : Bool

    fn not(b: Bool) -> Bool {
        match b { | Bool.true => Bool.false | Bool.false => Bool.true }
    }
    fn and(a: Bool, b: Bool) -> Bool {
        match a { | Bool.true => b | Bool.false => Bool.false }
    }
    fn or(a: Bool, b: Bool) -> Bool {
        match a { | Bool.true => Bool.true | Bool.false => b }
    }

    -- Natural numbers and arithmetic (structural recursion on the first argument).
    inductive Nat : Type | zero : Nat | succ : Nat -> Nat

    fn add(m: Nat, n: Nat) -> Nat {
        match m { | Nat.zero => n | Nat.succ(k) => Nat.succ(k.rec) }
    }
    fn mul(m: Nat, n: Nat) -> Nat {
        match m { | Nat.zero => Nat.zero | Nat.succ(k) => add(n, k.rec) }
    }

    -- Polymorphic lists.
    inductive List (A : Type) : Type | nil : List A | cons : A -> List A -> List A

    fn length{A: Type}(xs: List A) -> Nat {
        match xs { | List.nil => Nat.zero | List.cons(h, t) => Nat.succ(t.rec) }
    }
    fn append{A: Type}(xs: List A, ys: List A) -> List A {
        match xs { | List.nil => ys | List.cons(h, t) => List.cons(A, h, t.rec) }
    }

    -- Optional values.
    inductive Option (A : Type) : Type | none : Option A | some : A -> Option A
"#;

/// Load the [`STDLIB`] prelude into a session (declaring its types and functions).
pub fn load(session: &mut Session) -> Result<(), String> {
    session.run(STDLIB)
}

/// A fresh session with the standard library loaded.
pub fn session() -> Result<Session, String> {
    let mut s = Session::new();
    load(&mut s)?;
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The whole prelude elaborates and type-checks through the kernel.
    #[test]
    fn stdlib_loads() {
        let s = session().expect("stdlib should load and check");
        for n in ["Bool", "Nat", "List", "Option", "Eq", "And", "Or", "not", "add", "mul", "length", "append"] {
            assert!(s.k.env().contains(n), "missing '{n}'");
        }
    }

    /// Library functions *compute*, so concrete specs over them auto-prove. `2 + 3 = 5`,
    /// `not (not true) = true`, `length [true] = 1`.
    #[test]
    fn stdlib_functions_compute() {
        let mut s = session().unwrap();
        // 2 + 3 = 5
        s.run(
            "fn add_2_3(u: Nat) -> Nat { \
               ensures(result == Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))); \
               add(Nat.succ(Nat.succ(Nat.zero)), Nat.succ(Nat.succ(Nat.succ(Nat.zero)))) }",
        )
        .unwrap();
        // 2 * 2 = 4
        s.run(
            "fn mul_2_2(u: Nat) -> Nat { \
               ensures(result == Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))); \
               mul(Nat.succ(Nat.succ(Nat.zero)), Nat.succ(Nat.succ(Nat.zero))) }",
        )
        .unwrap();
        // length [true] = 1
        s.run(
            "fn len_one(u: Nat) -> Nat { \
               ensures(result == Nat.succ(Nat.zero)); \
               length(List.cons(Bool, Bool.true, List.nil(Bool))) }",
        )
        .unwrap();
        assert!(s.verified("add_2_3"));
        assert!(s.verified("mul_2_2"));
        assert!(s.verified("len_one"));
    }

    /// **Inductive arithmetic lemmas proved automatically.** `x + 0 = x` and `x · 0 = 0`
    /// are true only by induction (their step cases need the hypothesis to rewrite) — the
    /// auto-prover now closes both with `Nat.rec` + the rewrite tactic. This is the kind
    /// of metatheory a verified pipeline relies on, discharged with no hand proof.
    #[test]
    fn inductive_arithmetic_lemmas_auto_prove() {
        let mut s = session().unwrap();
        s.run("fn add_zero(x: Nat) -> Nat { ensures(result == x); add(x, Nat.zero) }").unwrap();
        s.run("fn mul_zero(x: Nat) -> Nat { ensures(result == Nat.zero); mul(x, Nat.zero) }")
            .unwrap();
        assert!(s.verified("add_zero"), "x + 0 = x by induction");
        assert!(s.verified("mul_zero"), "x · 0 = 0 by induction");
    }

    /// `append` computes: `append [true] [false]` has length `2` (exercises a
    /// polymorphic, recursive library function end to end).
    #[test]
    fn stdlib_append_then_length() {
        let mut s = session().unwrap();
        s.run(
            "fn appended(u: Nat) -> Nat { \
               ensures(result == Nat.succ(Nat.succ(Nat.zero))); \
               length(append(List.cons(Bool, Bool.true, List.nil(Bool)), \
                             List.cons(Bool, Bool.false, List.nil(Bool)))) }",
        )
        .unwrap();
        assert!(s.verified("appended"), "length (append [true] [false]) ≡ 2");
    }
}
