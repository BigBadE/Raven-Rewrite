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
const NAT_DEC: &str = r#"
    def Eq.subst.{u} (A : Sort u) (P : A -> Prop) (a : A) (b : A) (h : Eq A a b) (pa : P a) : P b :=
      Eq.rec.{u, 0} A a (fun (x : A) (p : Eq A a x) => P x) pa b h
    def Eq.symm.{u} (A : Sort u) (a : A) (b : A) (h : Eq A a b) : Eq A b a :=
      Eq.rec.{u, 0} A a (fun (x : A) (p : Eq A a x) => Eq A x a) (Eq.refl.{u} A a) b h
    inductive Nat : Type | zero : Nat | succ : Nat -> Nat
    fn predN(n : Nat) -> Nat { match n { | Nat.zero => Nat.zero | Nat.succ(m) => m } }
    def natIsZero (k : Nat) : Prop :=
      Nat.rec.{1} (fun (_ : Nat) => Prop) True (fun (_ : Nat) (_ : Prop) => False) k
    def zero_ne_succ (n : Nat) (h : Eq.{1} Nat Nat.zero (Nat.succ n)) : False :=
      Eq.rec.{1, 0} Nat Nat.zero (fun (m : Nat) (_ : Eq.{1} Nat Nat.zero m) => natIsZero m) True.intro (Nat.succ n) h
    def succ_ne_zero (n : Nat) (h : Eq.{1} Nat (Nat.succ n) Nat.zero) : False :=
      zero_ne_succ n (Eq.symm.{1} Nat (Nat.succ n) Nat.zero h)
    def succ_inj (n : Nat) (m : Nat) (h : Eq.{1} Nat (Nat.succ n) (Nat.succ m)) : Eq.{1} Nat n m :=
      Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Nat n (predN x)) (Nat.succ n) (Nat.succ m) h (Eq.refl.{1} Nat n)
    def succ_cong (n : Nat) (m : Nat) (h : Eq.{1} Nat n m) : Eq.{1} Nat (Nat.succ n) (Nat.succ m) :=
      Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Nat (Nat.succ n) (Nat.succ x)) n m h (Eq.refl.{1} Nat (Nat.succ n))
    fn decEqNat(a : Nat) -> ((b : Nat) -> Decidable (Eq.{1} Nat a b)) {
        match a {
          | Nat.zero => fun (b : Nat) => match b {
              | Nat.zero    => Decidable.isTrue (Eq.{1} Nat Nat.zero Nat.zero) (Eq.refl.{1} Nat Nat.zero)
              | Nat.succ(m) => Decidable.isFalse (Eq.{1} Nat Nat.zero (Nat.succ m)) (zero_ne_succ m)
            }
          | Nat.succ(k) => fun (b : Nat) => match b {
              | Nat.zero    => Decidable.isFalse (Eq.{1} Nat (Nat.succ k) Nat.zero) (succ_ne_zero k)
              | Nat.succ(m) => match decEqNat(k)(m) {
                  | Decidable.isTrue(h)  => Decidable.isTrue (Eq.{1} Nat (Nat.succ k) (Nat.succ m)) (succ_cong k m h)
                  | Decidable.isFalse(hn) => Decidable.isFalse (Eq.{1} Nat (Nat.succ k) (Nat.succ m))
                      (fun (e : Eq.{1} Nat (Nat.succ k) (Nat.succ m)) => hn (succ_inj k m e))
                }
            }
        }
    }
    instance decNat {a : Nat} {b : Nat} : Decidable (Eq.{1} Nat a b) := decEqNat a b
"#;

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
