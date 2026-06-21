//! Rust-like Raven proofs (`enum` data, `::` paths, `==` propositions, `//` comments, and a
//! proof-by-induction `fn` whose IH is a recursive call) checked through the dependent kernel.
//! This mirrors `examples/proofs/nat_induction.rv`, which `rvc --verify` checks the same way.
use rv_kernel::verify::Session;

#[test]
fn rustlike_enum_and_induction_proof() {
    let src = r#"
        enum Nat { Zero, Succ(Nat) }

        fn plus(n: Nat, m: Nat) -> Nat {
            match n {
              | Nat::Zero => m
              | Nat::Succ(k) => Nat::Succ(plus(k, m))
            }
        }

        // Leibniz substitution, defined in Raven itself on the equality eliminator.
        fn subst(A: Type, P: A -> Prop, a: A, b: A, h: a == b, pa: P(a)) -> P(b) {
            Eq::rec(A, a, fun (x: A) (p: a == x) => P(x), pa, b, h)
        }

        fn succ_cong(a: Nat, b: Nat, h: a == b) -> Nat::Succ(a) == Nat::Succ(b) {
            subst(Nat, fun (x: Nat) => Nat::Succ(a) == Nat::Succ(x), a, b, h,
                  Eq::refl(Nat, Nat::Succ(a)))
        }

        fn plus_zero(n: Nat) -> plus(n, Nat::Zero) == n {
            match n {
              | Nat::Zero => Eq::refl(Nat, Nat::Zero)
              | Nat::Succ(k) => succ_cong(plus(k, Nat::Zero), k, plus_zero(k))
            }
        }
    "#;
    let mut s = Session::new();
    rv_kernel::logic::declare_logic(&mut s.k).unwrap();
    match s.run(src) {
        Ok(()) => {}
        Err(e) => panic!("rustlike proof failed:\n{e}"),
    }
    // The proof obligation for plus_zero should be discharged (it's a `fn` whose body is the proof).
    assert!(s.open_fns().is_empty(), "open obligations remain: {:?}", s.open_fns());
}
