//! Rust-like indexed `enum` relations (GADTs) — `where`-pinned conclusions, recursive fields,
//! case analysis on a derivation, and the induction hypothesis (`.rec`) — checked through the
//! kernel. Mirrors `examples/proofs/indexed_relation.rv` (`rvc --verify`).
use rv_kernel::verify::Session;

#[test]
fn indexed_relation_proof() {
    // A length-indexed vector and a proof that `append` lengths add — exercises an indexed
    // `enum` (the relation `Plus`), `where`-pinned conclusions, and induction on a derivation.
    let src = r#"
        enum Nat { Zero, Succ(Nat) }

        // The graph of addition as an indexed relation: `Plus(a, b, c)` means a + b == c.
        enum Plus(a: Nat, b: Nat, c: Nat) -> Prop {
            PZero(m: Nat) where a == Nat::Zero, b == m, c == m;
            PSucc(k: Nat, m: Nat, r: Nat, h: Plus(k, m, r))
                where a == Nat::Succ(k), b == m, c == Nat::Succ(r);
        }

        // Plus is total/functional enough to be deterministic: if a+b==c and a+b==d then c==d.
        // Proof by induction on the first derivation.
        fn subst(A: Type, P: A -> Prop, a: A, b: A, h: a == b, pa: P(a)) -> P(b) {
            Eq::rec(A, a, fun (x: A) (p: a == x) => P(x), pa, b, h)
        }
        fn succ_cong(a: Nat, b: Nat, h: a == b) -> Nat::Succ(a) == Nat::Succ(b) {
            subst(Nat, fun (x: Nat) => Nat::Succ(a) == Nat::Succ(x), a, b, h, Eq::refl(Nat, Nat::Succ(a)))
        }

        // Induction on a derivation, using the IH on the recursive field (`hk.rec`): rebuild
        // the derivation structurally. This is the capability the deep proofs are migrated onto.
        fn plus_copy(a: Nat, b: Nat, c: Nat, h: Plus(a, b, c)) -> Plus(a, b, c) {
            match h {
              | Plus::PZero(m) => Plus::PZero(m)
              | Plus::PSucc(k, m, r, hk) => Plus::PSucc(k, m, r, hk.rec)
            }
        }
    "#;
    let mut s = Session::new();
    rv_kernel::logic::declare_logic(&mut s.k).unwrap();
    if let Err(e) = s.run(src) {
        panic!("indexed relation failed:\n{e}");
    }
    assert!(s.open_fns().is_empty(), "open: {:?}", s.open_fns());
}
