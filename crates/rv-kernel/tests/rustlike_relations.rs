//! Rust-like indexed `enum` relations (GADTs) — `where`-pinned conclusions, recursive fields,
//! case analysis on a derivation, and the induction hypothesis (`.rec`) — checked through the
//! kernel. Mirrors `examples/proofs/indexed_relation.rv` (`rvc --verify`).
use rv_kernel::verify::Session;

#[test]
fn indexed_relation_proof() {
    // A length-indexed vector and a proof that `append` lengths add — exercises an indexed
    // `enum` (the relation `Plus`), `where`-pinned conclusions, and induction on a derivation.
    let src = include_str!("fixtures/rustlike_relations_src.rv");
    let mut s = Session::new();
    rv_kernel::logic::declare_logic(&mut s.k).unwrap();
    if let Err(e) = s.run(src) {
        panic!("indexed relation failed:\n{e}");
    }
    assert!(s.open_fns().is_empty(), "open: {:?}", s.open_fns());
}
