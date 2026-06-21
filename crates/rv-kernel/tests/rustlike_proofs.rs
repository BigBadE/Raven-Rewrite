//! Rust-like Raven proofs (`enum` data, `::` paths, `==` propositions, `//` comments, and a
//! proof-by-induction `fn` whose IH is a recursive call) checked through the dependent kernel.
//! This mirrors `examples/proofs/nat_induction.rv`, which `rvc --verify` checks the same way.
use rv_kernel::verify::Session;

#[test]
fn rustlike_enum_and_induction_proof() {
    let src = include_str!("fixtures/rustlike_proofs_src.rv");
    let mut s = Session::new();
    rv_kernel::logic::declare_logic(&mut s.k).unwrap();
    match s.run(src) {
        Ok(()) => {}
        Err(e) => panic!("rustlike proof failed:\n{e}"),
    }
    // The proof obligation for plus_zero should be discharged (it's a `fn` whose body is the proof).
    assert!(s.open_fns().is_empty(), "open obligations remain: {:?}", s.open_fns());
}
