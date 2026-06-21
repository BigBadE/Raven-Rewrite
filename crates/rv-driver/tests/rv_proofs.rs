//! The verified `.rv` proofs under `examples/proofs/` check through the kernel (the same path
//! as `rvc --verify`). Keeps the Rust-like Raven proof corpus green in CI.
use rv_driver::verify_rv;

fn check(name: &str) {
    let path = format!("{}/../../examples/proofs/{}", env!("CARGO_MANIFEST_DIR"), name);
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    let report = verify_rv(&src, None).unwrap_or_else(|e| panic!("{name} failed to elaborate:\n{e}"));
    assert!(report.all_verified(), "{name} not verified; open: {:?}", report.open);
}

#[test]
fn nat_induction() {
    check("nat_induction.rv");
}

#[test]
fn nat_arithmetic() {
    check("nat_arithmetic.rv");
}

#[test]
fn indexed_relation() {
    check("indexed_relation.rv");
}
