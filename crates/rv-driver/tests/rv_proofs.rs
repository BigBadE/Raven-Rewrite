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

#[test]
fn compiler_correctness() {
    check("compiler_correctness.rv");
}

#[test]
fn list_lib() {
    check("list.rv");
}

#[test]
fn bool_logic() {
    check("bool_logic.rv");
}

#[test]
fn arith_assoc() {
    check("arith_assoc.rv");
}

#[test]
fn mul() {
    check("mul.rv");
}

#[test]
fn type_soundness() {
    check("type_soundness.rv");
}

#[test]
fn optimizer() {
    check("optimizer.rv");
}

#[test]
fn list_map() {
    check("list_map.rv");
}

#[test]
fn append_assoc() {
    check("append_assoc.rv");
}

#[test]
fn le() {
    check("le.rv");
}

#[test]
fn le_trans() {
    check("le_trans.rv");
}

#[test]
fn mutual_trees() {
    check("mutual_trees.rv");
    // It also computes: a forest of two leaves has size 2.
    let path = format!("{}/../../examples/proofs/mutual_trees.rv", env!("CARGO_MANIFEST_DIR"));
    let src = std::fs::read_to_string(&path).unwrap();
    let report = verify_rv(&src, Some("example")).unwrap();
    let run = report.run.unwrap().unwrap();
    assert!(run.contains("Succ") && run.contains("Zero"), "expected a size-2 Nat, got {run}");
}
