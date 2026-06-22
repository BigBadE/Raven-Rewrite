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
fn refinement() {
    check("refinement.rv");
    let path = format!("{}/../../examples/proofs/refinement.rv", env!("CARGO_MANIFEST_DIR"));
    let src = std::fs::read_to_string(&path).unwrap();
    // `safe_pred(2)` auto-discharges `is_pos(2)` and runs to `pred 2 = 1` (one `Succ`).
    let run = verify_rv(&src, Some("example")).unwrap().run.unwrap().unwrap();
    assert_eq!(run.matches("Succ").count(), 1, "pred of 2 should be 1, got {run}");
    // `only_one(1)` auto-discharges the equation `1 == 1` and runs to `pred 1 = 0`.
    let run2 = verify_rv(&src, Some("also")).unwrap().run.unwrap().unwrap();
    assert!(run2.contains("Zero") && run2.matches("Succ").count() == 0, "pred of 1 should be 0, got {run2}");
}

#[test]
fn cek_machine() {
    check("cek_machine.rv");
    // It also evaluates (\x. x + 1) 2 to 3.
    let path = format!("{}/../../examples/proofs/cek_machine.rv", env!("CARGO_MANIFEST_DIR"));
    let src = std::fs::read_to_string(&path).unwrap();
    let run = verify_rv(&src, Some("answer")).unwrap().run.unwrap().unwrap();
    // 3 = Succ (Succ (Succ Zero)) — three Succs.
    let succs = run.matches("Succ").count();
    assert_eq!(succs, 3, "expected the machine to compute 3, got {run}");
}

#[test]
fn typed_arith() {
    check("typed_arith.rv");
}

#[test]
fn stlc() {
    check("stlc.rv");
}

#[test]
fn reflect() {
    check("reflect.rv");
}

#[test]
fn dependent_match() {
    check("dependent_match.rv");
}

#[test]
fn stlc_preservation() {
    // Full STLC preservation in Rust-like .rv: the autosubst substitution lemma (weakening +
    // sub_lemma) plus the `preservation` theorem — a well-typed term that steps stays
    // well-typed — for beta + application congruences, via injectivity-based inversion.
    check("stlc_preservation.rv");
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
