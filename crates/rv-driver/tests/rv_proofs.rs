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

// The generic `stdlib.rv` subsumes the old monomorphic `list.rv` / `list_map.rv` /
// `append_assoc.rv`: it proves length_append, map_length, map_append and append_assoc once,
// for *every* element type.
#[test]
fn generic_stdlib() {
    check("stdlib.rv");
}

#[test]
fn decide_reflection() {
    check("decide_demo.rv");
}

/// Machine types (Bool algebra, a 1-bit wrapping adder proved equal to mod-2 arithmetic,
/// signed-int negation) modeled in Raven and kernel-checked — the kernel gains no native
/// machine support. Demonstrates the unified trust architecture.
#[test]
fn machine_model() {
    check("machine.rv");
}

/// The partiality membrane modeled as a kernel-checked type: a divergent `Partial<Empty>` is
/// constructible (Turing-complete) but cannot be forced without a termination witness, so no
/// `fn () -> Empty` exists. Lets a total kernel admit a partial runtime, soundly.
#[test]
fn partial_membrane() {
    check("partial.rv");
}

/// The realization layer made explicit: the trusted model↔native `axiom`s, with a proof that a
/// model law transfers to the native op through them. The complete realization trust list.
#[test]
fn realization_axioms() {
    check("realization.rv");
}

/// A mutable heap modeled as `Addr -> Option<Val>` with the McCarthy read-over-write laws
/// proved — how references get meaning with no kernel notion of mutable state.
#[test]
fn heap_laws() {
    check("heap.rv");
}

/// A bounded machine word: the 1-bit wrapping adder proved to be a commutative group
/// (identity, self-inverse, commutativity, associativity) — overflow arithmetic's algebra.
#[test]
fn word_algebra() {
    check("word.rv");
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
fn systemf() {
    // System F (polymorphic λ-calculus): the typing relation over type/term de Bruijn
    // binders + PROGRESS (a closed well-typed term is a value or steps), via canonical forms
    // (curried-value convoy) and the `Exists`/`Or` step witness. Preservation builds on this.
    check("systemf.rv");
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
