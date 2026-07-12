//! The independent re-check harness ([`rv_kernel::recheck_all_definitions`]) run over the
//! **whole verified `.rv` proof corpus** under `examples/proofs/`.
//!
//! `verify_rv` already checks each definition once, at the moment the tactic engine /
//! elaborator produces it, via `Kernel::add_definition`. That is necessary but is *not* the
//! same claim as "the trust boundary holds": it only shows the checker accepted what the
//! elaborator handed it, through the elaborator's own call path. This test re-derives trust
//! from scratch — for every proof file, after verification finishes, it walks the *finished*
//! environment and re-checks every stored `Def`'s value against its type with a brand-new
//! `Checker`, completely independent of how elaboration produced it. If any definition ever
//! reached the environment without being genuinely checked (a future bug in the
//! `add_definition` call sites, or an `Env::insert` bypass that shouldn't exist — see the
//! trust map in `rv_kernel::lib`), this test fails on that file, not silently trusting
//! elaboration's say-so.
use rv_driver::verify_rv_session;

/// Load and independently re-check one proof file; returns how many `Def`s it re-verified.
fn recheck(name: &str) -> usize {
    let path = format!("{}/../../examples/proofs/{}", env!("CARGO_MANIFEST_DIR"), name);
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    let session = verify_rv_session(&src).unwrap_or_else(|e| panic!("{name} failed to elaborate:\n{e}"));
    rv_kernel::recheck_all_definitions(session.k.env())
        .unwrap_or_else(|e| panic!("{name}: independent re-check failed: {e}"))
}

/// Every proof file in `examples/proofs/` exercised by `crates/rv-driver/tests/rv_proofs.rs`
/// (kept in sync with that list), re-verified independently of elaboration.
const PROOF_FILES: &[&str] = &[
    "nat_induction.rv",
    "nat_arithmetic.rv",
    "indexed_relation.rv",
    "compiler_correctness.rv",
    "stdlib.rv",
    "decide_demo.rv",
    "machine.rv",
    "partial.rv",
    "realization.rv",
    "heap.rv",
    "separation.rv",
    "word.rv",
    "bool_logic.rv",
    "arith_assoc.rv",
    "mul.rv",
    "type_soundness.rv",
    "optimizer.rv",
    "le.rv",
    "le_trans.rv",
    "refinement.rv",
    "cek_machine.rv",
    "typed_arith.rv",
    "stlc.rv",
    "reflect.rv",
    "dependent_match.rv",
    "stlc_preservation.rv",
    "systemf.rv",
    "mutual_trees.rv",
    "quotient_demo.rv",
    "trunc_demo.rv",
    "graded_demo.rv",
];

#[test]
fn whole_corpus_independently_rechecks() {
    let mut total = 0usize;
    for f in PROOF_FILES {
        total += recheck(f);
    }
    // Sanity: the corpus is non-trivial, so this should have re-checked a healthy number of
    // definitions (proofs + supporting lemmas), not silently iterated zero.
    assert!(total > 50, "expected a substantial corpus of re-checked defs, got {total}");
}
