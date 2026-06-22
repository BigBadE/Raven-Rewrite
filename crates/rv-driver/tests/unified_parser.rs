//! The unified front-end: `.rv` proof files parsed by the **single** `rv-syntax` parser
//! and translated to kernel commands (no second text parser), then kernel-checked. Each
//! file here must verify identically to the `verify_rv` (kernel-parser) path — proving the
//! one parser is at parity for the Rust-style proof fragment.
use rv_driver::verify_rv_unified;

fn check_unified(name: &str) {
    let path = format!("{}/../../examples/proofs/{}", env!("CARGO_MANIFEST_DIR"), name);
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    let report = verify_rv_unified(&src, None)
        .unwrap_or_else(|e| panic!("{name} failed through the unified front-end:\n{e}"));
    assert!(report.all_verified(), "{name} not verified (unified); open: {:?}", report.open);
}

#[test]
fn unified_one_file() {
    // The flagship "one file, runtime computation + proof, one checker" file, now also
    // parsed by the one front-end parser.
    check_unified("unified.rv");
}
