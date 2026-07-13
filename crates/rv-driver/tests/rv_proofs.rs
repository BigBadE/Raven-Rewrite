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

/// Fractional-permission SEPARATION LOGIC, proved by the kernel: a `Perm` half-unit algebra
/// (`half + half = full`, commutative/associative composition, over-one invalidity), a
/// permission-annotated heap with a `l |->[pi] v` points-to, heap composition with pointwise
/// separating-conjunction commutativity/associativity and the frame property, and the
/// ownership x dependency bridge as theorems — a full-permission owner cannot admit a companion
/// (over-provisioning is invalid: the `&mut` exclusivity), and a shared points-to splits into two
/// readers (`l |->[1]v == l |->[½]v * l |->[½]v`: the `&` duplicability). Zero axioms.
#[test]
fn separation_logic() {
    check("separation.rv");
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

// --- Quotient types, propositional truncation, and QTT-graded binders reachable from
// `.rv` surface syntax (`Quot`/`Trunc`'s dotted-name constants installed by the driver;
// the `(x :1 T) -> U` / `fun (x :1 T) => …` graded-binder spelling checked by the
// kernel's usage pass — see `crates/rv-kernel/src/graded.rs`). ---

#[test]
fn quotient_demo() {
    check("quotient_demo.rv");
}

#[test]
fn trunc_demo() {
    check("trunc_demo.rv");
}

/// The cubical layer (`Path`/`PathP`, interval literals/connections, `plam`/`papp`,
/// and the derived `refl`/`ap`/`pfunext`/`transport`/`psubst`/`J`/`ptrans`/
/// `path_to_eq`/`eq_to_path`), plus the interval HIT `I2` — see
/// `crates/rv-kernel/src/cubical_surface.rs` and `crates/rv-kernel/src/elab2.rs`.
#[test]
fn cubical() {
    check("cubical.rv");
}

/// The consolidated cubical layer's showcase: `S1c`/`S2` (the genuinely-computing
/// cubical circle/sphere HITs), `Equiv`/`idEquiv` (bi-invertible equivalences),
/// `ua` (univalence, stated), and the equivalence ALGEBRA (`idToEquiv`/`symEquiv`/
/// `compEquiv`, the `compEquiv` unit laws, `symEquiv`'s involution, `ap`-
/// functoriality, and the `Univalence` statement itself) — on top of the base
/// `Path`/`I2` layer `cubical()` above already covers. See
/// `crates/rv-kernel/src/kernel_ext.rs`'s `install_s1c`/`install_s2`/
/// `install_equiv`/`install_contr`/`install_hae`/`install_ua`/`install_fiber2`/
/// `install_equiv_algebra`, and `docs/cubical.md`.
#[test]
fn cubical_showcase() {
    check("cubical_showcase.rv");
}

#[test]
fn graded_demo() {
    check("graded_demo.rv");
}

#[test]
fn graded_binder_linear_violation_rejected() {
    // A `:1` (linear) binder used twice must be a hard verification error, not silently
    // accepted — the whole point of the usage discipline.
    let path = format!(
        "{}/../../examples/proofs/graded_demo_linear_violation.rv",
        env!("CARGO_MANIFEST_DIR")
    );
    let src = std::fs::read_to_string(&path).unwrap();
    let err = verify_rv(&src, None).unwrap_err();
    assert!(err.contains("usage discipline"), "expected a usage-discipline error, got: {err}");
}

#[test]
fn funext_smoke_test() {
    let src = r#"
enum Nat { Zero, Succ(Nat) }
fn test(f: Nat -> Nat, g: Nat -> Nat, h: (x: Nat) -> f(x) == g(x)) -> f == g {
    funext(Nat, Nat, f, g, h)
}
"#;
    let r = verify_rv(src, None).expect("funext usable from surface .rv");
    assert!(r.all_verified(), "open: {:?}", r.open);
}
