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

/// `plus_comm` and a `mult` algebra (right-identity, right-zero, left-distributivity over
/// `plus`) extending the verified Nat arithmetic in `nat_induction.rv`/`arith_assoc.rv`.
#[test]
fn stdlib_nat() {
    check("stdlib_nat.rv");
}

/// `reverse` (with its involution law), `map` fusion, and `map_id` extending the generic
/// `List<A>` library in `stdlib.rv`.
#[test]
fn stdlib_list() {
    check("stdlib_list.rv");
}

/// `Option<A>`'s `bind` and its monad laws (left/right identity, associativity), plus the
/// `map`/`bind` relating laws, extending `stdlib.rv`'s `Option<A>`.
#[test]
fn stdlib_option() {
    check("stdlib_option.rv");
}

/// A verified boolean algebra: `and`/`or` commutativity/associativity/identity, both
/// distributivity laws, both De Morgan laws, double negation, and absorption — extending the
/// small library in `bool_logic.rv`.
#[test]
fn stdlib_bool() {
    check("stdlib_bool.rv");
}

/// Nat `<=` ordering: antisymmetry (extending `le.rv`/`le_trans.rv`), `max`/`min` with their
/// commutativity/bounding lemmas, and monotonicity of `plus` w.r.t. `<=`.
#[test]
fn stdlib_order() {
    check("stdlib_order.rv");
}

/// More `List<A>` lemmas: `length` vs. `reverse`, `mem`/`mem_append`, `filter` with a length
/// bound, `all`/`any` distributing over `append`, and `foldr`'s append-fusion law.
#[test]
fn stdlib_list2() {
    check("stdlib_list2.rv");
}

/// Verified insertion sort over `List<Nat>`: `leb`'s two-way reflection into `Le`
/// (`leb_true_le`/`leb_false_le`), `insert`/`isort` with their length-preservation lemmas, and
/// the headline correctness theorem `sorted_isort` — insertion sort produces a sorted list.
#[test]
fn alg_sorting() {
    check("alg_sorting.rv");
}

/// A verified binary search tree over `Nat`: `insert`/`member`, and the membership headlines
/// `insert_member` (the inserted key is found) and `member_insert_other` (insert preserves
/// existing members).
#[test]
fn bst() {
    check("bst.rv");
}

/// The BST ORDERING invariant (bounded-tree predicates `all_lt`/`all_gt`/`is_bst`) and its
/// preservation under `insert`: the headline `insert_preserves_bst` (`is_bst(t) == True ->
/// is_bst(insert(x, t)) == True`), built from the two bound-propagation crux lemmas
/// `all_lt_insert`/`all_gt_insert`.
#[test]
fn bst_ordered() {
    check("bst_ordered.rv");
}

/// Regression for the `run_solo_fn` auto-curry elaborator crash (see the file's own header):
/// a `match <param> { .. }` whose parameter list also declares a later hypothesis mentioning
/// the scrutinee (the convoy shape from `bst.rv`/`bst_ordered.rv`) used to crash even when
/// that hypothesis went unused, because the non-recursive `fn` was wrongly auto-curried.
#[test]
fn convoy_hyp_direct() {
    check("convoy_hyp_direct.rv");
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
fn opt_constfold() {
    check("opt_constfold.rv");
}

/// A verified stack-machine compiler: `Expr` (literals/`+`/`*`) compiled to a flat `Instr`
/// program for a stack machine `exec`, with the headline
/// `compile_correct : exec(compile(e), Nil) == Cons(eval(e), Nil)`, proved via the standard
/// generalized-stack strengthening `exec_compile : exec(compile(e), s) == Cons(eval(e), s)`.
#[test]
fn compile_stack() {
    check("compile_stack.rv");
}

/// Algebraic simplification (`e+0=e`, `0+e=e`, `e*1=e`, `1*e=e`, `e*0=0`, `0*e=0`) via smart
/// constructors, with the headline `simplify_correct : eval(simplify(e)) == eval(e)`.
#[test]
fn opt_simplify() {
    check("opt_simplify.rv");
}

/// The optimizing-compiler capstone: consolidates `opt_simplify.rv` and `compile_stack.rv` into
/// one end-to-end theorem, `opt_compile_correct : exec(compile(simplify(e)), Nil) == Cons(eval(e), Nil)`
/// (compiling the optimized expression on the empty stack still yields the correct result), plus
/// the bonus `opt_compile_preserves : exec(compile(simplify(e)), Nil) == exec(compile(e), Nil)`.
#[test]
fn opt_compile_pipeline() {
    check("opt_compile_pipeline.rv");
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

/// Big-step ⟹ multi-step small-step equivalence (`eval_to_steps`) for a bool/`if` + Peano-`Suc`
/// object language, complementing `typed_arith.rv`'s progress/preservation development with the
/// other classic operational-semantics correspondence.
#[test]
fn bigstep_smallstep() {
    check("bigstep_smallstep.rv");
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
fn coinductive_demo() {
    check("coinductive.rv");
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

/// The consolidation capstone: one file exercising the whole ladder — an
/// executable fn with a borrow-checked strong update through `&mut` and a
/// refinement-typed precondition (routed to `rv-solve` + the VM), an
/// inductive proof by recursion, cubical `refl`/`ap`/`transport`/`J`, the
/// genuinely-computing `S1c` HIT recursor, the `Equiv` algebra
/// (`idEquiv`/`symEquiv`/`compEquiv`), and `ua`/`Univalence` STATED (not
/// proved — see docs/cubical.md §6). See `examples/proofs/capstone.rv`.
#[test]
fn capstone() {
    check("capstone.rv");
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

/// A self-recursive call from inside a *second*, nested `match` — recursing on both of a
/// `fn`'s parameters at once (`max`'s natural, non-curried form) used to reject with "unknown
/// name" because a plain non-dependent recursor IH can't represent a call that varies a
/// second parameter. The elaborator now auto-curries this internally (see
/// `rv_kernel::verify::Session::run_solo_fn`), so the natural two-parameter source verifies
/// without the manual `Nat -> (Nat -> Nat)` currying workaround.
#[test]
fn nested_match_self_recursion_on_two_params() {
    let src = r#"
enum Nat { Zero, Succ(Nat) }
fn max(n: Nat, m: Nat) -> Nat {
    match n {
      | Nat::Zero    => m
      | Nat::Succ(a) => match m {
          | Nat::Zero    => Nat::Succ(a)
          | Nat::Succ(b) => Nat::Succ(max(a, b))
        }
    }
}
fn max_two_one(u: Nat) -> Nat
    ensures result == Nat::Succ(Nat::Succ(Nat::Zero));
{
    max(Nat::Succ(Nat::Succ(Nat::Zero)), Nat::Succ(Nat::Zero))
}
"#;
    let r = verify_rv(src, None).expect("nested-match self-recursion on two params should elaborate");
    assert!(r.all_verified(), "open: {:?}", r.open);
}

/// The auto-currying rewrite must not over-broaden name scope: a call to a name that is
/// genuinely undefined inside the nested match arm still fails with "unknown name", not
/// silently resolve to something in the recursion machinery.
#[test]
fn nested_match_undefined_name_still_rejected() {
    let src = r#"
enum Nat { Zero, Succ(Nat) }
fn max(n: Nat, m: Nat) -> Nat {
    match n {
      | Nat::Zero    => m
      | Nat::Succ(a) => match m {
          | Nat::Zero    => Nat::Succ(a)
          | Nat::Succ(b) => Nat::Succ(bogus(a, b))
        }
    }
}
"#;
    let err = verify_rv(src, None).unwrap_err();
    assert!(err.contains("unknown name"), "expected an unknown-name error, got: {err}");
}
