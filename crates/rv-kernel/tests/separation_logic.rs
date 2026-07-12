//! Fractional-permission SEPARATION LOGIC (`examples/proofs/separation.rv`) checked directly
//! through the dependent kernel — the same trusted checker as `rvc --verify`, with no additions
//! to its core. Proves the ownership x dependency bridge as kernel-verified propositions: a
//! `Perm` half-unit algebra (`half + half = full`, commutative/associative composition, over-one
//! invalidity), a `l |->[pi] v` points-to over a permission-annotated heap, separating-conjunction
//! commutativity/associativity and the frame property (pointwise), full-permission exclusivity
//! (co-ownership over-provisions and is invalid — why `&mut` licenses a strong update), and shared
//! duplicability (`l |->[1]v == l |->[½]v * l |->[½]v` — why `&` is freely shared). Zero axioms.
use rv_kernel::verify::Session;
use rv_kernel::KernelExt;

/// The equality-combinator prelude that `.rv` proofs assume (mirrors `crates/rv-driver/prelude.rv`,
/// which `rvc --verify` loads automatically).
const PRELUDE: &str = "\
fn subst(A: Type, P: A -> Prop, a: A, b: A, h: a == b, pa: P(a)) -> P(b) {
    Eq::rec(A, a, fun (x: A) (p: a == x) => P(x), pa, b, h)
}
fn symm(A: Type, a: A, b: A, h: a == b) -> b == a {
    subst(A, fun (x: A) => x == a, a, b, h, Eq::refl(A, a))
}
fn trans(A: Type, a: A, b: A, c: A, h1: a == b, h2: b == c) -> a == c {
    subst(A, fun (x: A) => a == x, b, c, h2, h1)
}
fn congr_arg(A: Type, B: Type, f: A -> B, a: A, b: A, h: a == b) -> f(a) == f(b) {
    subst(A, fun (x: A) => f(a) == f(x), a, b, h, Eq::refl(B, f(a)))
}
";

#[test]
fn separation_logic_proofs_check_in_kernel() {
    let src = include_str!("../../../examples/proofs/separation.rv");
    let mut s = Session::new();
    rv_kernel::logic::declare_logic(&mut s.k).expect("logic prelude");
    s.k.install_quot().expect("quotient schema");
    s.k.install_funext().expect("funext (derived from quotients)");
    s.run(PRELUDE).expect("equality prelude should check");
    match s.run(src) {
        Ok(()) => {}
        Err(e) => panic!("separation.rv failed to check in the kernel:\n{e}"),
    }
    assert!(
        s.open_fns().is_empty(),
        "open proof obligations remain: {:?}",
        s.open_fns()
    );
}
