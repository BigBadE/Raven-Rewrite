//! End-to-end tests for the public `default_registry()` API.
//!
//! The contract under test is purely about soundness + the documented fragment:
//! VALID obligations must `Discharge`; INVALID ones must NOT (they return `Failed`).

use super::default_registry;
use rv_core::{BinOp, Prop, Sym, Symbols, Term};
use rv_logic::Obligation;

// --- small builders so the tests read like the math ------------------------

fn cmp(op: BinOp, a: Term, b: Term) -> Prop {
    Prop::Holds(Term::bin(op, a, b))
}
fn var(x: Sym) -> Term {
    Term::Var(x)
}
fn int(n: i64) -> Term {
    Term::Int(n)
}

/// Discharge `ctx ⟹ goal` and report whether it was discharged.
fn discharges(ctx: Prop, goal: Prop) -> bool {
    let reg = default_registry();
    let ob = Obligation::new(ctx, goal, "test");
    reg.discharge(&ob).is_discharged()
}

/// Discharge `ctx ⟹ goal` and return the `Failed` message (panics if discharged).
fn failure_message(ctx: Prop, goal: Prop) -> Option<String> {
    let reg = default_registry();
    let ob = Obligation::new(ctx, goal, "test");
    match reg.discharge(&ob) {
        rv_logic::Outcome::Failed(m) => m,
        rv_logic::Outcome::Discharged(_) => panic!("expected Failed, got Discharged"),
    }
}

/// A non-linear opaque term `a / b` (Div is not linear ⇒ opaque). Used to exercise the
/// equality/congruence fragment over genuinely uninterpreted operands.
fn opaque(a: Sym, b: Sym) -> Term {
    Term::bin(BinOp::Div, var(a), var(b))
}

// ===========================================================================
// VALID obligations — must discharge
// ===========================================================================

/// Congruence over uninterpreted applications: `a == b ⟹ f(a) == f(b)`. The
/// equality `a == b` is linear, so this also exercises sharing it into the
/// congruence closure (theory combination).
#[test]
fn congruence_apps_discharges() {
    let mut s = Symbols::new();
    let (a, b, f) = (s.intern("a"), s.intern("b"), s.intern("f"));
    let ctx = cmp(BinOp::Eq, var(a), var(b));
    let goal = cmp(
        BinOp::Eq,
        Term::app(f, vec![var(a)]),
        Term::app(f, vec![var(b)]),
    );
    assert!(discharges(ctx, goal));
}

/// Two-argument congruence: `a == c ∧ b == d ⟹ g(a, b) == g(c, d)`.
#[test]
fn congruence_binary_app_discharges() {
    let mut s = Symbols::new();
    let (a, b, c, d, g) = (
        s.intern("a"),
        s.intern("b"),
        s.intern("c"),
        s.intern("d"),
        s.intern("g"),
    );
    let ctx = cmp(BinOp::Eq, var(a), var(c)).and(cmp(BinOp::Eq, var(b), var(d)));
    let goal = cmp(
        BinOp::Eq,
        Term::app(g, vec![var(a), var(b)]),
        Term::app(g, vec![var(c), var(d)]),
    );
    assert!(discharges(ctx, goal));
}

/// Soundness: congruence must not over-fire. With no `a == b`, `f(a) == f(b)`
/// is invalid and must NOT discharge.
#[test]
fn congruence_apps_no_overfire() {
    let mut s = Symbols::new();
    let (a, b, f) = (s.intern("a"), s.intern("b"), s.intern("f"));
    let goal = cmp(
        BinOp::Eq,
        Term::app(f, vec![var(a)]),
        Term::app(f, vec![var(b)]),
    );
    assert!(!discharges(Prop::True, goal));
}

#[test]
fn gt_zero_implies_ne_zero() {
    // x > 0  ⟹  x != 0
    let mut s = Symbols::new();
    let x = s.intern("x");
    let ctx = cmp(BinOp::Gt, var(x), int(0));
    let goal = cmp(BinOp::Ne, var(x), int(0));
    assert!(discharges(ctx, goal));
}

#[test]
fn ge_one_implies_ne_zero() {
    // x >= 1  ⟹  x != 0
    let mut s = Symbols::new();
    let x = s.intern("x");
    let ctx = cmp(BinOp::Ge, var(x), int(1));
    let goal = cmp(BinOp::Ne, var(x), int(0));
    assert!(discharges(ctx, goal));
}

#[test]
fn eq_implies_itself() {
    // (a == b)  ⟹  (a == b)
    let mut s = Symbols::new();
    let a = s.intern("a");
    let b = s.intern("b");
    let p = cmp(BinOp::Eq, var(a), var(b));
    assert!(discharges(p.clone(), p));
}

#[test]
fn between_3_and_5_implies_eq_4() {
    // x < 5 ∧ x > 3  ⟹  x == 4
    let mut s = Symbols::new();
    let x = s.intern("x");
    let ctx = cmp(BinOp::Lt, var(x), int(5)).and(cmp(BinOp::Gt, var(x), int(3)));
    let goal = cmp(BinOp::Eq, var(x), int(4));
    assert!(discharges(ctx, goal));
}

#[test]
fn goal_true_is_trivial() {
    // anything ⟹ True
    let mut s = Symbols::new();
    let x = s.intern("x");
    assert!(discharges(cmp(BinOp::Gt, var(x), int(0)), Prop::True));
}

#[test]
fn false_context_proves_anything() {
    // False ⟹ (x > 0)   (vacuously valid)
    let mut s = Symbols::new();
    let x = s.intern("x");
    assert!(discharges(Prop::False, cmp(BinOp::Gt, var(x), int(0))));
}

#[test]
fn transitivity_of_le() {
    // x <= y ∧ y <= z  ⟹  x <= z
    let mut s = Symbols::new();
    let (x, y, z) = (s.intern("x"), s.intern("y"), s.intern("z"));
    let ctx = cmp(BinOp::Le, var(x), var(y)).and(cmp(BinOp::Le, var(y), var(z)));
    let goal = cmp(BinOp::Le, var(x), var(z));
    assert!(discharges(ctx, goal));
}

#[test]
fn disjunctive_goal_discharged() {
    // x >= 1  ⟹  (x > 0 ∨ x == -7)   — true via the left disjunct.
    let mut s = Symbols::new();
    let x = s.intern("x");
    let ctx = cmp(BinOp::Ge, var(x), int(1));
    let goal = cmp(BinOp::Gt, var(x), int(0)).or(cmp(BinOp::Eq, var(x), int(-7)));
    assert!(discharges(ctx, goal));
}

#[test]
fn scaled_coefficients() {
    // 2*x <= 4  ⟹  x <= 2
    let mut s = Symbols::new();
    let x = s.intern("x");
    let two_x = Term::bin(BinOp::Mul, int(2), var(x));
    let ctx = cmp(BinOp::Le, two_x, int(4));
    let goal = cmp(BinOp::Le, var(x), int(2));
    assert!(discharges(ctx, goal));
}

#[test]
fn negated_implication_in_context() {
    // (x > 0 ⟹ x > 0)  is a tautology stated as the goal with empty-ish ctx.
    let mut s = Symbols::new();
    let x = s.intern("x");
    let goal = cmp(BinOp::Gt, var(x), int(0)).implies(cmp(BinOp::Gt, var(x), int(0)));
    assert!(discharges(Prop::True, goal));
}

// ===========================================================================
// INVALID obligations — must NOT discharge (sound failure)
// ===========================================================================

#[test]
fn ge_zero_does_not_imply_ne_zero() {
    // x >= 0  ⟹  x != 0   is INVALID (x could be 0). Must NOT discharge.
    let mut s = Symbols::new();
    let x = s.intern("x");
    let ctx = cmp(BinOp::Ge, var(x), int(0));
    let goal = cmp(BinOp::Ne, var(x), int(0));
    assert!(!discharges(ctx, goal), "x>=0 does NOT imply x!=0 (x=0 is a counterexample)");
}

#[test]
fn true_does_not_imply_gt_zero() {
    // true  ⟹  x > 0   is INVALID. Must NOT discharge.
    let mut s = Symbols::new();
    let x = s.intern("x");
    assert!(!discharges(Prop::True, cmp(BinOp::Gt, var(x), int(0))));
}

#[test]
fn unrelated_vars_not_valid() {
    // x > 0  ⟹  y > 0   is INVALID (y unconstrained).
    let mut s = Symbols::new();
    let (x, y) = (s.intern("x"), s.intern("y"));
    let ctx = cmp(BinOp::Gt, var(x), int(0));
    let goal = cmp(BinOp::Gt, var(y), int(0));
    assert!(!discharges(ctx, goal));
}

#[test]
fn le_does_not_imply_lt() {
    // x <= 5  ⟹  x < 5   is INVALID (x could be 5).
    let mut s = Symbols::new();
    let x = s.intern("x");
    let ctx = cmp(BinOp::Le, var(x), int(5));
    let goal = cmp(BinOp::Lt, var(x), int(5));
    assert!(!discharges(ctx, goal));
}

#[test]
fn nonlinear_goal_fails_soundly() {
    // x > 0  ⟹  x * y > 0   — x*y is non-linear (opaque). We cannot prove it, and we
    // must NOT (it is in fact invalid for y <= 0). Must NOT discharge.
    let mut s = Symbols::new();
    let (x, y) = (s.intern("x"), s.intern("y"));
    let ctx = cmp(BinOp::Gt, var(x), int(0));
    let goal = cmp(BinOp::Gt, Term::bin(BinOp::Mul, var(x), var(y)), int(0));
    assert!(!discharges(ctx, goal));
}

#[test]
fn opaque_atom_consistent_is_not_proved() {
    // p ⟹ q  with p, q opaque booleans is INVALID. Must NOT discharge.
    let mut s = Symbols::new();
    let p = Prop::Holds(var(s.intern("p")));
    let q = Prop::Holds(var(s.intern("q")));
    assert!(!discharges(p, q));
}

#[test]
fn opaque_atom_self_implication_discharges() {
    // p ⟹ p  with p opaque IS valid (¬p ∧ p is unsat). Must discharge.
    let mut s = Symbols::new();
    let p = Prop::Holds(var(s.intern("p")));
    assert!(discharges(p.clone(), p));
}

// ===========================================================================
// Counterexamples — invalid obligations should report a concrete model
// ===========================================================================

#[test]
fn counterexample_true_does_not_imply_gt_zero() {
    // true ⟹ x > 0 is invalid; a model with x ≤ 0 must be found in the box.
    let mut s = Symbols::new();
    let x = s.intern("x");
    let msg = failure_message(Prop::True, cmp(BinOp::Gt, var(x), int(0)))
        .expect("expected a counterexample string");
    assert!(msg.starts_with("counterexample:"), "got: {msg}");
    // The reported value of x must actually violate x > 0 (i.e. x ≤ 0).
    let val = parse_var_value(&msg, x);
    assert!(val <= 0, "counterexample {msg} should have x<=0");
}

#[test]
fn counterexample_ge_zero_not_ne_zero() {
    // x >= 0 ⟹ x != 0 is invalid; the only counterexample is x = 0.
    let mut s = Symbols::new();
    let x = s.intern("x");
    let ctx = cmp(BinOp::Ge, var(x), int(0));
    let goal = cmp(BinOp::Ne, var(x), int(0));
    let msg = failure_message(ctx, goal).expect("expected a counterexample string");
    assert!(msg.starts_with("counterexample:"), "got: {msg}");
    assert_eq!(parse_var_value(&msg, x), 0, "the only model is x=0; got {msg}");
}

#[test]
fn counterexample_le_does_not_imply_lt() {
    // x <= 5 ⟹ x < 5 is invalid; x = 5 is the witness.
    let mut s = Symbols::new();
    let x = s.intern("x");
    let ctx = cmp(BinOp::Le, var(x), int(5));
    let goal = cmp(BinOp::Lt, var(x), int(5));
    let msg = failure_message(ctx, goal).expect("expected a counterexample string");
    assert!(msg.starts_with("counterexample:"), "got: {msg}");
    assert_eq!(parse_var_value(&msg, x), 5, "the only model is x=5; got {msg}");
}

/// Pull the integer value assigned to `sym` out of a "counterexample: vN=.., .." string.
fn parse_var_value(msg: &str, sym: Sym) -> i64 {
    let needle = format!("v{}=", sym.0);
    let rest = msg.split(&needle).nth(1).unwrap_or_else(|| panic!("{sym:?} not in {msg}"));
    let num: String =
        rest.chars().take_while(|c| c.is_ascii_digit() || *c == '-').collect();
    num.parse().unwrap_or_else(|_| panic!("bad number in {msg}"))
}

// ===========================================================================
// Equality / congruence over opaque (uninterpreted) operands
// ===========================================================================

#[test]
fn eq_transitivity_over_opaque() {
    // a == b ∧ b == c ⟹ a == c, where a,b,c are opaque (Div) terms.
    let mut s = Symbols::new();
    let (a, b, c, d) = (s.intern("a"), s.intern("b"), s.intern("c"), s.intern("d"));
    let (oa, ob, oc) = (opaque(a, d), opaque(b, d), opaque(c, d));
    let ctx = Prop::Holds(Term::bin(BinOp::Eq, oa.clone(), ob.clone()))
        .and(Prop::Holds(Term::bin(BinOp::Eq, ob, oc.clone())));
    let goal = Prop::Holds(Term::bin(BinOp::Eq, oa, oc));
    assert!(discharges(ctx, goal), "equality transitivity over opaque terms must hold");
}

#[test]
fn eq_symmetry_over_opaque() {
    // a == b ⟹ b == a over opaque terms.
    let mut s = Symbols::new();
    let (a, b, d) = (s.intern("a"), s.intern("b"), s.intern("d"));
    let (oa, ob) = (opaque(a, d), opaque(b, d));
    let ctx = Prop::Holds(Term::bin(BinOp::Eq, oa.clone(), ob.clone()));
    let goal = Prop::Holds(Term::bin(BinOp::Eq, ob, oa));
    assert!(discharges(ctx, goal), "equality symmetry over opaque terms must hold");
}

#[test]
fn eq_and_neq_is_contradiction() {
    // a == b ∧ a != b ⟹ False : the context is UNSAT, so it discharges *anything*.
    let mut s = Symbols::new();
    let (a, b, d) = (s.intern("a"), s.intern("b"), s.intern("d"));
    let (oa, ob) = (opaque(a, d), opaque(b, d));
    let ctx = Prop::Holds(Term::bin(BinOp::Eq, oa.clone(), ob.clone()))
        .and(Prop::Holds(Term::bin(BinOp::Ne, oa, ob)));
    // The goal here is False; an UNSAT context proves it.
    assert!(discharges(ctx.clone(), Prop::False), "contradictory context proves False");
    // And it proves an arbitrary unrelated opaque goal too.
    let g = Prop::Holds(var(s.intern("anything")));
    assert!(discharges(ctx, g), "contradictory context proves anything");
}

#[test]
fn opaque_eq_does_not_overreach() {
    // a == b ⟹ a == c (c unrelated) is INVALID — congruence must not invent it.
    let mut s = Symbols::new();
    let (a, b, c, d) = (s.intern("a"), s.intern("b"), s.intern("c"), s.intern("d"));
    let (oa, ob, oc) = (opaque(a, d), opaque(b, d), opaque(c, d));
    let ctx = Prop::Holds(Term::bin(BinOp::Eq, oa.clone(), ob));
    let goal = Prop::Holds(Term::bin(BinOp::Eq, oa, oc));
    assert!(!discharges(ctx, goal), "must not prove a==c from a==b alone");
}

// ===========================================================================
// Strengthened arithmetic — constant multiples, folding, x+x ≡ 2*x
// ===========================================================================

#[test]
fn two_x_gt_four_implies_x_gt_one() {
    // 2*x > 4  ⟹  x > 1.  Over ints 2x>4 ⟺ x>=3, which implies x>1. VALID.
    let mut s = Symbols::new();
    let x = s.intern("x");
    let two_x = Term::bin(BinOp::Mul, int(2), var(x));
    let ctx = cmp(BinOp::Gt, two_x, int(4));
    let goal = cmp(BinOp::Gt, var(x), int(1));
    assert!(discharges(ctx, goal));
}

#[test]
fn x_plus_x_equals_two_x() {
    // x + x <= 4  ⟹  2*x <= 4 : `x+x` and `2*x` must normalize identically.
    let mut s = Symbols::new();
    let x = s.intern("x");
    let x_plus_x = Term::bin(BinOp::Add, var(x), var(x));
    let two_x = Term::bin(BinOp::Mul, int(2), var(x));
    let ctx = cmp(BinOp::Le, x_plus_x, int(4));
    let goal = cmp(BinOp::Le, two_x, int(4));
    assert!(discharges(ctx, goal));
}

#[test]
fn mul_on_right_side_is_handled() {
    // x*3 <= 6  ⟹  x <= 2 : constant multiplier on the *right* side. VALID.
    let mut s = Symbols::new();
    let x = s.intern("x");
    let x_times_3 = Term::bin(BinOp::Mul, var(x), int(3));
    let ctx = cmp(BinOp::Le, x_times_3, int(6));
    let goal = cmp(BinOp::Le, var(x), int(2));
    assert!(discharges(ctx, goal));
}

#[test]
fn constant_folding_normalizes() {
    // 2*x + 3 > x + 1  ⟹  x > -2.  LHS-RHS = x + 2 > 0 ⟺ x > -2. VALID.
    let mut s = Symbols::new();
    let x = s.intern("x");
    let lhs = Term::bin(BinOp::Add, Term::bin(BinOp::Mul, int(2), var(x)), int(3));
    let rhs = Term::bin(BinOp::Add, var(x), int(1));
    let ctx = cmp(BinOp::Gt, lhs, rhs);
    let goal = cmp(BinOp::Gt, var(x), int(-2));
    assert!(discharges(ctx, goal));
}

#[test]
fn scaled_lower_bound_is_not_overstrengthened() {
    // 2*x > 4 ⟹ x > 2 is INVALID over rationals/our procedure?  Over ints 2x>4 ⟺
    // x>=3 ⟹ x>2, so it IS valid. But 2*x >= 4 ⟹ x > 2 is INVALID (x=2 works).
    let mut s = Symbols::new();
    let x = s.intern("x");
    let two_x = Term::bin(BinOp::Mul, int(2), var(x));
    let ctx = cmp(BinOp::Ge, two_x, int(4)); // x >= 2
    let goal = cmp(BinOp::Gt, var(x), int(2)); // x > 2
    assert!(!discharges(ctx, goal), "x>=2 does NOT imply x>2 (x=2 counterexample)");
}
