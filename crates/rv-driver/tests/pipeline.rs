//! End-to-end pipeline tests: source text → verified → compiled → run.
use rv_driver::{run_pipeline, verify, Value};

/// A program whose call-site precondition and assertion are discharged from
/// concrete values, and which runs to a known result.
#[test]
fn div_main_verifies_and_runs() {
    let src = r#"
        fn div(x: i64, y: i64) -> i64
          requires y != 0;
        {
          return x / y;
        }
        fn main() -> i64 {
          let a: i64 = 10;
          let b: i64 = 2;
          assert b != 0;
          return div(a, b);
        }
    "#;
    let report = run_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "expected all obligations discharged: {report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(5))));
}

/// A refinement precondition (`x > 0`) discharges the division-by-zero obligation
/// in the callee body via linear arithmetic.
#[test]
fn refinement_precondition_discharges_div() {
    let src = r#"
        fn recip(x: i64) -> i64
          requires x > 0;
        {
          return 100 / x;
        }
    "#;
    let report = verify(src).expect("front-end ok");
    assert!(report.all_verified(), "x > 0 should imply x != 0: {report:?}");
    assert!(report.obligations.iter().any(|o| o.origin.contains("division")));
}

/// Soundness guard: a division with no precondition must NOT verify (x could be 0).
#[test]
fn unguarded_division_is_not_verified() {
    let src = r#"
        fn bad(x: i64) -> i64 {
          return 100 / x;
        }
    "#;
    let report = verify(src).expect("front-end ok");
    assert!(!report.all_verified(), "unguarded division must not be proved safe");
    assert!(report.num_failed() >= 1);
}

/// `panic` aborts; the non-panicking path runs normally.
#[test]
fn panic_path_aborts_other_runs() {
    let src = r#"
        fn checked(x: i64) -> i64 {
          if x < 0 { panic; }
          return x;
        }
        fn main() -> i64 { return checked(7); }
    "#;
    let report = run_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(7))));
}

/// The `?` operator composes on a call result (Option propagation), end to end.
#[test]
fn try_operator_runs() {
    let src = r#"
        enum Opt { None, Some(i64), }
        fn first(x: i64) -> Opt {
          if x > 0 { return Opt::Some(x); }
          return Opt::None;
        }
        fn unwrap_add(x: i64) -> Opt {
          let v: i64 = first(x)?;
          return Opt::Some(wrapping_add(v, 1));
        }
        fn main() -> i64 {
          let r: Opt = unwrap_add(5);
          match r { Opt::Some(n) => { return n; } Opt::None => { return 0; } }
        }
    "#;
    let report = run_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(6))));
}

/// Overflow safety: a bounded sum is proved to stay within range.
#[test]
fn bounded_addition_verifies_no_overflow() {
    let src = r#"
        fn add(a: i64, b: i64) -> i64
          requires a >= 0;
          requires a <= 100;
          requires b >= 0;
          requires b <= 100;
        {
          return a + b;
        }
    "#;
    let report = verify(src).expect("front-end ok");
    assert!(report.all_verified(), "bounded a+b must prove no overflow: {report:?}");
    assert!(report.obligations.iter().any(|o| o.origin.contains("overflow")));
}

/// Soundness guard: an unbounded `a + b` can overflow, so it must NOT verify.
#[test]
fn unbounded_addition_is_not_verified() {
    let src = r#"
        fn add(a: i64, b: i64) -> i64 { return a + b; }
    "#;
    let report = verify(src).expect("front-end ok");
    assert!(!report.all_verified(), "unbounded a+b can overflow; must not be proved safe");
    assert!(report.num_failed() >= 1);
    assert!(report.obligations.iter().any(|o| o.origin.contains("overflow")));
}

/// The `wrapping_*` opt-out: `wrapping_add` emits NO overflow obligation, so an
/// unbounded wrapping sum verifies (and runs with native wrapping arithmetic).
#[test]
fn wrapping_addition_opts_out_of_overflow() {
    let src = r#"
        fn add(a: i64, b: i64) -> i64 { return wrapping_add(a, b); }
        fn main() -> i64 { return add(2, 3); }
    "#;
    let report = run_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "wrapping_add must not require an overflow proof: {report:?}");
    assert!(!report.obligations.iter().any(|o| o.origin.contains("overflow")));
    assert_eq!(report.run, Some(Ok(Value::Int(5))));
}

/// Generics (type-erased) + a method (`impl` desugared to a function + resolved call).
#[test]
fn generics_and_methods_run() {
    let src = r#"
        struct Point { x: i64, y: i64, }
        impl Point {
          fn sum(self) -> i64 { return wrapping_add(self.x, self.y); }
        }
        fn id<T>(x: T) -> T { return x; }
        fn main() -> i64 {
          let p: Point = Point { x: 3, y: 4 };
          let n: i64 = id(1);
          return p.sum();
        }
    "#;
    let report = run_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(7))));
}

/// References: take `&mut`, mutate through it, observe at the source.
#[test]
fn mutable_reference_mutation_runs() {
    let src = r#"
        fn main() -> i64 {
          let x: i64 = 1;
          let r: &mut i64 = &mut x;
          *r = 5;
          return x;
        }
    "#;
    let report = run_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(5))));
}

/// Ownership: using an ADT value after it was moved is a borrow-check error.
#[test]
fn use_after_move_is_rejected() {
    let src = r#"
        struct S { v: i64 }
        fn main() -> i64 {
          let a: S = S { v: 1 };
          let b: S = a;
          let c: S = a;
          return b.v;
        }
    "#;
    let report = verify(src).expect("front-end ok");
    assert!(!report.all_verified(), "use-after-move must be rejected");
    assert!(report.borrow_errors.iter().any(|e| e.contains("moved")));
}

/// Enums + exhaustive `match`, compiled and run.
#[test]
fn enum_match_runs() {
    let src = r#"
        enum Opt { None, Some(i64), }
        fn main() -> i64 {
          let o: Opt = Opt::Some(42);
          match o {
            Opt::Some(x) => { return x; }
            Opt::None => { return 0; }
          }
        }
    "#;
    let report = run_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(42))));
}

/// Structs: construct, then read fields back through projections.
#[test]
fn struct_field_access_runs() {
    let src = r#"
        struct Point { x: i64, y: i64, }
        fn main() -> i64 {
          let p: Point = Point { x: 3, y: 4 };
          return wrapping_add(p.x, p.y);
        }
    "#;
    let report = run_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(7))));
}

/// Loop invariant proved by induction: holds on entry and is preserved.
#[test]
fn loop_invariant_verifies() {
    let src = r#"
        fn sum_to(n: i64) -> i64
          requires n >= 0;
        {
          let i: i64 = 0;
          let s: i64 = 0;
          while i < n
            invariant i >= 0;
          {
            i = wrapping_add(i, 1);
            s = wrapping_add(s, i);
          }
          return s;
        }
    "#;
    let report = verify(src).expect("front-end ok");
    assert!(report.all_verified(), "loop invariant should be inductive: {report:?}");
    assert!(report.obligations.iter().any(|o| o.origin.contains("invariant")));
}

/// A non-exhaustive match is rejected as a front-end (type) error.
#[test]
fn non_exhaustive_match_is_rejected() {
    let src = r#"
        enum Three { A, B, C, }
        fn pick(t: Three) -> i64 {
          let u: Three = Three::A;
          match u {
            Three::A => { return 1; }
            Three::B => { return 2; }
          }
        }
    "#;
    assert!(verify(src).is_err(), "non-exhaustive match must be a type error");
}

/// A precondition over a struct *field* (`p.v != 0`) discharges a body's
/// division by that same field — the spec's `p.v` and the code's read of `p.v`
/// share one uninterpreted projection term, so congruence connects them.
#[test]
fn field_precondition_discharges_div() {
    let src = r#"
        struct P { v: i64 }
        fn recip(p: P) -> i64
          requires p.v != 0;
        {
          return 100 / p.v;
        }
    "#;
    let report = verify(src).expect("front-end ok");
    assert!(report.all_verified(), "p.v != 0 should guard the division: {report:?}");
    assert!(report.obligations.iter().any(|o| o.origin.contains("division")));
}

/// Soundness guard for field specs: with no precondition, the field division
/// must NOT verify (`p.v` could be 0).
#[test]
fn unguarded_field_division_is_not_verified() {
    let src = r#"
        struct P { v: i64 }
        fn recip(p: P) -> i64 {
          return 100 / p.v;
        }
    "#;
    let report = verify(src).expect("front-end ok");
    assert!(!report.all_verified(), "unguarded field division must not be proved safe");
    assert!(report.num_failed() >= 1);
}

/// Branching: the prover uses the path condition. On the `then` branch `x != 0`
/// holds, so the division is safe there; we guard the else branch too.
#[test]
fn branch_path_condition_is_used() {
    let src = r#"
        fn safe(x: i64) -> i64 {
          if x > 0 {
            return 100 / x;
          } else {
            return 0;
          }
        }
    "#;
    let report = verify(src).expect("front-end ok");
    assert!(report.all_verified(), "path condition x>0 should guard the division: {report:?}");
}

// ---------------------------------------------------------------------------
// The verified-Raven path: dependent-type-theory kernel surface (`.rvk`).
// ---------------------------------------------------------------------------

/// A Raven kernel-surface program verifies through the dependent kernel: a `match`-
/// defined recursive function plus a spec proved automatically by computation, all on
/// top of the preloaded standard library.
/// A Rust-like `.rv` proof program with an `ensures` spec, verified through the kernel.
#[test]
fn raven_kernel_program_verifies() {
    let src = r#"
        enum Nat { Zero, Succ(Nat) }
        fn dbl(n: Nat) -> Nat {
            match n {
              | Nat::Zero    => Nat::Zero
              | Nat::Succ(k) => Nat::Succ(Nat::Succ(k.rec))
            }
        }
        fn dbl_two(u: Nat) -> Nat {
            ensures(result == Nat::Succ(Nat::Succ(Nat::Succ(Nat::Succ(Nat::Zero)))));
            dbl(Nat::Succ(Nat::Succ(Nat::Zero)))
        }
    "#;
    let report = rv_driver::verify_rv(src, None).expect("front-end ok");
    assert!(report.all_verified(), "dbl 2 ≡ 4 should verify: {report:?}");
    assert!(report.verified.contains(&"dbl_two".to_string()));
}

/// A false spec is *not* reported as verified (soundness through the driver path).
#[test]
fn raven_kernel_false_spec_stays_open() {
    let src = r#"
        enum Nat { Zero, Succ(Nat) }
        fn wrong(x: Nat) -> Nat {
            ensures(result == Nat::Succ(x));
            x
        }
    "#;
    let report = rv_driver::verify_rv(src, None).expect("front-end ok");
    assert!(!report.all_verified(), "a false spec must not verify");
    assert!(report.open.contains(&"wrong".to_string()));
}

/// The surface as a *compiler*, not just a verifier: a parameterless `answer` is evaluated to
/// its canonical value through the driver's run path.
#[test]
fn raven_kernel_program_runs() {
    let src = r#"
        enum Nat { Zero, Succ(Nat) }
        fn dbl(n: Nat) -> Nat {
            match n { | Nat::Zero => Nat::Zero | Nat::Succ(k) => Nat::Succ(Nat::Succ(k.rec)) }
        }
        fn answer() -> Nat { dbl(Nat::Succ(Nat::Succ(Nat::Zero))) }
    "#;
    let report = rv_driver::verify_rv(src, Some("answer")).expect("front-end ok");
    assert!(report.all_verified());
    // dbl 2 ≡ 4 = four Succs.
    assert_eq!(report.run.unwrap().unwrap().matches("Succ").count(), 4, "dbl 2 should evaluate to 4");
}
