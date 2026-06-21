//! End-to-end pipeline tests: source text → verified → compiled → run.
use rv_driver::{run_pipeline, run_rust_modules_pipeline, run_rust_pipeline, verify, Value};

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

/// Real Rust source (tree-sitter frontend) with a `#[requires]` spec verifies + runs.
#[test]
fn real_rust_file_verifies_and_runs() {
    let src = r#"
        #[requires(y != 0)]
        fn div(x: i64, y: i64) -> i64 { return x / y; }
        fn main() -> i64 { let a: i64 = 10; let b: i64 = 2; return div(a, b); }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(5))));
}

/// Real Rust: `let S { x, y } = p;` destructures a struct via field projections.
#[test]
fn rust_struct_destructuring_runs() {
    let src = r#"
        struct Point { x: i64, y: i64 }
        fn main() -> i64 {
          let p: Point = Point { x: 3, y: 4 };
          let Point { x, y } = p;
          return x.wrapping_add(y);
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(7))));
}

/// Sized integers: `u8 + u8` can exceed 255, so an unguarded add must NOT verify
/// (width-specific overflow bound).
#[test]
fn rust_u8_addition_can_overflow() {
    let src = r#"fn add(a: u8, b: u8) -> u8 { return a + b; }"#;
    let report = run_rust_pipeline(src, None).expect("front-end ok");
    assert!(!report.all_verified(), "u8 + u8 can overflow 255; must not verify");
    assert!(report.obligations.iter().any(|o| o.origin.contains("overflow")));
}

/// Sized integers: bounding the inputs proves the `u8` sum stays within range,
/// and a `u8` parameter's implicit `0 <= a <= 255` makes the result run.
#[test]
fn rust_bounded_u8_addition_verifies_and_runs() {
    let src = r#"
        #[requires(a <= 100)]
        fn inc(a: u8) -> u8 { return a + 1; }
        fn main() -> i64 { let r: u8 = inc(41); return r; }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "bounded u8 add should verify: {report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(42))));
}

/// `Vec`: `new`/`push`/`len`/index, with a `v.len()` guard discharging the
/// dynamic bounds obligation on `v[i]`.
#[test]
fn rust_vec_push_len_guarded_index_runs() {
    let src = r#"
        fn main() -> i64 {
          let mut v: Vec<i64> = Vec::new();
          v.push(10);
          v.push(20);
          v.push(30);
          let n: i64 = v.len();
          if n > 1 { return v[1]; }
          return 0;
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "guarded vec index should verify: {report:?}");
    assert!(report.obligations.iter().any(|o| o.origin.contains("out of bounds")));
    assert_eq!(report.run, Some(Ok(Value::Int(20))));
}

/// `for x in v.iter()` over a `Vec` iterates by index: the element `x` is the
/// real `v[i]`, its read bounds-checked and discharged by the loop guard, and it
/// executes to the summed total.
#[test]
fn rust_for_over_sequence_runs() {
    let src = r#"
        fn main() -> i64 {
          let mut v: Vec<i64> = Vec::new();
          v.push(2);
          v.push(40);
          let mut total: i64 = 0;
          for x in v.iter() {
            total = total.wrapping_add(x);
          }
          return total;
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert!(report.obligations.iter().any(|o| o.origin.contains("out of bounds")));
    assert_eq!(report.run, Some(Ok(Value::Int(42))));
}

/// Bitwise & shift operators (`& | ^ << >>`) execute with exact i64 semantics and
/// emit no overflow obligation (they can't overflow the way `+`/`*` do).
#[test]
fn rust_bitwise_and_shift_run() {
    let src = r#"
        fn main() -> i64 {
          let a: i64 = 12;
          let b: i64 = 10;
          let mut acc: i64 = (a & b) | (a ^ b);
          acc = acc ^ 1;
          let shifted: i64 = 1 << 4;
          // Bitwise results are opaque to the linear solver, so combine them with
          // `wrapping_*` (the explicit overflow opt-out) to keep the path verified.
          return acc.wrapping_add(shifted).wrapping_sub(shifted >> 2);
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    // (12&10)=8, (12^10)=6, 8|6=14, 14^1=15; 1<<4=16; 16>>2=4; 15+16-4 = 27.
    assert_eq!(report.run, Some(Ok(Value::Int(27))));
}

/// `vec![a, b, c]` expands to a real `Vec` aggregate (length 3), so `.len()` and
/// a guarded index verify.
#[test]
fn rust_vec_macro_runs() {
    let src = r#"
        fn main() -> i64 {
          let v: Vec<i64> = vec![10, 20, 30];
          let n: i64 = v.len();
          if n > 1 { return v[1]; }
          return 0;
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(20))));
}

/// A closure that captures an enclosing local runs end-to-end: closure conversion
/// lifts `|x| x.wrapping_add(base)` to a top-level function whose first parameter
/// is the captured `base`, and the indirect call prepends the captured `10`, so
/// `f(5)` computes `5 + 10 = 15`.
#[test]
fn rust_closure_capture_and_call_runs() {
    let src = r#"
        fn main() -> i64 {
          let base: i64 = 10;
          let f = |x: i64| x.wrapping_add(base);
          return f(5);
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(15))));
}

/// The higher-order case that the whole stdlib build rests on: a generic function
/// `apply<F: Fn(i64)->i64>(f, x)` calls its closure argument *indirectly* (the
/// target is a runtime value, not statically known), exactly as `Iterator::map`
/// will. `apply(|n| n*3, 4)` runs to `12`.
#[test]
fn rust_higher_order_closure_arg_runs() {
    let src = r#"
        fn apply<F: Fn(i64) -> i64>(f: F, x: i64) -> i64 {
          return f(x);
        }
        fn main() -> i64 {
          let g = |n: i64| n.wrapping_mul(3);
          return apply(g, 4);
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(12))));
}

/// A `&[T]` slice parameter is modeled as the sequence it views: `.len()` and
/// guarded indexing verify via the same dynamic-length bounds machinery as `Vec`.
#[test]
fn rust_slice_param_len_and_guarded_index_runs() {
    let src = r#"
        fn first_or_zero(xs: &[i64]) -> i64 {
          let n: i64 = xs.len();
          if n > 0 { return xs[0]; }
          return 0;
        }
        fn main() -> i64 {
          let v: Vec<i64> = Vec::new();
          return first_or_zero(&v);
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "guarded slice index should verify: {report:?}");
    assert!(report.obligations.iter().any(|o| o.origin.contains("out of bounds")));
}

/// Soundness guard: an unguarded `Vec` index past a known-too-small length must
/// NOT verify.
#[test]
fn rust_vec_unguarded_index_is_not_verified() {
    let src = r#"
        fn main() -> i64 {
          let mut v: Vec<i64> = Vec::new();
          v.push(10);
          return v[5];
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(!report.all_verified(), "unguarded vec index must not be proved safe");
    assert!(report.obligations.iter().any(|o| o.origin.contains("out of bounds")));
}

/// Built-in `Option` prelude + combinators (`unwrap_or`, `is_some`).
#[test]
fn rust_option_combinators_run() {
    let src = r#"
        fn lookup(x: i64) -> Option {
          if x > 0 { return Option::Some(x); }
          return Option::None;
        }
        fn main() -> i64 {
          let a: Option = lookup(5);
          let b: Option = lookup(0);
          let av: i64 = a.unwrap_or(0);
          let bv: i64 = b.unwrap_or(99);
          if a.is_some() { return av.wrapping_add(bv); }
          return 0;
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(104)))); // 5 + 99
}

/// Built-in `Result` prelude + `is_ok`/`unwrap`.
#[test]
fn rust_result_unwrap_runs() {
    let src = r#"
        fn parse(x: i64) -> Result {
          if x >= 0 { return Result::Ok(x); }
          return Result::Err(x);
        }
        fn main() -> i64 {
          let r: Result = parse(7);
          if r.is_ok() { return r.unwrap(); }
          return 0;
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(7))));
}

/// `Self` in an impl (type + `Self { .. }` + `Self::new`), unqualified prelude
/// variants (`Some`/`None`), and `as` casts all resolve.
#[test]
fn rust_self_unqualified_variants_and_casts_run() {
    let src = r#"
        struct Counter { n: i64 }
        impl Counter {
          fn new(start: i64) -> Self { return Self { n: start }; }
          fn get(self) -> i64 { return self.n; }
        }
        fn find(x: i64) -> Option {
          if x > 0 { return Some(x); }
          return None;
        }
        fn main() -> i64 {
          let c: Counter = Counter::new(41);
          let o: Option = find(5);
          let v: i64 = o.unwrap_or(0);
          let w: i32 = 7 as i32;
          return c.get().wrapping_add(v).wrapping_add(w as i64);
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(53)))); // 41 + 5 + 7
}

/// Value-position `match` and `if`/`else`: a `let` bound to a structured
/// expression whose arms/branches each produce the bound value.
#[test]
fn rust_value_position_match_and_if_run() {
    let src = r#"
        enum Dir { North, South, East, West }
        fn code(d: Dir) -> i64 {
            let n: i64 = match d {
                North => 1,
                South => 2,
                East => 3,
                West => 4,
            };
            return n;
        }
        fn main() -> i64 {
            let a: i64 = code(East);
            let b: i64 = if a > 2 { 10 } else { 20 };
            return a.wrapping_add(b);
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    // East => 3; 3 > 2 => 10; 3 + 10 = 13.
    assert_eq!(report.run, Some(Ok(Value::Int(13))));
}

/// `if let Some(v) = opt { v } else { d }` desugars to a one-arm match and works
/// in value position (binding the payload in the `then` branch).
#[test]
fn rust_if_let_runs() {
    let src = r#"
        fn find(x: i64) -> Option {
            if x > 0 { return Some(x); }
            return None;
        }
        fn main() -> i64 {
            let o: Option = find(7);
            let r: i64 = if let Some(v) = o { v } else { 0 };
            return r.wrapping_add(1);
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    // find(7) = Some(7); the `if let` binds v = 7; 7 + 1 = 8.
    assert_eq!(report.run, Some(Ok(Value::Int(8))));
}

/// Inline modules + `use` + a path-qualified call resolve in one flat namespace.
#[test]
fn rust_inline_modules_run() {
    let src = r#"
        mod geometry {
            pub struct Point { pub x: i64, pub y: i64 }
            pub fn origin() -> Point { return Point { x: 0, y: 0 }; }
        }
        use geometry::Point;
        fn main() -> i64 {
            let p: Point = geometry::origin();
            let q: Point = Point { x: 3, y: 4 };
            return q.x.wrapping_add(q.y).wrapping_add(p.x);
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(7))));
}

/// Multiple source files compiled together: a type + fn defined in one file are
/// used from another (cross-file references in a flat namespace).
#[test]
fn rust_multi_file_compiles_together() {
    let lib = r#"
        pub struct Counter { pub n: i64 }
        #[requires(start >= 0)]
        pub fn make(start: i64) -> Counter { return Counter { n: start }; }
    "#;
    let main = r#"
        fn main() -> i64 {
            let c: Counter = make(41);
            return c.n.wrapping_add(1);
        }
    "#;
    let report = run_rust_modules_pipeline(&[lib, main], Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(42))));
}

/// Tuples + arrays: construct, destructure a tuple, index an array in bounds.
#[test]
fn rust_tuples_and_arrays_run() {
    let src = r#"
        fn main() -> i64 {
          let t: (i64, i64) = (3, 4);
          let a: [i64; 3] = [10, 20, 30];
          let (x, y) = t;
          return a[1].wrapping_add(x).wrapping_add(y);
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(27)))); // 20 + 3 + 4
}

/// Soundness guard: a constant out-of-bounds array index must NOT verify.
#[test]
fn rust_out_of_bounds_index_is_not_verified() {
    let src = r#"
        fn main() -> i64 {
          let a: [i64; 3] = [10, 20, 30];
          return a[5];
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(!report.all_verified(), "a[5] on a length-3 array must not verify");
    assert!(report.obligations.iter().any(|o| o.origin.contains("out of bounds")));
}

/// A dynamic index guarded by a precondition (`0 <= i < 3`) verifies; an index
/// store (`a[0] = ..`) runs.
#[test]
fn rust_guarded_dynamic_index_verifies_and_store_runs() {
    let src = r#"
        #[requires(i >= 0)]
        #[requires(i < 3)]
        fn get(a: [i64; 3], i: i64) -> i64 { return a[i]; }
        fn main() -> i64 {
          let mut a: [i64; 3] = [1, 2, 3];
          a[0] = 100;
          return a[0];
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "guarded index must verify: {report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(100))));
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

/// Real Rust: `a.wrapping_add(b)` is the method-syntax opt-out on the `.rs` path.
#[test]
fn rust_wrapping_method_opts_out() {
    let src = r#"
        fn add(a: i64, b: i64) -> i64 { return a.wrapping_add(b); }
        fn main() -> i64 { return add(2, 3); }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert!(!report.obligations.iter().any(|o| o.origin.contains("overflow")));
    assert_eq!(report.run, Some(Ok(Value::Int(5))));
}

/// Real Rust: `panic!()` aborts the bad path; the good path runs.
#[test]
fn rust_panic_macro_runs() {
    let src = r#"
        fn checked(x: i64) -> i64 {
          if x < 0 { panic!(); }
          return x;
        }
        fn main() -> i64 { return checked(7); }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(7))));
}

/// Real Rust: `assert!(cond)` becomes a discharged obligation guarding the div.
#[test]
fn rust_assert_macro_verifies() {
    let src = r#"
        fn main() -> i64 {
          let a: i64 = 10;
          let b: i64 = 2;
          assert!(b != 0);
          return a / b;
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(5))));
}

/// Real Rust: the `?` operator propagates `Option`, end to end.
#[test]
fn rust_try_operator_runs() {
    let src = r#"
        enum Opt { None, Some(i64) }
        fn first(x: i64) -> Opt {
          if x > 0 { return Opt::Some(x); }
          return Opt::None;
        }
        fn add1(x: i64) -> Opt {
          let v: i64 = first(x)?;
          return Opt::Some(v.wrapping_add(1));
        }
        fn main() -> i64 {
          let r: Opt = add1(5);
          match r { Opt::Some(n) => { return n; } Opt::None => { return 0; } }
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(6))));
}

/// Real Rust: an `impl` block with methods (one calling another) verifies + runs.
#[test]
fn rust_impl_methods_run() {
    let src = r#"
        struct Point { x: i64, y: i64 }
        impl Point {
          fn sum(self) -> i64 { return self.x.wrapping_add(self.y); }
          fn scaled(self, k: i64) -> i64 { return self.sum().wrapping_mul(k); }
        }
        fn main() -> i64 {
          let p: Point = Point { x: 3, y: 4 };
          return p.scaled(2);
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(14))));
}

/// Real Rust: a `trait` + its `impl` lower so the trait method runs.
#[test]
fn rust_trait_impl_runs() {
    let src = r#"
        struct S { v: i64 }
        trait Get { fn get(self) -> i64; }
        impl Get for S { fn get(self) -> i64 { return self.v; } }
        fn main() -> i64 { let s: S = S { v: 9 }; return s.get(); }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(9))));
}

/// Real Rust: a `for` range loop with `+=` sums 0..5 = 10.
#[test]
fn rust_for_range_loop_runs() {
    let src = r#"
        fn main() -> i64 {
          let mut s: i64 = 0;
          for i in 0..5 { s += i; }
          return s;
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(10))));
}

/// Real Rust: `loop` with `break` and `continue` — sum 1..=10 skipping 5 = 50.
#[test]
fn rust_loop_break_continue_runs() {
    let src = r#"
        fn main() -> i64 {
          let mut s: i64 = 0;
          let mut i: i64 = 0;
          loop {
            i += 1;
            if i > 10 { break; }
            if i == 5 { continue; }
            s += i;
          }
          return s;
        }
    "#;
    let report = run_rust_pipeline(src, Some("main")).expect("front-end ok");
    assert!(report.all_verified(), "{report:?}");
    assert_eq!(report.run, Some(Ok(Value::Int(50))));
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
#[test]
fn raven_kernel_program_verifies() {
    let src = r#"
        fn dbl(n: Nat) -> Nat {
            match n {
              | Nat.zero    => Nat.zero
              | Nat.succ(k) => Nat.succ(Nat.succ(k.rec))
            }
        }
        fn dbl_two(u: Nat) -> Nat {
            ensures(result == Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))));
            dbl(Nat.succ(Nat.succ(Nat.zero)))
        }
    "#;
    let report = rv_driver::verify_raven(src, true).expect("front-end ok");
    assert!(report.all_verified(), "dbl 2 ≡ 4 should verify: {report:?}");
    assert!(report.verified.contains(&"dbl_two".to_string()));
}

/// A false spec is *not* reported as verified (soundness through the driver path).
#[test]
fn raven_kernel_false_spec_stays_open() {
    let src = r#"
        fn wrong(x: Nat) -> Nat {
            ensures(result == Nat.succ(x));
            x
        }
    "#;
    let report = rv_driver::verify_raven(src, true).expect("front-end ok");
    assert!(!report.all_verified(), "a false spec must not verify");
    assert!(report.open.contains(&"wrong".to_string()));
}

/// The kernel surface as a *compiler*, not just a verifier: a parameterless `answer`
/// is evaluated to its canonical value through the driver's run path.
#[test]
fn raven_kernel_program_runs() {
    let src = r#"
        fn dbl(n: Nat) -> Nat {
            match n { | Nat.zero => Nat.zero | Nat.succ(k) => Nat.succ(Nat.succ(k.rec)) }
        }
        fn answer() -> Nat { dbl(Nat.succ(Nat.succ(Nat.zero))) }
    "#;
    let report = rv_driver::run_raven(src, true, Some("answer")).expect("front-end ok");
    assert!(report.all_verified());
    assert_eq!(report.run.unwrap().unwrap(), "4", "dbl 2 should evaluate to 4");
}
