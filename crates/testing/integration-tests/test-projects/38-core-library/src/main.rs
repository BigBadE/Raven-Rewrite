// Core library prelude types test
//
// These types come from the real Rust core library prelude!
// Only Option and Result are in the prelude (core::prelude::v1).

// ===== Option Tests =====
// Option is in prelude: `pub use crate::option::Option::{self, None, Some};`

fn test_option_some() -> bool {
    let x: Option<i64> = Option::Some(42);
    match x {
        Option::Some(v) => v == 42,
        Option::None => false,
    }
}

fn test_option_none() -> bool {
    let x: Option<i64> = Option::None;
    match x {
        Option::Some(_) => false,
        Option::None => true,
    }
}

fn test_option_bool() -> bool {
    let x: Option<bool> = Option::Some(true);
    match x {
        Option::Some(v) => v,
        Option::None => false,
    }
}

fn test_option_zero() -> bool {
    let x: Option<i64> = Option::Some(0);
    match x {
        Option::Some(v) => v == 0,
        Option::None => false,
    }
}

// Nested Option test
fn test_option_nested() -> bool {
    let x: Option<Option<i64>> = Option::Some(Option::Some(99));
    match x {
        Option::Some(inner) => {
            match inner {
                Option::Some(v) => v == 99,
                Option::None => false,
            }
        }
        Option::None => false,
    }
}

// Option with negative values
fn test_option_negative() -> bool {
    let x: Option<i64> = Option::Some(-100);
    match x {
        Option::Some(v) => v == -100,
        Option::None => false,
    }
}

// ===== Result Tests =====
// Result is in prelude: `pub use crate::result::Result::{self, Err, Ok};`

fn test_result_ok() -> bool {
    let x: Result<i64, i64> = Result::Ok(42);
    match x {
        Result::Ok(v) => v == 42,
        Result::Err(_) => false,
    }
}

fn test_result_err() -> bool {
    let x: Result<i64, i64> = Result::Err(404);
    match x {
        Result::Ok(_) => false,
        Result::Err(e) => e == 404,
    }
}

fn test_result_different_types() -> bool {
    let x: Result<i64, bool> = Result::Err(true);
    match x {
        Result::Ok(_) => false,
        Result::Err(e) => e,
    }
}

fn test_result_zero() -> bool {
    let x: Result<i64, i64> = Result::Ok(0);
    match x {
        Result::Ok(v) => v == 0,
        Result::Err(_) => false,
    }
}

// Nested Result test
fn test_result_nested() -> bool {
    let x: Result<Result<i64, i64>, i64> = Result::Ok(Result::Ok(123));
    match x {
        Result::Ok(inner) => {
            match inner {
                Result::Ok(v) => v == 123,
                Result::Err(_) => false,
            }
        }
        Result::Err(_) => false,
    }
}

// Result with negative error
fn test_result_negative_err() -> bool {
    let x: Result<i64, i64> = Result::Err(-999);
    match x {
        Result::Ok(_) => false,
        Result::Err(e) => e == -999,
    }
}

// ===== Mixed Option and Result Tests =====

fn test_option_of_result() -> bool {
    let x: Option<Result<i64, i64>> = Option::Some(Result::Ok(77));
    match x {
        Option::Some(r) => {
            match r {
                Result::Ok(v) => v == 77,
                Result::Err(_) => false,
            }
        }
        Option::None => false,
    }
}

fn test_result_of_option() -> bool {
    let x: Result<Option<i64>, i64> = Result::Ok(Option::Some(88));
    match x {
        Result::Ok(opt) => {
            match opt {
                Option::Some(v) => v == 88,
                Option::None => false,
            }
        }
        Result::Err(_) => false,
    }
}

// ===== Generic Function with Option =====
// Single generic param works

fn identity_option<T>(x: Option<T>) -> Option<T> {
    x
}

fn test_generic_option_identity() -> bool {
    let x: Option<i64> = Option::Some(55);
    let y = identity_option(x);
    match y {
        Option::Some(v) => v == 55,
        Option::None => false,
    }
}

// ===== Pattern Matching with Multiple Arms =====

fn test_option_multiple_values() -> bool {
    let a: Option<i64> = Option::Some(1);
    let b: Option<i64> = Option::Some(2);
    let c: Option<i64> = Option::None;

    let sum = match a {
        Option::Some(v) => v,
        Option::None => 0,
    } + match b {
        Option::Some(v) => v,
        Option::None => 0,
    } + match c {
        Option::Some(v) => v,
        Option::None => 0,
    };

    sum == 3
}

fn test_result_chain() -> bool {
    let r1: Result<i64, i64> = Result::Ok(10);
    let r2: Result<i64, i64> = Result::Ok(20);
    let r3: Result<i64, i64> = Result::Err(0);

    let val1 = match r1 {
        Result::Ok(v) => v,
        Result::Err(_) => 0,
    };
    let val2 = match r2 {
        Result::Ok(v) => v,
        Result::Err(_) => 0,
    };
    let val3 = match r3 {
        Result::Ok(v) => v,
        Result::Err(_) => 0,
    };

    val1 + val2 + val3 == 30
}

// ===== Deeply Nested Types =====

fn test_triple_nested_option() -> bool {
    let x: Option<Option<Option<i64>>> = Option::Some(Option::Some(Option::Some(42)));
    match x {
        Option::Some(a) => {
            match a {
                Option::Some(b) => {
                    match b {
                        Option::Some(v) => v == 42,
                        Option::None => false,
                    }
                }
                Option::None => false,
            }
        }
        Option::None => false,
    }
}

fn main() -> i64 {
    let mut passed: i64 = 0;

    // Basic Option tests (6)
    if test_option_some() { passed = passed + 1; }
    if test_option_none() { passed = passed + 1; }
    if test_option_bool() { passed = passed + 1; }
    if test_option_zero() { passed = passed + 1; }
    if test_option_nested() { passed = passed + 1; }
    if test_option_negative() { passed = passed + 1; }

    // Basic Result tests (6)
    if test_result_ok() { passed = passed + 1; }
    if test_result_err() { passed = passed + 1; }
    if test_result_different_types() { passed = passed + 1; }
    if test_result_zero() { passed = passed + 1; }
    if test_result_nested() { passed = passed + 1; }
    if test_result_negative_err() { passed = passed + 1; }

    // Mixed tests (2)
    if test_option_of_result() { passed = passed + 1; }
    if test_result_of_option() { passed = passed + 1; }

    // Generic function test (1)
    if test_generic_option_identity() { passed = passed + 1; }

    // Multiple value tests (2)
    if test_option_multiple_values() { passed = passed + 1; }
    if test_result_chain() { passed = passed + 1; }

    // Deep nesting test (1)
    if test_triple_nested_option() { passed = passed + 1; }

    // Should return 18
    passed
}
