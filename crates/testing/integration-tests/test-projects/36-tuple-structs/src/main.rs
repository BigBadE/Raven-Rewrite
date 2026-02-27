// Test tuple struct definitions and operations

// Simple single-field wrapper (newtype pattern)
struct Wrapper(i64);

// Multi-field tuple struct
struct Point(i64, i64);

// Nested tuple struct
struct Pair(i64, i64);

fn test_newtype() -> i64 {
    // Construction
    let w = Wrapper(42);
    // Field access
    w.0
}

fn test_multi_field() -> i64 {
    // Construction
    let p = Point(10, 20);
    // Field access
    p.0 + p.1
}

fn test_pattern_match() -> i64 {
    let w = Wrapper(100);
    // Tuple struct pattern in match
    match w {
        Wrapper(x) => x,
    }
}

fn test_pattern_let() -> i64 {
    let p = Point(3, 4);
    // Tuple struct pattern in let binding
    let Point(x, y) = p;
    x + y
}

fn main() -> i64 {
    let a = test_newtype();      // 42
    let b = test_multi_field();  // 30
    let c = test_pattern_match(); // 100
    let d = test_pattern_let();  // 7

    // Total: 42 + 30 + 100 + 7 = 179
    a + b + c + d
}
