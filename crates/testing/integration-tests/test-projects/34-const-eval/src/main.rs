const X: i64 = 42;
const Y: i64 = X + 8;
const Z: i64 = 2 * 3 + 4;
const FLAG: bool = true;

static S: i64 = 100;

fn main() -> i64 {
    X
}

#[test]
fn test_basic_const() -> bool {
    if X == 42 { true } else { false }
}

#[test]
fn test_const_referencing_const() -> bool {
    if Y == 50 { true } else { false }
}

#[test]
fn test_const_arithmetic() -> bool {
    if Z == 10 { true } else { false }
}

#[test]
fn test_bool_const() -> bool {
    FLAG
}

#[test]
fn test_static_read() -> bool {
    if S == 100 { true } else { false }
}

#[test]
fn test_const_in_expression() -> bool {
    let result: i64 = X + Y;
    if result == 92 { true } else { false }
}
