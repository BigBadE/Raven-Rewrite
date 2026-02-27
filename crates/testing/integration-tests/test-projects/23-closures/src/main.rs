fn main() -> i64 {
    42
}

#[test]
fn test_basic_closure() -> bool {
    let add_one = |x: i64| x + 1;
    let result: i64 = add_one(5);
    if result == 6 { true } else { false }
}

#[test]
fn test_closure_with_capture() -> bool {
    let offset: i64 = 10;
    let add_offset = |x: i64| x + offset;
    let result: i64 = add_offset(5);
    if result == 15 { true } else { false }
}
