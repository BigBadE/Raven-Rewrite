// Core library types test - Option only (simplified)

enum Option<T> {
    None,
    Some(T),
}

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

fn main() -> i64 {
    let mut passed: i64 = 0;
    if test_option_some() { passed = passed + 1; }
    if test_option_none() { passed = passed + 1; }
    passed
}
