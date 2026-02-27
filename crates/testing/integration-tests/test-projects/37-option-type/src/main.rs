// Generic enum
enum Option<T> {
    None,
    Some(T),
}

// Non-generic function taking generic enum - should be monomorphized
fn get_or_default(opt: Option<i64>, default: i64) -> i64 {
    match opt {
        Option::Some(v) => v,
        Option::None => default,
    }
}

fn test_option_some() -> bool {
    let s = Option::Some(42);
    get_or_default(s, 0) == 42
}

fn test_option_none() -> bool {
    let n = Option::None;
    get_or_default(n, 99) == 99
}

fn main() -> i64 {
    let s = Option::Some(42);
    get_or_default(s, 0)
}
