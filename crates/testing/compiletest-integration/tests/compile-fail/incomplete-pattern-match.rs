enum Option {
    Some(i64),
    None,
}

fn main() -> i64 {
    let x = Option::Some(42);
    match x {
        Option::Some(v) => v,
        // Error: non-exhaustive patterns, missing None
    }
}
