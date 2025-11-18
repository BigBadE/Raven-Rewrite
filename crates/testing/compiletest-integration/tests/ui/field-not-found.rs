struct Counter {
    value: i64,
}

fn main() -> i64 {
    let c = Counter { value: 42 };
    c.undefined_field //~ ERROR field not found
}
