fn classify(x: i64) -> i64 {
    match x {
        0 => 0,
        1..=10 => 1,
        _ => 2,
    }
}

fn main() -> i64 {
    classify(5)
}
