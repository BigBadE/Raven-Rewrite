fn classify(x: i64, y: i64) -> i64 {
    match (x, y) {
        (0, 0) => 0,
        (0, _) | (_, 0) => 1,
        (1, 1) | (2, 2) | (3, 3) => 2,
        _ => 3,
    }
}

fn main() -> i64 {
    classify(0, 5)
}
