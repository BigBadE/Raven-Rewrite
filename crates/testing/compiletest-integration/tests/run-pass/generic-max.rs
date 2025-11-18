fn max<T>(a: T, b: T) -> T {
    if a > b {
        a
    } else {
        b
    }
}

fn main() -> i64 {
    max(10, 42)
}
