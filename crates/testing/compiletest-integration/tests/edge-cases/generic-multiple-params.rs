fn combine<T, U>(x: T, y: U) -> T {
    x
}

fn main() -> i64 {
    combine(42, "ignored")
}
