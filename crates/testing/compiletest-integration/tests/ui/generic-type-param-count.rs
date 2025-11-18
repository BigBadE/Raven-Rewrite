fn identity<T>(x: T) -> T {
    x
}

fn main() -> i64 {
    identity::<i64, i64>(42) //~ ERROR wrong number of type parameters
}
