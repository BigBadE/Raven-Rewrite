fn dangling() -> &i64 {
    let x = 42;
    &x //~ ERROR value does not live long enough
}

fn main() -> i64 {
    *dangling()
}
