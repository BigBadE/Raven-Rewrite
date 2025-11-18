fn take_ownership(x: i64) -> i64 { x }

fn main() -> i64 {
    let x = 42;
    let y = take_ownership(x);
    x //~ ERROR use of moved value
}
