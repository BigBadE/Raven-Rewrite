// Genuine Rust syntax, parsed by tree-sitter-rust and verified+run by raven.
//   rvc examples/real.rs --run   →  VERIFIED, main() = Int(5)
#[requires(y != 0)]
fn div(x: i64, y: i64) -> i64 {
    return x / y;
}

fn main() -> i64 {
    let a: i64 = 10;
    let b: i64 = 2;
    return div(a, b);
}
