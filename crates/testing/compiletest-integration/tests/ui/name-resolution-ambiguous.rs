fn foo() -> i64 { 1 }
fn foo() -> i64 { 2 } //~ ERROR duplicate definition

fn main() -> i64 {
    foo()
}
