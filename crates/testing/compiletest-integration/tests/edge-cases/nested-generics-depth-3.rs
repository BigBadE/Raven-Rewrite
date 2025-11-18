fn wrap1<T>(x: T) -> T { x }
fn wrap2<T>(x: T) -> T { wrap1(x) }
fn wrap3<T>(x: T) -> T { wrap2(x) }

fn main() -> i64 {
    wrap3(42)
}
