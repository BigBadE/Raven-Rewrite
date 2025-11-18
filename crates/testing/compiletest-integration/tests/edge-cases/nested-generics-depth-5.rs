fn level1<T>(x: T) -> T { x }
fn level2<T>(x: T) -> T { level1(x) }
fn level3<T>(x: T) -> T { level2(x) }
fn level4<T>(x: T) -> T { level3(x) }
fn level5<T>(x: T) -> T { level4(x) }

fn main() -> i64 {
    level5(42)
}
