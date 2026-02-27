// Test: trait bounds on generic parameters
// Verifies that <T: Trait> syntax is parsed correctly

trait Summable {
    fn sum(&self) -> i64;
}

struct Pair {
    a: i64,
    b: i64,
}

impl Summable for Pair {
    fn sum(&self) -> i64 {
        self.a + self.b
    }
}

fn get_sum<T: Summable>(item: &T) -> i64 {
    item.sum()
}

fn main() -> i64 {
    let p = Pair { a: 20, b: 22 };
    let result = get_sum(&p);
    if result == 42 { 42 } else { 0 }
}

#[test]
fn test_bounded_generic_call() -> bool {
    let p = Pair { a: 15, b: 27 };
    let result = get_sum(&p);
    if result == 42 { true } else { false }
}

#[test]
fn test_bounded_generic_different_values() -> bool {
    let p = Pair { a: 100, b: 200 };
    let result = get_sum(&p);
    if result == 300 { true } else { false }
}
