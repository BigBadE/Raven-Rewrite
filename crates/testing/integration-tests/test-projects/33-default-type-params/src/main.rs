// Test: Default type parameters on traits
// trait MyAdd<Rhs = Self> — when Rhs is not specified, it defaults to Self.

trait MyAdd<Rhs = Self> {
    fn my_add(&self, rhs: &Rhs) -> i64;
}

struct Num {
    val: i64,
}

impl MyAdd for Num {
    fn my_add(&self, rhs: &Num) -> i64 {
        self.val + rhs.val
    }
}

fn main() -> i64 {
    let a = Num { val: 10 };
    let b = Num { val: 20 };
    a.my_add(&b)
}

// Test that default type parameter works (Rhs defaults to Self = Num)
#[test]
fn test_default_type_param() -> bool {
    let a = Num { val: 10 };
    let b = Num { val: 20 };
    let result = a.my_add(&b);
    if result == 30 { true } else { false }
}
