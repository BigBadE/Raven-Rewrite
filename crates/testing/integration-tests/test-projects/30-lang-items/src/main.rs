// Test: Lang item attribute dispatch
// The trait is named "MyAdd" (NOT "Add"), but marked with #[lang = "add"].
// The + operator should dispatch through the lang item registry, not by name.
#[lang = "add"]
trait MyAdd {
    fn add(&self, other: &Self) -> Self;
}

struct Wrapper {
    val: i64,
}

impl MyAdd for Wrapper {
    fn add(&self, other: &Wrapper) -> Wrapper {
        Wrapper {
            val: self.val + other.val,
        }
    }
}

fn main() -> i64 {
    0
}

// Test that #[lang = "add"] makes + dispatch through the lang item registry
// even though the trait is not named "Add"
#[test]
fn test_lang_item_add() -> bool {
    let a = Wrapper { val: 30 };
    let b = Wrapper { val: 12 };
    let c = a + b;
    if c.val == 42 { true } else { false }
}

// Test that primitives are implicitly Copy (can be used after assignment)
#[test]
fn test_primitive_copy() -> bool {
    let v: i64 = 42;
    let a: i64 = v;
    let b: i64 = v;
    if a + b == 84 { true } else { false }
}

// Test that booleans are implicitly Copy
#[test]
fn test_bool_copy() -> bool {
    let flag: bool = true;
    let p: bool = flag;
    let q: bool = flag;
    if p { q } else { false }
}
