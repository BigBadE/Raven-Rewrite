// Test: Blanket implementations
// impl<T: Describable> Summary for T — when a type implements Describable,
// it automatically gets the Summary implementation.

trait Describable {
    fn describe(&self) -> i64;
}

trait Summary {
    fn summarize(&self) -> i64;
}

impl<T: Describable> Summary for T {
    fn summarize(&self) -> i64 {
        self.describe() + 1000
    }
}

struct Item {
    val: i64,
}

impl Describable for Item {
    fn describe(&self) -> i64 {
        self.val
    }
}

fn main() -> i64 {
    let item = Item { val: 5 };
    item.summarize()
}

// Test that blanket impl provides the method
#[test]
fn test_blanket_impl() -> bool {
    let item = Item { val: 5 };
    let result = item.summarize();
    if result == 1005 { true } else { false }
}

// Test that the concrete trait method still works
#[test]
fn test_concrete_trait() -> bool {
    let item = Item { val: 42 };
    let result = item.describe();
    if result == 42 { true } else { false }
}
