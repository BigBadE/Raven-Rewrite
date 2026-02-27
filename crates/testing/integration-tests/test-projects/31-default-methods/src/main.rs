// Test: Default method implementations in traits
// A trait method with a body serves as the default when an impl doesn't override it.

trait Greetable {
    fn name(&self) -> i64;
    fn greeting(&self) -> i64 {
        self.name() + 100
    }
}

struct Person {
    id: i64,
}

impl Greetable for Person {
    fn name(&self) -> i64 {
        self.id
    }
    // greeting() uses the default implementation
}

fn main() -> i64 {
    let p = Person { id: 42 };
    p.greeting()
}

// Test that default method dispatches through self correctly
#[test]
fn test_default_method() -> bool {
    let p = Person { id: 42 };
    let result = p.greeting();
    if result == 142 { true } else { false }
}

// Test that the required method works directly
#[test]
fn test_required_method() -> bool {
    let p = Person { id: 7 };
    let result = p.name();
    if result == 7 { true } else { false }
}
