// Comprehensive trait system test
// Tests: traits, supertraits, where clauses

// Base trait
trait Container {
    fn get(&self) -> i64;
}

// Supertrait constraint: Display requires Container
trait Display: Container {
    fn show(&self) -> i64;
}

// Simple struct to hold a value
struct Box {
    value: i64,
}

// Implement Container for Box
impl Container for Box {
    fn get(&self) -> i64 {
        self.value
    }
}

// Implement Display for Box (requires Container to be implemented)
impl Display for Box {
    fn show(&self) -> i64 {
        self.get()
    }
}

// Inherent impl for Box
impl Box {
    fn new(v: i64) -> Box {
        Box { value: v }
    }
}

// Generic function with where clause
fn process<T>(item: &T) -> i64
where
    T: Display,
{
    item.show()
}

fn main() -> i64 {
    let b = Box::new(42);

    // Test trait method
    let result = b.show();

    // Test generic with where clause
    let generic_result = process(&b);

    // Both should be 42
    if result == 42 && generic_result == 42 {
        42
    } else {
        0
    }
}
