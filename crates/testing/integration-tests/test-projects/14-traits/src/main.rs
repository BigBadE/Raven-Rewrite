// Comprehensive trait system test
// Tests: traits, associated types, supertraits, where clauses

// Base trait with associated type
trait Container {
    type Item;
    fn get(&self) -> &Self::Item;
}

// Supertrait constraint: Display requires Container
trait Display: Container {
    fn show(&self) -> i64;
}

// Simple struct to hold a value
struct Box {
    value: i64,
}

// Implement Container for Box with associated type
impl Container for Box {
    type Item = i64;

    fn get(&self) -> &Self::Item {
        &self.value
    }
}

// Implement Display for Box (requires Container to be implemented)
impl Display for Box {
    fn show(&self) -> i64 {
        // Dereference the result from get()
        *self.get()
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
