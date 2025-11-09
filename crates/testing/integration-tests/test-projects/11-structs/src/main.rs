// Simple struct with two integer fields
struct Point {
    x: i32,
    y: i32,
}

fn test_struct_creation() -> i32 {
    // Create a Point instance
    let p = Point { x: 10, y: 20 };

    // Access fields and return their sum
    p.x + p.y
}

fn main() -> i32 {
    let result = test_struct_creation();

    // Should return 30 (10 + 20)
    if result == 30 {
        1
    } else {
        0
    }
}
