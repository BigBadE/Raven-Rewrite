type Int = i64;
type Boolean = bool;

fn add_ints(a: Int, b: Int) -> Int {
    a + b
}

fn main() -> i64 {
    let x: Int = 10;
    let y: Int = 20;
    add_ints(x, y)
}

#[test]
fn test_simple_alias() -> bool {
    let x: Int = 42;
    if x == 42 { true } else { false }
}

#[test]
fn test_alias_in_function_sig() -> bool {
    let result: Int = add_ints(10, 20);
    if result == 30 { true } else { false }
}

#[test]
fn test_bool_alias() -> bool {
    let flag: Boolean = true;
    flag
}
