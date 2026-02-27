mod utils;

fn main() -> i64 {
    utils::get_value()
}

#[test]
fn test_cross_module_call() -> bool {
    if utils::get_value() == 42 {
        true
    } else {
        false
    }
}

#[test]
fn test_cross_module_add() -> bool {
    if utils::add(10, 20) == 30 {
        true
    } else {
        false
    }
}
