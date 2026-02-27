fn main() -> i64 {
    let arr = [10, 20, 30];
    arr[1]
}

#[test]
fn test_array_first_element() -> bool {
    let arr = [100, 200, 300];
    if arr[0] == 100 { true } else { false }
}

#[test]
fn test_array_last_element() -> bool {
    let arr = [5, 10, 15, 20];
    if arr[3] == 20 { true } else { false }
}

#[test]
fn test_array_element_arithmetic() -> bool {
    let arr = [3, 7, 11];
    let sum = arr[0] + arr[1] + arr[2];
    if sum == 21 { true } else { false }
}
