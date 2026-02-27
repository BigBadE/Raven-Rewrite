fn main() -> i64 {
    42
}

#[test]
fn test_for_sum() -> bool {
    let mut sum: i64 = 0;
    for i in 0..5 {
        sum = sum + i;
    }
    if sum == 10 { true } else { false }
}

#[test]
fn test_for_product() -> bool {
    let mut product: i64 = 1;
    for i in 1..6 {
        product = product * i;
    }
    if product == 120 { true } else { false }
}

#[test]
fn test_for_count() -> bool {
    let mut count: i64 = 0;
    for _i in 0..10 {
        count = count + 1;
    }
    if count == 10 { true } else { false }
}
