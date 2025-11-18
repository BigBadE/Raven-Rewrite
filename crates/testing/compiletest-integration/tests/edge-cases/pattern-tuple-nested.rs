fn extract(pair: (i64, (i64, i64))) -> i64 {
    match pair {
        (x, (y, z)) => x + y + z,
    }
}

fn main() -> i64 {
    extract((10, (20, 12)))
}
