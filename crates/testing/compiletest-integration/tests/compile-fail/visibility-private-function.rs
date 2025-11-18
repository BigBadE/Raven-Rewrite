mod inner {
    fn private_fn() -> i64 { 42 }
}

fn main() -> i64 {
    inner::private_fn() // Error: private function
}
