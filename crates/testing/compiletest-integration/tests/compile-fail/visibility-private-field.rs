mod inner {
    pub struct Data {
        private_field: i64,
    }

    pub fn new() -> Data {
        Data { private_field: 42 }
    }
}

fn main() -> i64 {
    let d = inner::new();
    d.private_field // Error: private field
}
