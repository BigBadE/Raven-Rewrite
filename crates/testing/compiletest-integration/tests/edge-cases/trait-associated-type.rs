trait Container {
    type Item;
    fn get(&self) -> Self::Item;
}

struct IntBox {
    value: i64,
}

impl Container for IntBox {
    type Item = i64;

    fn get(&self) -> i64 {
        self.value
    }
}

fn main() -> i64 {
    let box_val = IntBox { value: 42 };
    box_val.get()
}
