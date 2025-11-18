trait Container {
    type Item;
    fn get(&self) -> Self::Item;
}

struct IntBox {
    value: i64,
}

impl Container for IntBox {
    // Error: missing associated type Item implementation
    fn get(&self) -> Self::Item {
        self.value
    }
}

fn main() -> i64 {
    let box_val = IntBox { value: 42 };
    box_val.get()
}
