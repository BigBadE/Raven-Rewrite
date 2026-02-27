trait Container {
    fn get(&self) -> i64;
    fn size(&self) -> i64;
}

struct Box {
    value: i64,
}

impl Container for Box {
    fn get(&self) -> i64 {
        self.value
    }

    fn size(&self) -> i64 {
        1
    }
}

struct Pair {
    a: i64,
    b: i64,
}

impl Container for Pair {
    fn get(&self) -> i64 {
        self.a + self.b
    }

    fn size(&self) -> i64 {
        2
    }
}

fn extract<T: Container>(c: &T) -> i64 {
    c.get() + c.size()
}

fn main() -> i64 {
    let b = Box { value: 40 };
    let p = Pair { a: 10, b: 20 };
    extract(&b) + extract(&p)
}
