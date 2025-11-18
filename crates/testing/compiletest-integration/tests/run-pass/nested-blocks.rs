fn main() -> i64 {
    let x = {
        let y = {
            let z = 10;
            z + 5
        };
        y + 27
    };
    x
}
