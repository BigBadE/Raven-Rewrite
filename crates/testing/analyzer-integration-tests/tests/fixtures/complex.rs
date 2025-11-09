fn complex_function(a: i32, b: i32, c: i32, d: i32, e: i32, f: i32) -> i32 {
    if a > 0 {
        if b > 0 {
            if c > 0 {
                if d > 0 {
                    if e > 0 {
                        return f;
                    }
                }
            }
        }
    }

    if a < 0 {
        return -1;
    } else if b < 0 {
        return -2;
    } else if c < 0 {
        return -3;
    } else if d < 0 {
        return -4;
    } else if e < 0 {
        return -5;
    }

    0
}

fn high_cognitive(x: i32) -> i32 {
    let mut result = 0;

    for i in 0..10 {
        if i % 2 == 0 {
            for j in 0..5 {
                if j > 2 {
                    result += 1;
                }
            }
        }
    }

    result
}
