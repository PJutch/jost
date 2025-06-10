use std::io;
use std::vec::Vec;

#[derive(Debug)]
enum Value {
    Int(i64)
}

fn main() {
    let stdin = io::stdin();
    let mut stack = Vec::<Value>::new();
    for line in stdin.lines() {
        let line = line.unwrap();
        if let Ok(number) = line.parse::<i64>() {
            stack.push(Value::Int(number));
            println!("{stack:?}");
        } else {
            println!("Unknown word");
        }
    }
}
