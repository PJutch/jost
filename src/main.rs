use std::io;
use std::vec::Vec;

#[derive(Debug)]
enum Word<'a> {
    Id(&'a str),
    Int(i64),
    String(&'a str),
}

fn get_byte(s: &str, index: usize) -> Option<u8> {
    s.as_bytes().get(index).copied()
}

fn parse_token(token: &str) -> Option<Word> {
    if token.bytes().all(|c| c.is_ascii_whitespace()) {
        Option::None
    } else if token.bytes().all(|c| c.is_ascii_digit()) {
        let mut value = 0i64;
        for digit in token.bytes() {
            value *= 10;
            value += (digit - b'0') as i64
        }
        Option::Some(Word::Int(value))
    } else {
        Option::Some(Word::Id(token))
    }
}

fn lex(code: &str) -> Vec<Word> {
    let mut result = Vec::<Word>::new();

    let mut token_start = 0;
    let mut quoted = false;
    for i in 0..=code.len() {
        if get_byte(code, i).is_some_and(|c| c == b'"') {
            if quoted {
                result.push(Word::String(&code[token_start..i]));
            }
            token_start = i + 1;
            quoted = !quoted;
        } else if !quoted && get_byte(code, i).is_none_or(|c| c.is_ascii_whitespace()) {
            if let Option::Some(token) = parse_token(&code[token_start..i]) {
                result.push(token);
            }
            token_start = i + 1;
        }
    }
    result
}

#[derive(Debug)]
enum Value {
    Int(i64),
    String(String),
}

impl Value {
    fn expect_int(self) -> Result<i64, String> {
        if let Value::Int(value) = self {
            Result::Ok(value)
        } else {
            Result::Err(format!("{self:?} not an integer"))
        }
    }
}

fn pop_int(stack: &mut Vec<Value>) -> Result<i64, String> {
    stack.pop().ok_or("Stack underflow")?.expect_int()
}

fn run(word: Word, stack: &mut Vec<Value>) -> Result<(), String> {
    match word {
        Word::Int(value) => {
            stack.push(Value::Int(value));
        }
        Word::String(value) => {
            stack.push(Value::String(value.into()));
        }
        Word::Id("+") => {
            let b = pop_int(stack)?;
            let a = pop_int(stack)?;
            stack.push(Value::Int(a + b));
        }
        Word::Id("-") => {
            let b = pop_int(stack)?;
            let a = pop_int(stack)?;
            stack.push(Value::Int(a - b));
        }
        Word::Id("*") => {
            let b = pop_int(stack)?;
            let a = pop_int(stack)?;
            stack.push(Value::Int(a * b));
        }
        Word::Id("/") => {
            let b = pop_int(stack)?;
            let a = pop_int(stack)?;
            stack.push(Value::Int(a / b));
        }
        Word::Id("%") => {
            let b = pop_int(stack)?;
            let a = pop_int(stack)?;
            stack.push(Value::Int(a % b));
        }
        Word::Id(id) => {
            return Result::Err(format!("Unknown word {id}"));
        }
    }
    Ok(())
}

fn main() {
    let stdin = io::stdin();
    let mut stack = Vec::<Value>::new();
    for line in stdin.lines() {
        let line = line.unwrap();
        for word in lex(&line) {
            if let Err(message) = run(word, &mut stack) {
                println!("{message}");
            } else {
                println!("{stack:?}");
            }
        }
    }
}
