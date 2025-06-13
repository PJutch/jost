use std::error::Error;
use std::vec::Vec;
use std::{error, i64, io};

#[derive(Debug)]
enum Word<'a> {
    Id(&'a str),
    Int(i64),
    String(&'a str),
}

fn is_space(char: u8) -> bool {
    char == ' ' as u8 || char == '\n' as u8 || char == '\t' as u8 || char == '\r' as u8
}

fn is_digit(char: u8) -> bool {
    '0' as u8 <= char && char <= '9' as u8
}

fn parse_token(token: &str) -> Option<Word> {
    if token.bytes().all(is_space) {
        Option::None
    } else if token.bytes().all(is_digit) {
        let mut value = 0i64;
        for digit in token.bytes() {
            value *= 10;
            value += (digit - '0' as u8) as i64
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
        if code.bytes().nth(i).is_some_and(|c| c == '"' as u8) {
            if quoted {
                result.push(Word::String(&code[token_start..i]));
            }
            token_start = i + 1;
            quoted = !quoted;
        } else if !quoted && code.bytes().nth(i).is_none_or(is_space) {
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
    fn expect_int(self: Self) -> Result<i64, String> {
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
