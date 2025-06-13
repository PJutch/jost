use std::io;
use std::vec::Vec;

#[derive(Debug)]
enum Token<'a> {
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

fn parse_token(token: &str) -> Option<Token> {
    if token.bytes().all(is_space) {
        Option::None
    } else if token.bytes().all(is_digit) {
        let mut value = 0i64;
        for digit in token.bytes() {
            value *= 10;
            value += (digit - '0' as u8) as i64
        }
        Option::Some(Token::Int(value))
    } else {
        Option::Some(Token::Id(token))
    }
}

fn lex(code: &str) -> Vec<Token> {
    let mut result = Vec::<Token>::new();

    let mut token_start = 0;
    let mut quoted = false;
    for i in 0..=code.len() {
        if code.bytes().nth(i).is_some_and(|c| c == '"' as u8) {
            if quoted {
                result.push(Token::String(&code[token_start..i]));
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

fn main() {
    let stdin = io::stdin();
    let mut stack = Vec::<Value>::new();
    for line in stdin.lines() {
        let line = line.unwrap();
        println!("{:?}", lex(&line));

        if let Ok(number) = line.parse::<i64>() {
            stack.push(Value::Int(number));
            println!("{stack:?}");
        } else {
            println!("Unknown word");
        }
    }
}
