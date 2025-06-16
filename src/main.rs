use core::net;
use std::fmt::{format, Display};
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

struct Variables {
    last_var: i64,
    stack: Vec<i64>,
}

impl Variables {
    fn new() -> Self {
        Self {
            last_var: 0,
            stack: Vec::new(),
        }
    }

    fn new_var(&mut self) -> i64 {
        self.last_var += 1;
        self.stack.push(self.last_var);
        self.last_var
    }

    fn pop_var(&mut self) -> Option<i64> {
        self.stack.pop()
    }
}

fn compile_bin_op(binop: &str, vars: &mut Variables) -> Result<String, String> {
    let a = vars.pop_var().ok_or("Stack underflow")?;
    let b = vars.pop_var().ok_or("Stack underflow")?;
    let result = vars.new_var();
    Result::Ok(format!("%{result} = %{a} {binop} %{b}"))
}

fn compile(word: Word, vars: &mut Variables) -> Result<String, String> {
    match word {
        Word::Int(value) => {
            let var = vars.new_var();
            Result::Ok(format!("%{var} = {value}"))
        }
        Word::String(value) => {
            let var: i64 = vars.new_var();
            Result::Ok(format!("%{var} = \"{value}\""))
        }
        Word::Id("+") => compile_bin_op("+", vars),
        Word::Id("-") => compile_bin_op("-", vars),
        Word::Id("*") => compile_bin_op("*", vars),
        Word::Id("/") => compile_bin_op("/", vars),
        Word::Id("%") => compile_bin_op("%", vars),
        Word::Id(id) => Err(format!("Unknown word {}", id)),
    }
}

fn main() {
    let stdin = io::stdin();
    let mut vars = Variables::new();
    for line in stdin.lines() {
        let line = line.unwrap();
        for word in lex(&line) {
            match compile(word, &mut vars) {
                Ok(output) => println!("{output}"),
                Err(message) => println!("{message}"),
            }
        }
    }
}
