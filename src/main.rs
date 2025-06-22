use core::{net, str};
use std::env;
use std::error::Error;
use std::fmt::{format, Display};
use std::fs::{write, File, OpenOptions};
use std::io::{self, Read, Stderr, Write};
use std::os::windows::io::FromRawHandle;
use std::process::{Command, Output, Stdio};
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

    fn push_var(&mut self, var: i64) {
        self.stack.push(var);
    }

    fn pop_var(&mut self) -> Option<i64> {
        self.stack.pop()
    }

    fn new_var(&mut self) -> i64 {
        self.last_var += 1;
        self.stack.push(self.last_var);
        self.last_var
    }
}

fn compile_bin_op(binop: &str, vars: &mut Variables) -> Result<String, String> {
    let a = vars.pop_var().ok_or("Stack underflow")?;
    let b = vars.pop_var().ok_or("Stack underflow")?;
    let result = vars.new_var();
    Result::Ok(format!("%{result} = %{a} {binop} %{b}"))
}

fn compile_word(word: Word, vars: &mut Variables) -> Result<String, String> {
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
        Word::Id("dup") => {
            let var: i64 = vars.pop_var().ok_or("Stack underflow")?;
            vars.push_var(var);
            vars.push_var(var);
            Result::Ok("".to_owned())
        }
        Word::Id("pop") => {
            vars.pop_var().ok_or("Stack underflow")?;
            Result::Ok("".to_owned())
        }
        Word::Id("swp") => {
            let a = vars.pop_var().ok_or("Stack underflow")?;
            let b = vars.pop_var().ok_or("Stack underflow")?;
            vars.push_var(b);
            vars.push_var(a);
            Result::Ok("".to_owned())
        }
        Word::Id(id) => Err(format!("Unknown word {}", id)),
    }
}

fn compile_to_ir(code: &str) -> Result<String, String> {
    let mut ir = String::new();
    let mut vars = Variables::new();
    for word in lex(code) {
        ir += compile_word(word, &mut vars)?.as_str();
        ir += "\n";
    }
    Result::Ok(ir)
}

fn run_stage(program: &str, input_file: &str, output_file: &str) -> Result<(), Box<dyn Error>> {
    if Command::new(program)
        .arg("-o")
        .arg(output_file)
        .arg(input_file)
        .status()?
        .success()
    {
        Result::Ok(())
    } else {
        Result::Err(Box::from(format!("{program} failed")))
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Flag {
    None,
    OutputFile,
}

fn change_extension(path: &str, old_extension: &str, new_extension: &str) -> String {
    path.trim_end_matches(old_extension).to_owned() + new_extension
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut input_file = Option::<String>::None;
    let mut output_file = Option::<String>::None;

    let mut current_flag = Flag::None;
    for arg in env::args().skip(1) {
        match arg.as_str() {
            "-o" => {
                current_flag = Flag::OutputFile;
            }
            flag if flag.starts_with('-') => {
                return Result::Err(Box::from(format!("flag {} is unknown", flag)))
            }
            arg => match current_flag {
                Flag::None => {
                    if input_file.is_none() {
                        input_file = Option::Some(arg.to_owned());
                    } else {
                        return Result::Err(Box::from("multiple input files provided"));
                    }
                }
                Flag::OutputFile => {
                    current_flag = Flag::None;
                    if output_file.is_none() {
                        output_file = Option::Some(arg.to_owned());
                    } else {
                        return Result::Err(Box::from("multiple input files provided"));
                    }
                }
            },
        }
    }

    if current_flag == Flag::OutputFile {
        return Result::Err(Box::from("-o expects an output file as an argument"));
    }

    let extension = ".jost";
    let input_file = input_file.ok_or("no input files provided")?;
    let ir_file = change_extension(input_file.as_str(), extension, ".ll");
    let bc_file = change_extension(input_file.as_str(), extension, ".bc");
    let asm_file = change_extension(input_file.as_str(), extension, ".s");
    let output_file = change_extension(input_file.as_str(), extension, ".exe");

    println!(
        "{} => {} => {} => {} => {}",
        input_file, ir_file, bc_file, asm_file, output_file
    );

    let mut code = String::new();
    OpenOptions::new()
        .read(true)
        .open(input_file)?
        .read_to_string(&mut code)?;

    OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&ir_file)?
        .write_all(compile_to_ir(code.as_str())?.as_bytes())
        .expect("write to {bc_file} should succeed");

    run_stage("llvm-as", ir_file.as_str(), &bc_file)?;
    run_stage("llc", &bc_file, &asm_file)?;
    run_stage("clang", &asm_file, output_file.as_str())?;

    Result::Ok(())
}
