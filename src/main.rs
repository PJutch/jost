use core::str;
use std::collections::HashMap;
use std::env;
use std::error::Error;
use std::fmt::Display;
use std::fs;
use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::process::Command;
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

#[derive(PartialEq, Eq)]
enum Type {
    Int,
    String,
}

#[derive(Clone)]
enum Value {
    IntLiteral(i64),
    Variable(i64),
    Global(String),
}

impl Value {
    fn to_expression(&self) -> String {
        match self {
            Self::IntLiteral(value) => value.to_string(),
            Self::Variable(index) => format!("%{index}"),
            Self::Global(name) => format!("ptr @{name}"),
        }
    }
}

struct Locals {
    last_var: i64,
    var_types: HashMap<i64, Type>,
    global_types: HashMap<String, Type>,
    stack: Vec<Value>,
    strings: Vec<String>,
}

impl Locals {
    fn new() -> Self {
        Self {
            last_var: 0,
            var_types: HashMap::new(),
            global_types: HashMap::new(),
            stack: Vec::new(),
            strings: Vec::new(),
        }
    }

    fn push(&mut self, value: Value) {
        self.stack.push(value);
    }

    fn pop(&mut self) -> Option<Value> {
        self.stack.pop()
    }

    fn new_var(&mut self, type_: Type) -> i64 {
        self.last_var += 1;
        self.var_types.insert(self.last_var, type_);
        self.last_var
    }

    fn type_of(&self, value: &Value) -> &Type {
        match value {
            Value::IntLiteral(_) => &Type::Int,
            Value::Variable(index) => &self.var_types[index],
            Value::Global(name) => &self.global_types[name],
        }
    }

    fn new_string(&mut self, s: &str) {
        self.strings.push(s.to_owned());

        let global_name = format!("__string{}", self.strings.len());
        self.global_types.insert(global_name.clone(), Type::String);
        self.push(Value::Global(global_name));
    }
}

impl Display for Locals {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("last var: {}, stack:", self.last_var))?;
        for value in &self.stack {
            f.write_str(" ")?;
            f.write_str(&value.to_expression())?;
        }

        f.write_str(", strings:")?;
        for string in &self.strings {
            f.write_str(" \"")?;
            f.write_str(string)?;
            f.write_str("\"")?;
        }
        Result::Ok(())
    }
}

fn compile_arithmetic(
    opcode: &str,
    operand_count: i64,
    locals: &mut Locals,
) -> Result<String, String> {
    let result = locals.new_var(Type::Int);
    let mut instruction = format!("    %{result} = {opcode}");

    for i in 0..operand_count {
        let operand = locals.pop().ok_or("Stack underflow")?;
        if *locals.type_of(&operand) != Type::Int {
            return Result::Err("Arithmetic instruction expects integers".to_string());
        }

        if i > 0 {
            instruction += ",";
        }
        instruction += " ";
        instruction += &operand.to_expression();
    }

    locals.push(Value::Variable(result));

    Result::Ok(instruction)
}

fn compile_word(word: Word, locals: &mut Locals) -> Result<String, String> {
    match word {
        Word::Int(value) => {
            locals.push(Value::IntLiteral(value));
            Result::Ok("".to_owned())
        }
        Word::String(value) => {
            locals.new_string(value);
            Result::Ok("".to_owned())
        }
        Word::Id("+") => compile_arithmetic("add i64", 2, locals),
        Word::Id("-") => compile_arithmetic("sub i64", 2, locals),
        Word::Id("*") => compile_arithmetic("mul i64", 2, locals),
        Word::Id("/") => compile_arithmetic("div i64", 2, locals),
        Word::Id("%") => compile_arithmetic("mod i64", 2, locals),
        Word::Id("dup") => {
            let value = locals.pop().ok_or("Stack underflow")?;
            locals.push(value.clone());
            locals.push(value);
            Result::Ok("".to_owned())
        }
        Word::Id("pop") => {
            locals.pop().ok_or("Stack underflow")?;
            Result::Ok("".to_owned())
        }
        Word::Id("swp") => {
            let a = locals.pop().ok_or("Stack underflow")?;
            let b = locals.pop().ok_or("Stack underflow")?;
            locals.push(b);
            locals.push(a);
            Result::Ok("".to_owned())
        }
        Word::Id("print") => {
            let value = locals.pop().ok_or("Stack underflow")?;
            if *locals.type_of(&value) == Type::String {
                Result::Ok(format!("call i32 @puts({})", value.to_expression()))
            } else {
                Result::Err("print only supports strings".to_owned())
            }
        }
        Word::Id(id) => Err(format!("Unknown word {}", id)),
    }
}

fn compile_to_ir(code: &str) -> Result<String, String> {
    let mut ir = String::new();
    let mut locals = Locals::new();

    ir += "target triple = \"x86_64-pc-windows-msvc19.40.33813\"\n\ndefine i32 @main() {\n";
    for word in lex(code) {
        let word_ir = compile_word(word, &mut locals)?;
        if !word_ir.is_empty() {
            ir += &word_ir;
            ir += "\n";
        }
    }
    ir += "    ret i32 0\n}";

    ir += "\n";
    for (i, string) in locals.strings.iter().enumerate() {
        ir += &format!(
            "\n@__string{} = constant [{} x i8] c\"{string}\\00\"",
            i + 1,
            string.len() + 1
        );
    }

    ir += "\n\ndeclare i32 @puts(ptr)\n";

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
    let mut print = false;
    let mut run = false;

    let mut current_flag = Flag::None;
    for arg in env::args().skip(1) {
        match arg.as_str() {
            "-o" => {
                current_flag = Flag::OutputFile;
            }
            "--print" => {
                if print {
                    return Result::Err(Box::from("--print specified twice"));
                }
                print = true;
            }
            "--run" => {
                if run {
                    return Result::Err(Box::from("--run specified twice"));
                }
                run = true;
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

    let mut code = String::new();
    OpenOptions::new()
        .read(true)
        .open(input_file)?
        .read_to_string(&mut code)?;

    let ir = compile_to_ir(code.as_str())?;

    OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&ir_file)?
        .write_all(ir.as_bytes())?;

    if print {
        println!("{ir}");
    }

    run_stage("llvm-as", ir_file.as_str(), &bc_file)?;
    run_stage("llc", &bc_file, &asm_file)?;
    run_stage("clang", &asm_file, output_file.as_str())?;

    if run {
        let abs_output_path = fs::canonicalize(&output_file)?;
        Command::new(&abs_output_path).status()?;
    }

    Result::Ok(())
}
