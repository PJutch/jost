use core::str;
use std::collections::HashMap;
use std::env;
use std::error::Error;
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

struct Lexer<'a> {
    code: &'a str,
    current_byte: usize,
}

impl<'a> Lexer<'a> {
    fn new(code: &'a str) -> Self {
        Self {
            code,
            current_byte: 0,
        }
    }

    fn next_word(&mut self) -> Option<Word<'a>> {
        let mut token_start = self.current_byte;
        let mut quoted = false;
        while self.current_byte <= self.code.len() {
            let current_byte = self.current_byte;
            self.current_byte += 1;

            if get_byte(self.code, current_byte).is_some_and(|c| c == b'"') {
                if quoted {
                    return Option::Some(Word::String(&self.code[token_start..current_byte]));
                }
                token_start = self.current_byte;
                quoted = true;
            } else if !quoted
                && get_byte(self.code, current_byte)
                    .is_none_or(|c| c == b')' && token_start + 1 < current_byte)
            {
                if let Option::Some(token) = parse_token(&self.code[token_start..current_byte]) {
                    self.current_byte -= 1;
                    return Option::Some(token);
                }
                token_start = current_byte;
            } else if !quoted && get_byte(self.code, current_byte).is_none_or(|c| c == b'(') {
                if let Option::Some(token) = parse_token(&self.code[token_start..=current_byte]) {
                    return Option::Some(token);
                }
                token_start = self.current_byte;
            } else if !quoted
                && get_byte(self.code, current_byte).is_none_or(|c| c.is_ascii_whitespace())
            {
                if let Option::Some(token) = parse_token(&self.code[token_start..current_byte]) {
                    return Option::Some(token);
                }
                token_start = self.current_byte;
            }
        }
        Option::None
    }

    fn is_empty(&self) -> bool {
        for i in self.current_byte..self.code.len() {
            if get_byte(self.code, i).is_some_and(|c| !c.is_ascii_whitespace()) {
                return false;
            }
        }
        true
    }

    fn debug_print(code: &'a str) {
        let mut lexer = Self::new(code);
        while let Some(word) = lexer.next_word() {
            println!("{word:?}");
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum Type {
    Int,
    String,
    FnPtr,
}

#[derive(Clone, Debug)]
enum Value {
    IntLiteral(i64),
    Variable(i64),
    Global(String),
}

impl Value {
    fn to_expression(&self, var_numbers: &HashMap<i64, i64>) -> String {
        match self {
            Self::IntLiteral(value) => value.to_string(),
            Self::Variable(index) => format!("%{}", var_numbers[index]),
            Self::Global(name) => format!("ptr @{name}"),
        }
    }

    fn to_callable(&self, var_numbers: &HashMap<i64, i64>) -> String {
        match self {
            Self::IntLiteral(_) => panic!("trying to call int literal"),
            Self::Variable(index) => format!("%{}", var_numbers[index]),
            Self::Global(name) => format!("@{name}"),
        }
    }
}

struct Globals {
    global_types: HashMap<String, Type>,
    strings: Vec<String>,
    lambdas: Vec<Locals>,
}

impl Globals {
    fn new() -> Self {
        Self {
            global_types: HashMap::new(),
            strings: Vec::new(),
            lambdas: Vec::new(),
        }
    }

    fn new_string(&mut self, s: &str) -> String {
        self.strings.push(s.to_owned());

        let global_name = format!("__string{}", self.strings.len());
        self.global_types.insert(global_name.clone(), Type::String);
        global_name
    }

    fn new_lambda(&mut self, locals: Locals) -> String {
        self.lambdas.push(locals);

        let global_name = format!("__lambda{}", self.lambdas.len());
        self.global_types.insert(global_name.clone(), Type::FnPtr);
        global_name
    }
}

struct Locals {
    last_var: i64,
    var_types: HashMap<i64, Type>,
    stack: Vec<Value>,
    ir: Vec<Instruction>,
}

impl Locals {
    fn new() -> Self {
        Self {
            last_var: 0,
            var_types: HashMap::new(),
            stack: Vec::new(),
            ir: Vec::new(),
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

    fn print_ir(&self) {
        for instruction in &self.ir {
            println!("{instruction:?}");
        }
    }
}

fn print_ir(locals: &Locals, globals: &Globals) {
    println!("main");
    locals.print_ir();
    for (i, lambda) in globals.lambdas.iter().enumerate() {
        println!("__lambda{}", i + 1);
        lambda.print_ir();
    }
}

fn type_of(value: &Value, locals: &Locals, globals: &Globals) -> Type {
    match value {
        Value::IntLiteral(_) => Type::Int,
        Value::Variable(index) => locals.var_types[index],
        Value::Global(name) => globals.global_types[name],
    }
}

#[derive(Clone, Copy, Debug)]
enum Arithemtic {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

impl Arithemtic {
    fn from_id(id: &str) -> Option<Arithemtic> {
        match id {
            "+" => Option::Some(Arithemtic::Add),
            "-" => Option::Some(Arithemtic::Sub),
            "*" => Option::Some(Arithemtic::Mul),
            "/" => Option::Some(Arithemtic::Div),
            "%" => Option::Some(Arithemtic::Mod),
            _ => Option::None,
        }
    }

    fn knows_id(id: &str) -> bool {
        Arithemtic::from_id(id).is_some()
    }

    fn to_llvm(self) -> &'static str {
        match self {
            Arithemtic::Add => "add i64",
            Arithemtic::Sub => "sub i64",
            Arithemtic::Mul => "mul i64",
            Arithemtic::Div => "div i64",
            Arithemtic::Mod => "mod i64",
        }
    }
}

#[derive(Debug)]
enum Instruction {
    Arithemtic(Arithemtic, Value, Value, i64),
    Print(Value),
    Call(Value),
}

fn compile_function(lexer: &mut Lexer, globals: &mut Globals) -> Result<Locals, String> {
    let mut locals = Locals::new();
    while let Some(word) = lexer.next_word() {
        match word {
            Word::Int(value) => {
                locals.push(Value::IntLiteral(value));
            }
            Word::String(value) => {
                locals.push(Value::Global(globals.new_string(value)));
            }
            Word::Id(id) if Arithemtic::knows_id(id) => {
                let result_var = locals.new_var(Type::Int);

                let a = locals.pop().ok_or("Stack underflow")?;
                let b = locals.pop().ok_or("Stack underflow")?;

                if type_of(&a, &locals, globals) == Type::Int
                    && type_of(&b, &locals, globals) == Type::Int
                {
                    locals.ir.push(Instruction::Arithemtic(
                        Arithemtic::from_id(id).expect(
                            "arithmetic from_id should succeed because it's checked in pattern guard",
                        ),
                        a,
                        b,
                        result_var,
                    ));

                    locals.push(Value::Variable(result_var));
                } else {
                    return Result::Err("arithmetic expects ints".to_owned());
                }
            }
            Word::Id("dup") => {
                let value = locals.pop().ok_or("Stack underflow")?;
                locals.push(value.clone());
                locals.push(value);
            }
            Word::Id("pop") => {
                locals.pop().ok_or("Stack underflow")?;
            }
            Word::Id("swp") => {
                let a = locals.pop().ok_or("Stack underflow")?;
                let b = locals.pop().ok_or("Stack underflow")?;
                locals.push(b);
                locals.push(a);
            }
            Word::Id("print") => {
                let value = locals.pop().ok_or("Stack underflow")?;
                if type_of(&value, &locals, globals) == Type::String {
                    locals.ir.push(Instruction::Print(value));
                } else {
                    return Result::Err("print only supports strings".to_owned());
                }
            }
            Word::Id("(") => {
                let lambda_locals = compile_function(lexer, globals)?;
                locals.push(Value::Global(globals.new_lambda(lambda_locals)));
            }
            Word::Id(")") => break,
            Word::Id("call") => {
                let value = locals.pop().ok_or("Stack underflow")?;
                if type_of(&value, &locals, globals) == Type::FnPtr {
                    locals.ir.push(Instruction::Call(value));
                } else {
                    return Result::Err("call works only with function pointers".to_owned());
                }
            }
            Word::Id(id) => return Err(format!("Unknown word {}", id)),
        }
    }
    Result::Ok(locals)
}

fn compile_to_ir(lexer: &mut Lexer, globals: &mut Globals) -> Result<Locals, String> {
    let ir = compile_function(lexer, globals)?;
    if lexer.is_empty() {
        Result::Ok(ir)
    } else {
        Result::Err("unexpected closing paranthesis".to_owned())
    }
}

struct GenerationContext {
    last_var_number: i64,
    var_numbers: HashMap<i64, i64>,
}

impl GenerationContext {
    fn new() -> Self {
        Self {
            last_var_number: 0,
            var_numbers: HashMap::new(),
        }
    }

    fn next_var_number(&mut self, var: i64) -> i64 {
        self.last_var_number += 1;
        self.var_numbers.insert(var, self.last_var_number);
        self.last_var_number
    }
}

fn generate_instruction_llvm(
    instruction: &Instruction,
    context: &mut GenerationContext,
) -> Result<String, String> {
    match instruction {
        Instruction::Arithemtic(op, a, b, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            Result::Ok(format!(
                "    %{result_var_number} = {} {}, {}",
                op.to_llvm(),
                a.to_expression(&context.var_numbers),
                b.to_expression(&context.var_numbers)
            ))
        }
        Instruction::Print(value) => {
            context.next_var_number(-1);
            Result::Ok(format!(
                "    call i32 @puts({})",
                value.to_expression(&context.var_numbers)
            ))
        }
        Instruction::Call(value) => Result::Ok(format!(
            "    call void {}()",
            value.to_callable(&context.var_numbers)
        )),
    }
}

fn generate_function_llvm(locals: &Locals) -> Result<String, String> {
    let mut llvm = String::new();
    let mut context = GenerationContext::new();
    for instruction in &locals.ir {
        let word_ir = generate_instruction_llvm(instruction, &mut context)?;
        llvm += &word_ir;
        llvm += "\n";
    }
    Result::Ok(llvm)
}

fn generate_llvm(locals: &Locals, globals: &Globals) -> Result<String, String> {
    let mut llvm =
        "target triple = \"x86_64-pc-windows-msvc19.40.33813\"\n\ndefine i32 @main() {\n"
            .to_owned();
    llvm += &generate_function_llvm(locals)?;
    llvm += "    ret i32 0\n}\n\n";

    for (i, lambda) in globals.lambdas.iter().enumerate() {
        llvm += &format!("define void @__lambda{}() {{\n", i + 1);
        llvm += &generate_function_llvm(lambda)?;
        llvm += "    ret void\n}\n\n";
    }

    for (i, string) in globals.strings.iter().enumerate() {
        llvm += &format!(
            "@__string{} = constant [{} x i8] c\"{string}\\00\"\n",
            i + 1,
            string.len() + 1
        );
    }
    llvm += "\n";

    llvm += "declare i32 @puts(ptr)\n";
    Result::Ok(llvm)
}

fn compile(code: &str, should_print_ir: bool) -> Result<String, String> {
    let mut lexer = Lexer::new(code);
    let mut globals = Globals::new();

    let locals = compile_to_ir(&mut lexer, &mut globals)?;
    if should_print_ir {
        print_ir(&locals, &globals);
    }

    generate_llvm(&locals, &globals)
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
    let mut lex = false;
    let mut ir = false;
    let mut print = false;
    let mut run = false;

    let mut current_flag = Flag::None;
    for arg in env::args().skip(1) {
        match arg.as_str() {
            "-o" => {
                current_flag = Flag::OutputFile;
            }
            "--run" => {
                if run {
                    return Result::Err(Box::from("--run specified twice"));
                }
                run = true;
            }
            "--lex" => {
                if lex {
                    return Result::Err(Box::from("--lex specified twice"));
                }
                lex = true;
            }
            "--ir" => {
                if ir {
                    return Result::Err(Box::from("--ir specified twice"));
                }
                ir = true;
            }
            "--print" => {
                if print {
                    return Result::Err(Box::from("--print specified twice"));
                }
                print = true;
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

    if lex {
        Lexer::debug_print(code.as_str());
    }

    let llvm = compile(code.as_str(), ir)?;

    OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&ir_file)?
        .write_all(llvm.as_bytes())?;

    if print {
        println!("{llvm}");
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
