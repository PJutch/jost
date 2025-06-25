use crate::lex::Lexer;
use crate::lex::Word;
use std::collections::HashMap;

#[derive(PartialEq, Eq, Clone, Copy)]
enum Type {
    Int,
    String,
    FnPtr,
}

#[derive(Clone, Debug)]
pub enum Value {
    IntLiteral(i64),
    Variable(i64),
    Global(String),
}

pub struct Globals {
    global_types: HashMap<String, Type>,
    pub strings: Vec<String>,
    pub lambdas: Vec<Locals>,
}

impl Globals {
    pub fn new() -> Self {
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

pub struct Locals {
    last_var: i64,
    var_types: HashMap<i64, Type>,
    stack: Vec<Value>,
    pub ir: Vec<Instruction>,
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

pub fn print_ir(locals: &Locals, globals: &Globals) {
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
pub enum Arithemtic {
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

    pub fn to_llvm(self) -> &'static str {
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
pub enum Instruction {
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

pub fn compile_to_ir(lexer: &mut Lexer, globals: &mut Globals) -> Result<Locals, String> {
    let ir = compile_function(lexer, globals)?;
    if lexer.is_empty() {
        Result::Ok(ir)
    } else {
        Result::Err("unexpected closing paranthesis".to_owned())
    }
}
