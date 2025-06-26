use crate::lex::Lexer;
use crate::lex::Word;
use std::collections::HashMap;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Type {
    Int,
    Bool,
    String,
    FnPtr(Vec<Type>, Vec<Type>),
    Type_,
}

#[derive(Clone, Debug)]
pub enum Value {
    IntLiteral(i64),
    BoolLiteral(bool),
    Type(Type),
    Variable(i64),
    Arg(i64),
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
        let global_name = format!("__lambda{}", self.lambdas.len() + 1);
        self.global_types.insert(
            global_name.clone(),
            Type::FnPtr(locals.arg_types.clone(), locals.result_types.clone()),
        );

        self.lambdas.push(locals);

        global_name
    }
}

#[derive(Debug)]
pub struct Locals {
    last_var: i64,
    pub var_types: HashMap<i64, Type>,
    stack: Vec<Value>,
    pub ir: Vec<Instruction>,
    pub arg_types: Vec<Type>,
    pub result_types: Vec<Type>,
    pub result_values: Vec<Value>,
}

impl Locals {
    fn new(arg_types: Vec<Type>, result_types: Vec<Type>) -> Self {
        let n_args = arg_types.len();
        let n_results = result_types.len();

        let mut locals = Self {
            last_var: n_args as i64,
            var_types: HashMap::new(),
            stack: Vec::new(),
            ir: Vec::new(),
            arg_types,
            result_types,
            result_values: Vec::with_capacity(n_results),
        };

        for i in 0..n_args {
            locals.push(Value::Arg(i as i64));
        }

        locals
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
        Value::BoolLiteral(_) => Type::Bool,
        Value::Type(_) => Type::Type_,
        Value::Variable(index) => locals.var_types[index].clone(),
        Value::Arg(index) => locals.arg_types[*index as usize].clone(),
        Value::Global(name) => globals.global_types[name].clone(),
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
    fn from_id(id: &str) -> Option<Self> {
        match id {
            "+" => Option::Some(Self::Add),
            "-" => Option::Some(Self::Sub),
            "*" => Option::Some(Self::Mul),
            "/" => Option::Some(Self::Div),
            "%" => Option::Some(Self::Mod),
            _ => Option::None,
        }
    }

    fn knows_id(id: &str) -> bool {
        Self::from_id(id).is_some()
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Relational {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl Relational {
    fn from_id(id: &str) -> Option<Self> {
        match id {
            "==" => Option::Some(Self::Eq),
            "!=" => Option::Some(Self::Ne),
            "<" => Option::Some(Self::Lt),
            "<=" => Option::Some(Self::Le),
            ">" => Option::Some(Self::Gt),
            ">=" => Option::Some(Self::Ge),
            _ => Option::None,
        }
    }

    fn knows_id(id: &str) -> bool {
        Self::from_id(id).is_some()
    }
}

#[derive(Debug)]
pub enum Logical {
    And,
    Or,
}

impl Logical {
    fn from_id(id: &str) -> Option<Self> {
        match id {
            "&&" => Option::Some(Self::And),
            "||" => Option::Some(Self::Or),
            _ => Option::None,
        }
    }

    fn knows_id(id: &str) -> bool {
        Self::from_id(id).is_some()
    }
}

#[derive(Debug)]
pub enum Instruction {
    Arithemtic(Arithemtic, Value, Value, i64),
    Relational(Relational, Value, Value, i64),
    Logical(Logical, Value, Value, i64),
    Not(Value, i64),
    Print(Value),
    Call(Value, Vec<Type>, Vec<Value>, Vec<i64>),
    If(Value, Locals),
}

fn compile_function(
    lexer: &mut Lexer,
    globals: &mut Globals,
    args: Vec<Type>,
    results: Vec<Type>,
) -> Result<Locals, String> {
    let mut locals = Locals::new(args, results);
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

                let b = locals.pop().ok_or("Stack underflow in arithmetic")?;
                let a = locals.pop().ok_or("Stack underflow in arithmetic")?;

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
            Word::Id(id) if Relational::knows_id(id) => {
                let result_var = locals.new_var(Type::Bool);

                let b = locals.pop().ok_or("Stack underflow in relational")?;
                let a = locals.pop().ok_or("Stack underflow in relational")?;

                if type_of(&a, &locals, globals) == Type::Int
                    && type_of(&b, &locals, globals) == Type::Int
                {
                    locals.ir.push(Instruction::Relational(
                        Relational::from_id(id).expect(
                            "relational from_id should succeed because it's checked in pattern guard",
                        ),
                        a,
                        b,
                        result_var,
                    ));

                    locals.push(Value::Variable(result_var));
                } else {
                    return Result::Err("relational expects ints".to_owned());
                }
            }
            Word::Id(id) if Logical::knows_id(id) => {
                let result_var = locals.new_var(Type::Bool);

                let b = locals.pop().ok_or("Stack underflow in logical")?;
                let a = locals.pop().ok_or("Stack underflow in logical")?;

                if type_of(&a, &locals, globals) == Type::Bool
                    && type_of(&b, &locals, globals) == Type::Bool
                {
                    locals.ir.push(Instruction::Logical(
                        Logical::from_id(id).expect(
                            "logical from_id should succeed because it's checked in pattern guard",
                        ),
                        a,
                        b,
                        result_var,
                    ));

                    locals.push(Value::Variable(result_var));
                } else {
                    return Result::Err("logical expects bools".to_owned());
                }
            }
            Word::Id("!") => {
                let result_var = locals.new_var(Type::Bool);
                let value = locals.pop().ok_or("Stack underflow in not")?;

                if type_of(&value, &locals, globals) == Type::Bool {
                    locals.ir.push(Instruction::Not(value, result_var));
                    locals.push(Value::Variable(result_var));
                } else {
                    return Result::Err("not expects bool".to_owned());
                }
            }
            Word::Id("true") => {
                locals.push(Value::BoolLiteral(true));
            }
            Word::Id("false") => {
                locals.push(Value::BoolLiteral(false));
            }
            Word::Id("dup") => {
                let value = locals.pop().ok_or("Stack underflow in dup")?;
                locals.push(value.clone());
                locals.push(value);
            }
            Word::Id("pop") => {
                locals.pop().ok_or("Stack underflow in pop")?;
            }
            Word::Id("swp") => {
                let a = locals.pop().ok_or("Stack underflow in swp")?;
                let b = locals.pop().ok_or("Stack underflow in swp")?;
                locals.push(b);
                locals.push(a);
            }
            Word::Id("print") => {
                let value = locals.pop().ok_or("Stack underflow in print")?;
                if type_of(&value, &locals, globals) == Type::String {
                    locals.ir.push(Instruction::Print(value));
                } else {
                    return Result::Err("print only supports strings".to_owned());
                }
            }
            Word::Id("(") => {
                let lambda_locals = compile_function(lexer, globals, Vec::new(), Vec::new())?;
                locals.push(Value::Global(globals.new_lambda(lambda_locals)));
            }
            Word::Id(")") => break,
            Word::Id("call") => {
                let value = locals.pop().ok_or("Stack underflow in call")?;
                if let Type::FnPtr(arg_types, result_types) = type_of(&value, &locals, globals) {
                    let mut args = Vec::new();
                    for arg_type in &arg_types {
                        let arg = locals.pop().ok_or("Stack underflow at call")?;
                        if type_of(&arg, &locals, globals) != *arg_type {
                            return Result::Err("wrong arg type".to_owned());
                        }
                        args.push(arg);
                    }

                    let mut results = Vec::new();
                    for result_type in &result_types {
                        let result_var = locals.new_var(result_type.clone());
                        locals.push(Value::Variable(result_var));
                        results.push(result_var);
                    }

                    locals
                        .ir
                        .push(Instruction::Call(value, arg_types.clone(), args, results));
                } else {
                    return Result::Err("call works only with function pointers".to_owned());
                }
            }
            Word::Id("if") => {
                if !matches!(lexer.next_word(), Some(Word::Id("("))) {
                    return Result::Err("if should be followed by open paranthesis".to_owned());
                }

                let condition = locals.pop().ok_or("Stack underflow in if")?;
                if type_of(&condition, &locals, globals) != Type::Bool {
                    return Result::Err("if expects a bool".to_owned());
                }

                locals.ir.push(Instruction::If(
                    condition,
                    compile_function(lexer, globals, Vec::new(), Vec::new())?,
                ));
            }
            Word::Id("fn") => {
                if !matches!(lexer.next_word(), Some(Word::Id("("))) {
                    return Result::Err("fn should be followed by open paranthesis".to_owned());
                }

                if let Value::Type(result) = locals.pop().ok_or("Stack underflow in fn")? {
                    if let Value::Type(arg) = locals.pop().ok_or("Stack underflow in fn")? {
                        let lambda_locals = compile_function(
                            lexer,
                            globals,
                            Vec::from([arg]),
                            Vec::from([result]),
                        )?;
                        locals.push(Value::Global(globals.new_lambda(lambda_locals)));
                    } else {
                        return Result::Err("arg type should be type".to_owned());
                    }
                } else {
                    return Result::Err("result type should be type".to_owned());
                }
            }
            Word::Id("Int") => {
                locals.push(Value::Type(Type::Int));
            }
            Word::Id("String") => {
                locals.push(Value::Type(Type::String));
            }
            Word::Id("Bool") => {
                locals.push(Value::Type(Type::Bool));
            }
            Word::Id(id) => return Err(format!("Unknown word {}", id)),
        }
    }

    for result_type in locals.result_types.clone() {
        let result_value = locals.pop().ok_or("Stack underflow in return")?;
        if type_of(&result_value, &locals, globals) != result_type {
            return Result::Err("result type mismatch".to_owned());
        }
        locals.result_values.push(result_value);
    }
    locals.result_values.reverse();

    Result::Ok(locals)
}

pub fn compile_to_ir(lexer: &mut Lexer, globals: &mut Globals) -> Result<Locals, String> {
    let ir = compile_function(lexer, globals, Vec::new(), Vec::new())?;
    if lexer.is_empty() {
        Result::Ok(ir)
    } else {
        Result::Err("unexpected closing paranthesis".to_owned())
    }
}
