use crate::lex::Lexer;
use crate::lex::Word;
use std::collections::HashMap;
use std::fmt::Display;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Type {
    Int,
    Bool,
    String,
    FnPtr(Vec<Type>, Vec<Type>),
    Type_,
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => f.write_str("Int"),
            Type::Bool => f.write_str("Bool"),
            Type::String => f.write_str("String"),
            Type::FnPtr(arg_types, result_types) => {
                f.write_str("fn (")?;
                for (i, arg_type) in arg_types.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    f.write_fmt(format_args!("{arg_type}"))?;
                }
                f.write_str(") -> (")?;
                for (i, result_type) in result_types.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    f.write_fmt(format_args!("{result_type}"))?;
                }
                f.write_str(")")
            }
            Type::Type_ => f.write_str("Type"),
        }
    }
}

fn display_type_list(types: Vec<Type>) -> String {
    let mut s = "".to_owned();
    for (i, type_) in types.iter().enumerate() {
        if i > 0 {
            s += " ";
        }
        s += &format!("{}", type_);
    }
    s
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

impl Value {
    fn unwrap_type(&self) -> &Type {
        match self {
            Value::Type(type_) => type_,
            _ => panic!("unwrap type assumed that value {self:?} is a type"),
        }
    }
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

    fn stack_as_string(&self, globals: &Globals) -> String {
        let mut types = Vec::new();
        for value in &self.stack {
            types.push(type_of(value, self, globals));
        }
        display_type_list(types)
    }

    fn pop_of_type(
        &mut self,
        type_: Type,
        globals: &Globals,
        position: i64,
        lexer: &Lexer,
    ) -> Result<Value, String> {
        if !self.stack.is_empty() {
            let value = &self.stack[self.stack.len() - 1];
            if type_of(value, self, globals) == type_ {
                return Result::Ok(self.pop().expect("stack is checked to not be empty"));
            }
        }

        Result::Err(lexer.make_error_report(
            position,
            &format!(
                "expected ... {type_}, found {}",
                self.stack_as_string(globals)
            ),
        ))
    }

    fn pop2_of_type(
        &mut self,
        type1: Type,
        type2: Type,
        globals: &Globals,
        position: i64,
        lexer: &Lexer,
    ) -> Result<(Value, Value), String> {
        if self.stack.len() >= 2 {
            let value1 = &self.stack[self.stack.len() - 2];
            let value2 = &self.stack[self.stack.len() - 1];
            if type_of(value1, self, globals) == type1 && type_of(value2, self, globals) == type2 {
                let value2 = self.pop().expect("stack is checked to have 2 values");
                let value1 = self.pop().expect("stack is checked to have 2 values");
                return Result::Ok((value1, value2));
            }
        }

        Result::Err(lexer.make_error_report(
            position,
            &format!(
                "expected ... {type1} {type2}, found {}",
                self.stack_as_string(globals)
            ),
        ))
    }

    fn popn_of_type_error_message(
        &self,
        types: &[Type],
        globals: &Globals,
        position: i64,
        lexer: &Lexer,
    ) -> String {
        let mut types_string = "".to_owned();
        for (i, type_) in types.iter().enumerate() {
            if i > 0 {
                types_string += ", ";
            }
            types_string += &format!("{type_}");
        }
        lexer.make_error_report(
            position,
            &format!(
                "expected ... {types_string}, found {}",
                self.stack_as_string(globals)
            ),
        )
    }

    fn popn_of_type(
        &mut self,
        types: &[Type],
        globals: &Globals,
        position: i64,
        lexer: &Lexer,
    ) -> Result<Vec<Value>, String> {
        if self.stack.len() < types.len() {
            return Result::Err(self.popn_of_type_error_message(types, globals, position, lexer));
        }

        for (i, type_) in types.iter().enumerate() {
            if type_of(
                &self.stack[self.stack.len() - types.len() + i],
                self,
                globals,
            ) != *type_
            {
                return Result::Err(
                    self.popn_of_type_error_message(types, globals, position, lexer),
                );
            }
        }

        let mut values = Vec::new();
        for _ in 0..types.len() {
            values.push(self.pop().expect("stack len is checked above"));
        }
        values.reverse();
        Result::Ok(values)
    }

    fn pop_of_any_type(
        &mut self,
        globals: &Globals,
        position: i64,
        lexer: &Lexer,
    ) -> Result<Value, String> {
        if let Some(value) = self.pop() {
            return Result::Ok(value);
        }

        Result::Err(lexer.make_error_report(
            position,
            &format!("expected ... A, found {}", self.stack_as_string(globals)),
        ))
    }

    fn pop2_of_any_type(
        &mut self,
        globals: &Globals,
        position: i64,
        lexer: &Lexer,
    ) -> Result<(Value, Value), String> {
        if self.stack.len() >= 2 {
            let value2 = self.pop().expect("stack is checked to have 2 values");
            let value1 = self.pop().expect("stack is checked to have 2 values");
            return Result::Ok((value1, value2));
        }

        Result::Err(lexer.make_error_report(
            position,
            &format!("expected ... A A, found {}", self.stack_as_string(globals)),
        ))
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

fn compile_call_args_error_message(
    arg_types: Vec<Type>,
    result_types: Vec<Type>,
    locals: &Locals,
    globals: &Globals,
    lexer: &Lexer,
    position: i64,
) -> String {
    let args_string = display_type_list(arg_types);
    let results_string = display_type_list(result_types);
    lexer.make_error_report(
        position,
        &format!(
            "expected ... {args_string} ({args_string} {results_string} FnPtr), found {}",
            locals.stack_as_string(globals)
        ),
    )
}

fn compile_call(
    locals: &mut Locals,
    globals: &Globals,
    lexer: &Lexer,
    position: i64,
) -> Result<(), String> {
    if !locals.stack.is_empty() {
        let fn_ptr = &locals.stack[locals.stack.len() - 1];
        if let Type::FnPtr(arg_types, result_types) = type_of(fn_ptr, locals, globals) {
            if locals.stack.len() < arg_types.len() {
                return Result::Err(compile_call_args_error_message(
                    arg_types,
                    result_types,
                    locals,
                    globals,
                    lexer,
                    position,
                ));
            }

            for (i, type_) in arg_types.iter().enumerate() {
                if type_of(
                    &locals.stack[locals.stack.len() - arg_types.len() + i],
                    locals,
                    globals,
                ) != *type_
                {
                    return Result::Err(compile_call_args_error_message(
                        arg_types,
                        result_types,
                        locals,
                        globals,
                        lexer,
                        position,
                    ));
                }
            }

            let mut args = Vec::new();
            for _ in 0..arg_types.len() {
                args.push(locals.pop().expect("stack len is checked above"));
            }
            args.reverse();

            let fn_ptr = locals.pop().expect("stack len is checked above");

            let mut results = Vec::new();
            for result_type in &result_types {
                let result_var = locals.new_var(result_type.clone());
                locals.push(Value::Variable(result_var));
                results.push(result_var);
            }

            locals
                .ir
                .push(Instruction::Call(fn_ptr, arg_types.clone(), args, results));
            return Result::Ok(());
        }
    }

    Result::Err(lexer.make_error_report(
        position,
        &format!(
            "expected ... FnPtr, found {}",
            locals.stack_as_string(globals)
        ),
    ))
}

fn do_type_assertion(
    locals: &mut Locals,
    globals: &Globals,
    lexer: &Lexer,
    position: i64,
) -> Result<(), String> {
    if locals.stack.len() >= 2 {
        let value = &locals.stack[locals.stack.len() - 2];
        let type_ = &locals.stack[locals.stack.len() - 1];
        if let Value::Type(type_) = type_ {
            let type_ = type_.clone();

            if type_of(value, locals, globals) != type_ {
                return Result::Err(lexer.make_error_report(
                    position,
                    &format!(
                        "expected ... {type_}, found {}",
                        locals.stack_as_string(globals)
                    ),
                ));
            }
            locals.pop();
        }
    }

    Result::Err(lexer.make_error_report(
        position,
        &format!(
            "expected ... value Type, found {}",
            locals.stack_as_string(globals)
        ),
    ))
}

fn compile_function(
    lexer: &mut Lexer,
    globals: &mut Globals,
    args: Vec<Type>,
    results: Vec<Type>,
    consume_all: bool,
) -> Result<Locals, String> {
    let mut last_pos = 0;
    let mut locals = Locals::new(args, results);
    while let Some(word) = lexer.next_word() {
        match word {
            Word::Int(value, _, _) => {
                locals.push(Value::IntLiteral(value));
            }
            Word::String(value, _, _) => {
                locals.push(Value::Global(globals.new_string(value)));
            }
            Word::Id(id, start, _) if Arithemtic::knows_id(id) => {
                let (a, b) = locals.pop2_of_type(Type::Int, Type::Int, globals, start, lexer)?;

                let result_var = locals.new_var(Type::Int);
                locals.push(Value::Variable(result_var));

                locals.ir.push(Instruction::Arithemtic(
                    Arithemtic::from_id(id).expect(
                        "arithmetic from_id should succeed because it's checked in pattern guard",
                    ),
                    a,
                    b,
                    result_var,
                ));
            }
            Word::Id(id, start, _) if Relational::knows_id(id) => {
                let (a, b) = locals.pop2_of_type(Type::Int, Type::Int, globals, start, lexer)?;

                let result_var = locals.new_var(Type::Bool);
                locals.push(Value::Variable(result_var));

                locals.ir.push(Instruction::Relational(
                    Relational::from_id(id).expect(
                        "relational from_id should succeed because it's checked in pattern guard",
                    ),
                    a,
                    b,
                    result_var,
                ));
            }
            Word::Id(id, start, _) if Logical::knows_id(id) => {
                let (a, b) = locals.pop2_of_type(Type::Bool, Type::Bool, globals, start, lexer)?;

                let result_var = locals.new_var(Type::Bool);
                locals.push(Value::Variable(result_var));

                locals.ir.push(Instruction::Logical(
                    Logical::from_id(id).expect(
                        "logical from_id should succeed because it's checked in pattern guard",
                    ),
                    a,
                    b,
                    result_var,
                ));
            }
            Word::Id("!", start, _) => {
                let value = locals.pop_of_type(Type::Bool, globals, start, lexer)?;

                let result_var = locals.new_var(Type::Bool);
                locals.push(Value::Variable(result_var));

                locals.ir.push(Instruction::Not(value, result_var));
            }
            Word::Id("true", _, _) => {
                locals.push(Value::BoolLiteral(true));
            }
            Word::Id("false", _, _) => {
                locals.push(Value::BoolLiteral(false));
            }
            Word::Id("dup", start, _) => {
                let value = locals.pop_of_any_type(globals, start, lexer)?;
                locals.push(value.clone());
                locals.push(value);
            }
            Word::Id("pop", start, _) => {
                locals.pop_of_any_type(globals, start, lexer)?;
            }
            Word::Id("swp", start, _) => {
                let (a, b) = locals.pop2_of_any_type(globals, start, lexer)?;
                locals.push(b);
                locals.push(a);
            }
            Word::Id("print", start, _) => {
                let value = locals.pop_of_type(Type::String, globals, start, lexer)?;
                locals.ir.push(Instruction::Print(value));
            }
            Word::Id("(", _, _) => {
                let lambda_locals =
                    compile_function(lexer, globals, Vec::new(), Vec::new(), false)?;
                locals.push(Value::Global(globals.new_lambda(lambda_locals)));
            }
            Word::Id(")", _, _) => break,
            Word::Id("call", start, _) => compile_call(&mut locals, globals, lexer, start)?,
            Word::Id("if", start, _) => {
                if !matches!(lexer.next_word(), Some(Word::Id("(", _, _))) {
                    return Result::Err(
                        lexer.make_error_report(start, "if should be followed by open paranthesis"),
                    );
                }

                let condition = locals.pop_of_type(Type::Bool, globals, start, lexer)?;

                locals.ir.push(Instruction::If(
                    condition,
                    compile_function(lexer, globals, Vec::new(), Vec::new(), false)?,
                ));
            }
            Word::Id("fn", start, _) => {
                if !matches!(lexer.next_word(), Some(Word::Id("(", _, _))) {
                    return Result::Err(
                        lexer.make_error_report(start, "fn should be followed by open paranthesis"),
                    );
                }

                let (arg, result) =
                    locals.pop2_of_type(Type::Type_, Type::Type_, globals, start, lexer)?;

                let lambda_locals = compile_function(
                    lexer,
                    globals,
                    Vec::from([arg.unwrap_type().clone()]),
                    Vec::from([result.unwrap_type().clone()]),
                    false,
                )?;
                locals.push(Value::Global(globals.new_lambda(lambda_locals)));
            }
            Word::Id("Int", _, _) => {
                locals.push(Value::Type(Type::Int));
            }
            Word::Id("String", _, _) => {
                locals.push(Value::Type(Type::String));
            }
            Word::Id("Bool", _, _) => {
                locals.push(Value::Type(Type::Bool));
            }
            Word::Id(":", start, _) => do_type_assertion(&mut locals, globals, lexer, start)?,
            Word::Id(id, start, _) => {
                return Err(lexer.make_error_report(start, &format!("Unknown word {}", id)))
            }
        }
        last_pos = lexer.current_byte as i64;
    }

    if !lexer.is_empty() {
        return Result::Err(lexer.make_error_report(last_pos, "unexpected closing paranthesis"));
    }

    let result_types = locals.result_types.clone();
    locals.result_values = locals.popn_of_type(&result_types, globals, last_pos, lexer)?;
    Result::Ok(locals)
}

pub fn compile_to_ir(lexer: &mut Lexer, globals: &mut Globals) -> Result<Locals, String> {
    compile_function(lexer, globals, Vec::new(), Vec::new(), true)
}
