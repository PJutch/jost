use crate::lex::Lexer;

use std::collections::HashMap;
use std::fmt::Display;

use core::panic;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Type {
    Int,
    Bool,
    String,
    FnPtr(Vec<Type>, Vec<Type>),
    List, // TODO: implement lists of type other than Type
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
            Type::List => f.write_str("List"),
            Type::Type_ => f.write_str("Type"),
        }
    }
}

pub fn display_type_list(types: &[Type]) -> String {
    let mut s = "".to_owned();
    for (i, type_) in types.iter().enumerate() {
        if i > 0 {
            s += " ";
        }
        s += &format!("{type_}");
    }
    s
}

#[derive(Clone, Debug)]
pub enum Value {
    IntLiteral(i64),
    BoolLiteral(bool),
    ListLiteral(Vec<Type>), // TODO: implement lists of type other than Type
    Type(Type),
    Variable(i64),
    Arg(i64),
    Global(String),
}

impl Value {
    pub fn unwrap_type(self) -> Type {
        match self {
            Value::Type(type_) => type_,
            _ => panic!("unwrap type assumed that value {self:?} is a type"),
        }
    }

    pub fn unwrap_list_literal(self) -> Vec<Type> {
        match self {
            Value::ListLiteral(types) => types,
            _ => panic!("unwrap list literal assumes that value {self:?} is a list literal"),
        }
    }
}

pub struct Globals {
    global_types: HashMap<String, Type>,
    pub strings: Vec<String>,
    pub lambdas: Vec<Function>,
}

impl Globals {
    pub fn new() -> Self {
        Self {
            global_types: HashMap::new(),
            strings: Vec::new(),
            lambdas: Vec::new(),
        }
    }

    pub fn new_string(&mut self, s: &str) -> String {
        self.strings.push(s.to_owned());

        let global_name = format!("__string{}", self.strings.len());
        self.global_types.insert(global_name.clone(), Type::String);
        global_name
    }

    pub fn new_lambda(&mut self, lambda: Function) -> String {
        let global_name = format!("__lambda{}", self.lambdas.len() + 1);
        self.global_types.insert(
            global_name.clone(),
            Type::FnPtr(lambda.arg_types.clone(), lambda.result_types.clone()),
        );

        self.lambdas.push(lambda);

        global_name
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct StackPosition {
    scope: usize,
    item: usize,
}

#[derive(Debug)]
pub struct Scope {
    pub stack: Vec<Value>,
    pub ir: Vec<Instruction>,

    pub to_borrow: Option<StackPosition>,

    pub end: i64,
}

pub struct Function {
    pub scopes: Vec<Scope>,

    last_var: i64,
    pub var_types: HashMap<i64, Type>,

    pub arg_types: Vec<Type>,
    pub result_types: Vec<Type>,
}

impl Function {
    pub fn new(arg_types: Vec<Type>, result_types: Vec<Type>) -> Self {
        let n_args = arg_types.len();

        let mut function = Self {
            scopes: Vec::new(),
            last_var: n_args as i64,
            var_types: HashMap::new(),
            arg_types,
            result_types,
        };

        function.new_scope();

        for i in 0..n_args {
            function.push(Value::Arg(i as i64));
        }

        function
    }

    pub fn over_top_stack_position(&self) -> StackPosition {
        StackPosition {
            scope: self.scopes.len(),
            item: 0,
        }
    }

    pub fn top_stack_position(&self) -> Option<StackPosition> {
        self.decrement_stack_position(self.over_top_stack_position())
    }

    pub fn decrement_stack_position(&self, mut pos: StackPosition) -> Option<StackPosition> {
        while pos.item == 0 && pos.scope > 0 {
            if let Some(scope) = self.scopes.get(pos.scope) {
                pos = scope.to_borrow?;
                pos.item += 1;
            } else {
                pos.scope -= 1;
                pos.item = self.scopes[pos.scope].stack.len();
            }
        }

        if pos.item != 0 {
            pos.item -= 1;
            Option::Some(pos)
        } else {
            Option::None
        }
    }

    pub fn at_stack_position(&self, pos: StackPosition) -> &Value {
        &self.scopes[pos.scope].stack[pos.item]
    }

    pub fn new_scope(&mut self) {
        self.scopes.push(Scope {
            stack: Vec::new(),
            ir: Vec::new(),
            to_borrow: self.top_stack_position(),
            end: 0,
        });
    }

    pub fn get_single_scope(&self) -> &Scope {
        if self.scopes.len() > 1 {
            panic!(
                "get_single_scope expects function to have a single scope, it has {}",
                self.scopes.len()
            );
        }
        self.scopes
            .first()
            .expect("get_single_scope expects function to have a scope")
    }

    fn print_to_borrow(&self) {
        for scope in &self.scopes {
            print!("{:?} ", scope.to_borrow);
        }
        println!();
    }

    pub fn push(&mut self, value: Value) {
        self.scopes
            .last_mut()
            .expect("push expects at least one scope to exist")
            .stack
            .push(value);
    }

    pub fn pop(&mut self) -> Option<Value> {
        if let Some(last_scope) = self.scopes.last_mut() {
            if let Some(value) = last_scope.stack.pop() {
                return Option::Some(value);
            }

            last_scope.to_borrow.map(|pos| {
                let result = self.at_stack_position(pos).clone();
                self.scopes
                    .last_mut()
                    .expect("scope existing is checked above")
                    .to_borrow = self.decrement_stack_position(pos);
                result
            })
        } else {
            Option::None
        }
    }

    pub fn add_instruction(&mut self, instruction: Instruction) {
        self.scopes
            .last_mut()
            .expect("add_instruction expects at least one scope to exist")
            .ir
            .push(instruction);
    }

    pub fn new_var(&mut self, type_: Type) -> i64 {
        self.last_var += 1;
        self.var_types.insert(self.last_var, type_);
        self.last_var
    }

    pub fn stack_as_string(&self, globals: &Globals) -> String {
        let mut types = Vec::new();

        let mut pos = self.over_top_stack_position();
        while let Some(new_pos) = self.decrement_stack_position(pos) {
            pos = new_pos;
            types.push(type_of(self.at_stack_position(pos), self, globals));
        }

        types.reverse();

        display_type_list(&types)
    }

    pub fn pop_of_type(
        &mut self,
        type_: Type,
        globals: &Globals,
        start: i64,
        end: i64,
        lexer: &Lexer,
    ) -> Result<Value, String> {
        if let Some(pos) = self.top_stack_position() {
            let value = self.at_stack_position(pos);
            if type_of(value, self, globals) == type_ {
                return Result::Ok(self.pop().expect("stack is checked to not be empty"));
            }
        }

        Result::Err(lexer.make_error_report(
            start,
            end,
            &format!(
                "expected ... {type_}, found {}",
                self.stack_as_string(globals)
            ),
        ))
    }

    pub fn pop2_of_type(
        &mut self,
        type1: Type,
        type2: Type,
        globals: &Globals,
        start: i64,
        end: i64,
        lexer: &Lexer,
    ) -> Result<(Value, Value), String> {
        if let Some(pos2) = self.top_stack_position() {
            if let Some(pos1) = self.decrement_stack_position(pos2) {
                if type_of(self.at_stack_position(pos1), self, globals) == type1
                    && type_of(self.at_stack_position(pos2), self, globals) == type2
                {
                    let value2 = self.pop().expect("stack is checked to have 2 values");
                    let value1 = self.pop().expect("stack is checked to have 2 values");
                    return Result::Ok((value1, value2));
                }
            }
        }

        Result::Err(lexer.make_error_report(
            start,
            end,
            &format!(
                "expected ... {type1} {type2}, found {}",
                self.stack_as_string(globals)
            ),
        ))
    }

    pub fn has_given_types_after(
        &self,
        types: &[Type],
        mut pos: StackPosition,
        globals: &Globals,
    ) -> bool {
        for type_ in types.iter().rev() {
            if let Some(new_pos) = self.decrement_stack_position(pos) {
                pos = new_pos;
                if type_of(self.at_stack_position(pos), self, globals) == *type_ {
                    continue;
                }
            }

            return false;
        }
        true
    }

    pub fn pop_of_any_type(
        &mut self,
        globals: &Globals,
        start: i64,
        end: i64,
        lexer: &Lexer,
    ) -> Result<Value, String> {
        if let Some(value) = self.pop() {
            return Result::Ok(value);
        }

        Result::Err(lexer.make_error_report(
            start,
            end,
            &format!("expected ... A, found {}", self.stack_as_string(globals)),
        ))
    }

    pub fn pop2_of_any_type(
        &mut self,
        globals: &Globals,
        start: i64,
        end: i64,
        lexer: &Lexer,
    ) -> Result<(Value, Value), String> {
        if let Some(pos) = self.top_stack_position() {
            if self.decrement_stack_position(pos).is_some() {
                let value2 = self.pop().expect("stack is checked to have 2 values");
                let value1 = self.pop().expect("stack is checked to have 2 values");
                return Result::Ok((value1, value2));
            }
        }

        Result::Err(lexer.make_error_report(
            start,
            end,
            &format!("expected ... A A, found {}", self.stack_as_string(globals)),
        ))
    }
}

fn print_function_ir(function: &Function) {
    for (i, scope) in function.scopes.iter().enumerate() {
        println!("  scope {i}");
        for instruction in &scope.ir {
            println!("    {instruction:?}");
        }
    }
}

pub fn print_ir(function: &Function, globals: &Globals) {
    println!("main");
    print_function_ir(function);
    for (i, lambda) in globals.lambdas.iter().enumerate() {
        println!("__lambda{}", i + 1);
        print_function_ir(lambda);
    }
}

pub fn type_of(value: &Value, function: &Function, globals: &Globals) -> Type {
    match value {
        Value::IntLiteral(_) => Type::Int,
        Value::BoolLiteral(_) => Type::Bool,
        Value::ListLiteral(_) => Type::List,
        Value::Type(_) => Type::Type_,
        Value::Variable(index) => function.var_types[index].clone(),
        Value::Arg(index) => function.arg_types[*index as usize].clone(),
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

#[derive(Clone, Copy, Debug)]
pub enum Relational {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Debug)]
pub enum Logical {
    And,
    Or,
}

#[derive(Debug)]
pub struct Phi {
    pub result_var: i64,
    pub result_type: Type,
    pub case1: Value,
    pub case2: Value,
}

#[derive(Debug)]
pub enum Instruction {
    Arithemtic(Arithemtic, Value, Value, i64),
    Relational(Relational, Value, Value, i64),
    Logical(Logical, Value, Value, i64),
    Not(Value, i64),
    Print(Value),
    Call(Value, Vec<Type>, Vec<Value>, Vec<Type>, Vec<i64>),
    If(Value, Scope, Scope, Vec<Phi>),
}
