use crate::lex::Lexer;
use crate::lex::Location;

use std::collections::btree_map::Values;
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

#[derive(Debug, Clone)]
pub struct Scope {
    pub stack: Vec<Value>,
    pub no_return: bool,

    pub n_borrowed: i64,

    create_borrowed_vars: bool,
    borrowed_vars: HashMap<i64, (i64, Value)>,

    pub ir: Vec<Instruction>,

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

        function.new_scope(false);

        for i in 0..n_args {
            function.push(Value::Arg(i as i64));
        }

        function
    }

    // this will create borrowed_vars automatically
    pub fn nth_from_top(&mut self, n: i64, globals: &Globals) -> Option<Value> {
        self.nth_from_top_impl(n as usize, self.scopes.len() - 1, globals)
    }

    fn create_borrowed_var(
        &mut self,
        scope_index: usize,
        borrowed_var_index: usize,
        value: Value,
        globals: &Globals,
    ) -> i64 {
        let var = self.new_var(type_of(&value, self, globals));
        self.scopes[scope_index]
            .borrowed_vars
            .insert(borrowed_var_index as i64, (var, value.clone()));
        var
    }

    pub fn nth_from_top_impl(
        &mut self,
        n: usize,
        current_scope_index: usize,
        globals: &Globals,
    ) -> Option<Value> {
        let current_scope = self.scopes.get_mut(current_scope_index)?;
        if n < current_scope.stack.len() {
            return Option::Some(current_scope.stack[current_scope.stack.len() - n - 1].clone());
        }

        let next_n = n - current_scope.stack.len() + current_scope.n_borrowed as usize;
        if current_scope.create_borrowed_vars {
            if let Some((_, value)) = current_scope.borrowed_vars.get(&(next_n as i64)) {
                return Option::Some(value.clone());
            }
        }

        let value = if current_scope_index > 0 {
            self.nth_from_top_impl(next_n, current_scope_index - 1, globals)?
        } else {
            return Option::None;
        };

        if self
            .scopes
            .get_mut(current_scope_index)?
            .create_borrowed_vars
        {
            Option::Some(Value::Variable(self.create_borrowed_var(
                current_scope_index,
                next_n,
                value,
                globals,
            )))
        } else {
            Option::Some(value)
        }
    }

    pub fn new_scope(&mut self, create_borrowed_vars: bool) {
        self.scopes.push(Scope {
            stack: Vec::new(),
            n_borrowed: 0,
            no_return: false,
            create_borrowed_vars,
            borrowed_vars: HashMap::new(),
            ir: Vec::new(),
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

    pub fn mark_no_return(&mut self) {
        self.scopes
            .last_mut()
            .expect("no_return expects at least one scope to exist")
            .no_return = true;
    }

    pub fn is_no_return(&self) -> bool {
        self.scopes
            .last()
            .expect("no_return expects at least one scope to exist")
            .no_return
    }

    pub fn push(&mut self, value: Value) {
        self.scopes
            .last_mut()
            .expect("push expects at least one scope to exist")
            .stack
            .push(value);
    }

    pub fn pop(&mut self, globals: &Globals) -> Option<Value> {
        if let Some(value) = self.scopes.last_mut()?.stack.pop() {
            return Option::Some(value);
        }

        let value = self.nth_from_top(0, globals)?;
        self.scopes.last_mut()?.n_borrowed += 1;
        Option::Some(value)
    }

    fn whole_stack(&mut self, globals: &Globals) -> Vec<Value> {
        let mut result: Vec<Value> = Vec::new();
        for (scope_index, scope) in self.scopes.clone().iter().enumerate() {
            for _ in 0..scope.n_borrowed {
                result.pop();
            }

            if scope.create_borrowed_vars {
                let mut new_result = Vec::new();
                for (item_index, value) in result.iter().rev().enumerate() {
                    if let Some((_, new_value)) = scope.borrowed_vars.get(&(item_index as i64)) {
                        new_result.push(new_value.clone());
                    } else {
                        new_result.push(Value::Variable(self.create_borrowed_var(
                            scope_index,
                            item_index,
                            value.clone(),
                            globals,
                        )));
                    }
                }
                result = new_result;
            }

            for value in &scope.stack {
                result.push(value.clone());
            }
        }
        result
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

    pub fn stack_as_string(&mut self, globals: &Globals) -> String {
        let mut types = Vec::new();
        for value in self.whole_stack(globals) {
            types.push(type_of(&value, self, globals));
        }
        display_type_list(&types)
    }

    pub fn pop_of_type(
        &mut self,
        type_: Type,
        globals: &Globals,
        location: Location,
        lexer: &Lexer,
    ) -> Result<Value, String> {
        if let Some(value) = self.nth_from_top(0, globals) {
            if type_of(&value, self, globals) == type_ {
                return Result::Ok(self.pop(globals).expect("stack is checked to not be empty"));
            }
        }

        Result::Err(lexer.make_error_report(
            location,
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
        location: Location,
        lexer: &Lexer,
    ) -> Result<(Value, Value), String> {
        if let Some(value1) = self.nth_from_top(1, globals) {
            if let Some(value2) = self.nth_from_top(0, globals) {
                if type_of(&value1, self, globals) == type1
                    && type_of(&value2, self, globals) == type2
                {
                    let value2 = self
                        .pop(globals)
                        .expect("stack is checked to have 2 values");
                    let value1 = self
                        .pop(globals)
                        .expect("stack is checked to have 2 values");
                    return Result::Ok((value1, value2));
                }
            }
        }

        Result::Err(lexer.make_error_report(
            location,
            &format!(
                "expected ... {type1} {type2}, found {}",
                self.stack_as_string(globals)
            ),
        ))
    }

    pub fn pop_of_any_type(
        &mut self,
        globals: &Globals,
        location: Location,
        lexer: &Lexer,
    ) -> Result<Value, String> {
        if let Some(value) = self.pop(globals) {
            return Result::Ok(value);
        }

        Result::Err(lexer.make_error_report(
            location,
            &format!("expected ... A, found {}", self.stack_as_string(globals)),
        ))
    }

    pub fn pop2_of_any_type(
        &mut self,
        globals: &Globals,
        location: Location,
        lexer: &Lexer,
    ) -> Result<(Value, Value), String> {
        if self.nth_from_top(0, globals).is_some() && self.nth_from_top(1, globals).is_some() {
            let value2 = self
                .pop(globals)
                .expect("stack is checked to have 2 values");
            let value1 = self
                .pop(globals)
                .expect("stack is checked to have 2 values");
            return Result::Ok((value1, value2));
        }

        Result::Err(lexer.make_error_report(
            location,
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

#[derive(Clone, Copy, Debug)]
pub enum Logical {
    And,
    Or,
}

#[derive(Debug, Clone)]
pub struct Phi {
    pub result_var: i64,
    pub result_type: Type,
    pub case1: Value,
    pub case2: Value,
}

#[derive(Debug, Clone)]
pub enum Instruction {
    Arithemtic(Arithemtic, Value, Value, i64),
    Relational(Relational, Value, Value, i64),
    Logical(Logical, Value, Value, i64),
    Not(Value, i64),
    Print(Value),
    Exit(Value),
    Call(Value, Vec<Type>, Vec<Value>, Vec<Type>, Vec<i64>),
    If(Value, Scope, Scope, Vec<Phi>),
    Loop(Vec<Phi>, Scope),
}
