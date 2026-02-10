use crate::lex::Lexer;
use crate::lex::Location;

use crate::types::display_type;
use crate::types::display_type_list;
use crate::types::merge_types;
use crate::types::resolve_actual_fields;
use crate::types::resolve_actual_type;
use crate::types::resolve_types_phi;
use crate::types::resolve_types_scope;
use crate::types::resolve_types_value;
use crate::types::type_of;
use crate::types::Fields;
use crate::types::Type;

use jost_macros::ResolveTypes;

use std::collections::HashMap;

use core::panic;

#[derive(Clone, Debug)]
pub enum Value {
    IntLiteral(i64),
    Int32Literal(i32),
    BoolLiteral(bool),
    Tuple(Vec<Value>, Vec<Type>),
    Array(Vec<Value>, Type),
    Slice(Box<Value>, Box<Value>),
    Vec(Box<Value>, Box<Value>, Box<Value>),
    Type(Type),
    Variable(i64),
    Arg(i64),
    Global(String),
    Function(String),
    Zeroed(Type, Location),
    Undefined(Type, Location),
    Length(Box<Value>, Location),
    SizeOf(Type),
}

impl Value {
    pub fn unwrap_type(self) -> Type {
        match self {
            Value::Type(type_) => type_,
            _ => panic!("unwrap type assumed that value {self:?} is a type"),
        }
    }
}

pub struct Globals {
    pub global_types: HashMap<String, Type>,

    pub strings: Vec<String>,
    pub lambdas: Vec<Function>,
    pub functions: HashMap<String, Function>,

    pub type_vars: HashMap<i64, Type>,
    pub type_var_locations: HashMap<i64, Location>,
    last_type_var: i64,
}

impl Globals {
    pub fn new() -> Self {
        Self {
            global_types: HashMap::from([("__string_buf".to_owned(), Type::String)]),
            strings: Vec::new(),
            lambdas: Vec::new(),
            functions: HashMap::new(),
            type_vars: HashMap::new(),
            type_var_locations: HashMap::new(),
            last_type_var: -1,
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

    pub fn new_type_var(&mut self, location: Location) -> i64 {
        self.last_type_var += 1;
        self.type_var_locations.insert(self.last_type_var, location);
        self.last_type_var
    }
}

#[derive(Debug, Clone)]
pub struct Scope {
    pub stack: Vec<Value>,
    pub no_return: bool,

    pub n_borrowed: i64,

    pub create_borrowed_vars: bool,
    pub borrowed_vars: HashMap<i64, (i64, Value)>,

    pub ir: Vec<Instruction>,

    pub end: i64,
}

impl Scope {
    pub fn new(create_borrowed_vars: bool) -> Self {
        Scope {
            stack: Vec::new(),
            n_borrowed: 0,
            no_return: false,
            create_borrowed_vars,
            borrowed_vars: HashMap::new(),
            ir: Vec::new(),
            end: 0,
        }
    }
}

#[derive(Clone, Default)]
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
            if let Some((var, _)) = current_scope.borrowed_vars.get(&(next_n as i64)) {
                return Option::Some(Value::Variable(*var));
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
        self.scopes.push(Scope::new(create_borrowed_vars));
    }

    pub fn pop_scope(&mut self) -> Scope {
        self.scopes
            .pop()
            .expect("pop_scope excpects a scope to exist")
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
        display_type_list(&types, globals)
    }

    pub fn peek_of_type(
        &mut self,
        type_: &Type,
        globals: &mut Globals,
        offset_from_top: i64,
    ) -> Option<Value> {
        if let Some(value) = self.nth_from_top(offset_from_top, globals) {
            if merge_types(&type_of(&value, self, globals), type_, globals) {
                return Option::Some(value);
            }
        }
        Option::None
    }

    pub fn pop_of_type(
        &mut self,
        type_: &Type,
        globals: &mut Globals,
        location: Location,
        lexer: &Lexer,
    ) -> Result<Value, String> {
        if self.peek_of_type(type_, globals, 0).is_some() {
            return Result::Ok(self.pop(globals).expect("stack is checked to not be empty"));
        }

        Result::Err(lexer.make_error_report(
            location,
            &format!(
                "expected ... {}, found {}",
                display_type(type_, globals),
                self.stack_as_string(globals)
            ),
        ))
    }

    pub fn pop2_of_type(
        &mut self,
        type1: Type,
        type2: Type,
        globals: &mut Globals,
        location: Location,
        lexer: &Lexer,
    ) -> Result<(Value, Value), String> {
        if self.peek_of_type(&type1, globals, 1).is_some()
            && self.peek_of_type(&type2, globals, 0).is_some()
        {
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
            &format!(
                "expected ... {} {}, found {}",
                display_type(&type1, globals),
                display_type(&type2, globals),
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

    pub fn pop3_of_any_type(
        &mut self,
        globals: &Globals,
        location: Location,
        lexer: &Lexer,
    ) -> Result<[Value; 3], String> {
        if self.nth_from_top(0, globals).is_some()
            && self.nth_from_top(1, globals).is_some()
            && self.nth_from_top(2, globals).is_some()
        {
            let value3 = self
                .pop(globals)
                .expect("stack is checked to have 3 values");
            let value2 = self
                .pop(globals)
                .expect("stack is checked to have 3 values");
            let value1 = self
                .pop(globals)
                .expect("stack is checked to have 3 values");
            return Result::Ok([value1, value2, value3]);
        }

        Result::Err(lexer.make_error_report(
            location,
            &format!(
                "expected ... A A A, found {}",
                self.stack_as_string(globals)
            ),
        ))
    }

    pub fn peek_n_of_types(
        &mut self,
        types: &[Type],
        globals: &Globals,
        offset_from_top: i64,
    ) -> Option<Vec<Value>> {
        types
            .iter()
            .enumerate()
            .map(|(i, arg_type)| {
                self.nth_from_top(offset_from_top + (types.len() - i - 1) as i64, globals)
                    .filter(|value| type_of(value, self, globals) == *arg_type)
            })
            .collect()
    }

    pub fn pop_signature(
        &mut self,
        globals: &mut Globals,
        lexer: &Lexer,
        location: Location,
    ) -> Result<(Vec<Type>, Vec<Type>), String> {
        if let Some(Value::Array(result_types, arg_types_type)) = self.nth_from_top(0, globals) {
            if let Some(Value::Array(arg_types, result_types_type)) = self.nth_from_top(1, globals)
            {
                if merge_types(&arg_types_type, &Type::Typ, globals)
                    && merge_types(&result_types_type, &Type::Typ, globals)
                {
                    self.pop(globals).expect("stack is checked above");
                    self.pop(globals).expect("stack is checked above");

                    let arg_types: Vec<Type> = arg_types
                        .into_iter()
                        .map(|type_| type_.unwrap_type())
                        .collect();
                    let result_types: Vec<Type> = result_types
                        .into_iter()
                        .map(|type_| type_.unwrap_type())
                        .collect();

                    return Result::Ok((arg_types, result_types));
                }
            }
        }

        Result::Err(lexer.make_error_report(
            location,
            &format!(
                "Expected Type n Array Type m Array, found {}",
                self.stack_as_string(globals)
            ),
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

pub trait ResolveTypes {
    fn resolve_types(
        self,
        function: &mut Function,
        globals: &mut Globals,
        lexer: &Lexer,
    ) -> Result<Self, String>
    where
        Self: Sized;
}

#[derive(Debug, Clone, Default, ResolveTypes)]
pub enum Instruction {
    #[default]
    Bogus,

    Arithemtic(Arithemtic, Value, Value, i64),
    Relational(Relational, Value, Value, i64),
    Relational32(Relational, Value, Value, i64),
    Logical(Logical, Value, Value, i64),
    Not(Value, i64),

    Alloca(Type, i64),
    AllocaN(Type, Value, i64),
    Load(Value, Type, i64),
    Store(Value, Type, Value),

    Memcopy(Value, Value, Value),

    Malloc(Value, i64),
    Realloc(Value, Value, i64),
    Free(Value),

    CheckNoDestructor(Type, Location),
    Clone(Value, Type, i64, Location),
    Destroy(Value, Type, Location),

    InsertValue(Value, Type, Value, Type, i64, i64),
    ExtractValue(Value, Type, Type, i64, i64),

    InsertValueDyn(Value, Type, Value, Type, Value, i64),
    ExtractValueDyn(Value, Type, Type, Value, i64),

    GetElementPtr(Type, Value, Value, i64),
    GetNeighbourPtr(Type, Value, Value, i64),

    GetField(Value, Fields, Type, String, i64),
    SetField(Value, Fields, Value, Type, String, i64),
    GetFieldPtr(Value, Fields, Type, String, i64),

    Bitcast(Value, Type, Type, i64),

    Print(Value, Type),
    Input(i64, Type, Location),

    Putstr(Value),
    Printf(Value, Vec<Value>),
    GetsS(Value, Value, Option<i64>),
    Strcmp(Value, Value, i64),
    Exit(Value),

    Call(Value, Vec<Type>, Vec<Value>, Vec<Type>, Vec<i64>),

    If(Value, Scope, Scope, Vec<Phi>),
    Loop(Vec<Phi>, Scope),
    While(Vec<Phi>, Scope, Value, Scope),
    Return(Vec<Value>, Vec<Type>),
}
