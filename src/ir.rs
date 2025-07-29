use crate::lex::Lexer;
use crate::lex::Location;

use std::collections::HashMap;

use core::panic;
use std::iter::zip;
use std::mem;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Type {
    Int,
    Int32,
    Bool,
    String,
    Ptr(Box<Type>),
    FnPtr(Vec<Type>, Vec<Type>),
    Tuple(Vec<Type>),
    Typ,
    TypVar(i64),
}

#[derive(Clone, Debug)]
pub enum Value {
    IntLiteral(i64),
    BoolLiteral(bool),
    Tuple(Vec<Value>, Vec<Type>),
    Type(Type),
    Variable(i64),
    Arg(i64),
    Global(String),
    Function(String),
    Zeroed(Type),
    Undefined,
    Length(Box<Value>, Location),
}

impl Value {
    pub fn unwrap_type(self) -> Type {
        match self {
            Value::Type(type_) => type_,
            _ => panic!("unwrap type assumed that value {self:?} is a type"),
        }
    }

    fn resolve_types(
        self,
        function: &mut Function,
        globals: &Globals,
        lexer: &Lexer,
    ) -> Result<Self, String> {
        Result::Ok(match self {
            Self::Tuple(values, types) => {
                let values = values
                    .into_iter()
                    .map(|value| value.resolve_types(function, globals, lexer))
                    .collect::<Result<Vec<Value>, String>>()?;
                let self_type = Type::Tuple(
                    types
                        .iter()
                        .map(|type_| globals.resolve_actual_type(type_, lexer))
                        .collect::<Result<Vec<Type>, String>>()?,
                );

                let mut built_tuple = Value::Undefined;
                for (i, value) in values.into_iter().enumerate() {
                    let next_var = function.new_var(self_type.clone());
                    function.add_instruction(Instruction::InsertValue(
                        built_tuple,
                        self_type.clone(),
                        value,
                        i as i64,
                        next_var,
                    ));
                    built_tuple = Self::Variable(next_var);
                }
                built_tuple
            }
            Self::Type(type_) => Self::Type(globals.resolve_actual_type(&type_, lexer)?),
            Self::Zeroed(type_) => Self::Zeroed(globals.resolve_actual_type(&type_, lexer)?),
            Self::Length(value, location) => {
                let value = value.resolve_types(function, globals, lexer)?;
                let type_ = type_of(&value, function, globals);
                if let Type::Tuple(types) = type_ {
                    Self::IntLiteral(types.len() as i64)
                } else {
                    return Result::Err(lexer.make_error_report(
                        location,
                        &format!("expected Tuple, found {}", display_type(&type_, globals)),
                    ));
                }
            }
            _ => self,
        })
    }
}

pub struct Globals {
    global_types: HashMap<String, Type>,

    pub strings: Vec<String>,
    pub lambdas: Vec<Function>,
    pub functions: HashMap<String, Function>,

    type_vars: HashMap<i64, Type>,
    type_var_locations: HashMap<i64, Location>,
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

    pub fn resolve_type(&self, type_: &Type) -> Type {
        match type_ {
            Type::TypVar(i) => self.type_vars.get(i).unwrap_or(type_).clone(),
            Type::FnPtr(arg_types, result_types) => Type::FnPtr(
                arg_types
                    .iter()
                    .map(|arg_type| self.resolve_type(arg_type))
                    .collect(),
                result_types
                    .iter()
                    .map(|result_type| self.resolve_type(result_type))
                    .collect(),
            ),
            _ => type_.clone(),
        }
    }

    fn resolve_actual_type(&self, type_: &Type, lexer: &Lexer) -> Result<Type, String> {
        let resolved_type = self.resolve_type(type_);
        if let Type::TypVar(i) = resolved_type {
            Result::Err(lexer.make_error_report(self.type_var_locations[&i], "Ambigous type"))
        } else {
            Result::Ok(resolved_type)
        }
    }

    pub fn merge_types(&mut self, type1: &Type, type2: &Type) -> bool {
        match type1 {
            Type::TypVar(i) => {
                if let Some(new_type1) = self.type_vars.get(i) {
                    self.merge_types(&new_type1.clone(), type2)
                } else {
                    if type2 != type1 {
                        self.type_vars.insert(*i, type2.clone());
                    }
                    true
                }
            }
            Type::FnPtr(arg_types1, result_types1) => {
                if let Type::FnPtr(arg_types2, result_types2) = type2 {
                    let arg_types_match = self.merge_type_lists(arg_types1, arg_types2);
                    let result_types_match = self.merge_type_lists(result_types1, result_types2);
                    arg_types_match && result_types_match
                } else {
                    false
                }
            }
            _ => match type2 {
                Type::TypVar(_) => self.merge_types(type2, type1),
                Type::FnPtr(_, _) => false,
                _ => type1 == type2,
            },
        }
    }

    pub fn merge_type_lists(&mut self, types1: &[Type], types2: &[Type]) -> bool {
        if types1.len() == types2.len() {
            let mut types_match = true;
            for (type1, type2) in zip(types1, types2) {
                if !self.merge_types(type1, type2) {
                    types_match = false;
                }
            }
            types_match
        } else {
            false
        }
    }

    pub fn new_type_var(&mut self, location: Location) -> i64 {
        let type_var = self.last_type_var;
        self.last_type_var += 1;

        self.type_var_locations.insert(type_var, location);

        type_var
    }
}

struct DisplayTypesContext {
    type_var_numbers: HashMap<i64, i64>,
    last_type_var_number: i64,
}

impl DisplayTypesContext {
    fn new() -> Self {
        Self {
            type_var_numbers: HashMap::new(),
            last_type_var_number: -1,
        }
    }

    fn type_var_number(&mut self, type_var: i64) -> i64 {
        self.type_var_numbers
            .get(&type_var)
            .cloned()
            .unwrap_or_else(|| {
                self.last_type_var_number += 1;
                self.type_var_numbers
                    .insert(type_var, self.last_type_var_number);
                self.last_type_var_number
            })
    }

    fn type_var_name(&mut self, type_var: i64) -> String {
        let type_var_number = self.type_var_number(type_var);
        ((b'A' + (type_var_number % 26) as u8) as char).to_string()
            + &"*".repeat(type_var_number as usize / 26)
    }

    fn display_type(&mut self, type_: &Type, globals: &Globals) -> String {
        match globals.resolve_type(type_) {
            Type::Int => "Int".to_owned(),
            Type::Int32 => "Int32".to_owned(),
            Type::Bool => "Bool".to_owned(),
            Type::String => "String".to_owned(),
            Type::Ptr(type_) => format!("{} Ptr", self.display_type(type_.as_ref(), globals)),
            Type::FnPtr(arg_types, result_types) => {
                format!(
                    "fn ({}) -> ({})",
                    self.display_type_list(&arg_types, globals),
                    self.display_type_list(&result_types, globals)
                )
            }
            Type::Tuple(types) => {
                "(".to_owned() + &self.display_type_list(&types, globals) + ") Tuple"
            }
            Type::Typ => "Type".to_owned(),
            Type::TypVar(i) => self.type_var_name(i),
        }
    }

    fn display_type_list(&mut self, types: &[Type], globals: &Globals) -> String {
        let mut s = "".to_owned();
        for (i, type_) in types.iter().enumerate() {
            if i > 0 {
                s += " ";
            }
            s += &self.display_type(type_, globals);
        }
        s
    }
}

pub fn display_type(type_: &Type, globals: &Globals) -> String {
    DisplayTypesContext::new().display_type(type_, globals)
}

pub fn display_type_list(types: &[Type], globals: &Globals) -> String {
    DisplayTypesContext::new().display_type_list(types, globals)
}

#[derive(Debug, Clone)]
pub struct Scope {
    pub stack: Vec<Value>,
    pub no_return: bool,

    pub n_borrowed: i64,

    create_borrowed_vars: bool,
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

    pub fn resolve_types(
        &self,
        function: &mut Function,
        globals: &mut Globals,
        lexer: &Lexer,
    ) -> Result<Self, String> {
        function.new_scope(self.create_borrowed_vars);
        for instruction in self.ir.clone() {
            instruction.resolve_types(function, globals, lexer)?;
        }

        let mut new_self = function.scopes.pop().expect("scope is created above");
        new_self.no_return = self.no_return;
        Result::Ok(new_self)
    }
}

#[derive(Clone)]
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

    pub fn resolve_types(&mut self, globals: &mut Globals, lexer: &Lexer) -> Result<Self, String> {
        let mut new_self = self.clone();
        for scope in mem::take(&mut new_self.scopes) {
            let new_scope = scope.resolve_types(&mut new_self, globals, lexer)?;
            new_self.scopes.push(new_scope);
        }
        Result::Ok(new_self)
    }

    pub fn pop_of_type(
        &mut self,
        type_: Type,
        globals: &mut Globals,
        location: Location,
        lexer: &Lexer,
    ) -> Result<Value, String> {
        if let Some(value) = self.nth_from_top(0, globals) {
            if globals.merge_types(&type_of(&value, self, globals), &type_) {
                return Result::Ok(self.pop(globals).expect("stack is checked to not be empty"));
            }
        }

        Result::Err(lexer.make_error_report(
            location,
            &format!(
                "expected ... {}, found {}",
                display_type(&type_, globals),
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
        if let Some(value1) = self.nth_from_top(1, globals) {
            if let Some(value2) = self.nth_from_top(0, globals) {
                if globals.merge_types(&type_of(&value1, self, globals), &type1)
                    && globals.merge_types(&type_of(&value2, self, globals), &type2)
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

    pub fn pop_signature(
        &mut self,
        globals: &mut Globals,
        lexer: &Lexer,
        location: Location,
    ) -> Result<(Vec<Type>, Vec<Type>), String> {
        if let Some(Value::Tuple(result_types, result_type_types)) = self.nth_from_top(0, globals) {
            if let Some(Value::Tuple(arg_types, arg_type_types)) = self.nth_from_top(1, globals) {
                if arg_type_types
                    .iter()
                    .all(|type_| globals.merge_types(type_, &Type::Typ))
                    && result_type_types
                        .iter()
                        .all(|type_| globals.merge_types(type_, &Type::Typ))
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
                "Expected Type n Array Type m Array, {}",
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

pub fn type_of(value: &Value, function: &Function, globals: &Globals) -> Type {
    match value {
        Value::IntLiteral(_) | Value::Length(_, _) => Type::Int,
        Value::BoolLiteral(_) => Type::Bool,
        Value::Tuple(_, types) => Type::Tuple(types.clone()),
        Value::Type(_) => Type::Typ,
        Value::Variable(index) => globals.resolve_type(&function.var_types[index]),
        Value::Arg(index) => globals.resolve_type(&function.arg_types[*index as usize]),
        Value::Global(name) => globals.resolve_type(&globals.global_types[name]),
        Value::Function(name) => Type::FnPtr(
            globals.functions[name]
                .arg_types
                .iter()
                .map(|type_| globals.resolve_type(type_))
                .collect(),
            globals.functions[name]
                .result_types
                .iter()
                .map(|type_| globals.resolve_type(type_))
                .collect(),
        ),
        Value::Zeroed(type_) => globals.resolve_type(type_),
        Value::Undefined => todo!("make undefined know its type"),
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

impl Phi {
    fn resolve_types(
        self,
        function: &mut Function,
        globals: &mut Globals,
        lexer: &Lexer,
    ) -> Result<Self, String> {
        Result::Ok(Phi {
            result_var: self.result_var,
            result_type: globals.resolve_type(&self.result_type),
            case1: self.case1.resolve_types(function, globals, lexer)?,
            case2: self.case2.resolve_types(function, globals, lexer)?,
        })
    }
}

#[derive(Debug, Clone, Default)]
pub enum Instruction {
    #[default]
    Bogus,

    Arithemtic(Arithemtic, Value, Value, i64),
    Relational(Relational, Value, Value, i64),
    Relational32(Relational, Value, Value, i64),
    Logical(Logical, Value, Value, i64),
    Not(Value, i64),

    Alloca(Value, Type, i64),
    Load(Value, Type, i64),
    Store(Value, Type, Value),

    InsertValue(Value, Type, Value, i64, i64),
    ExtractValue(Value, Type, i64, i64),

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

fn resolve_print(
    value: Value,
    type_: Type,
    function: &mut Function,
    globals: &mut Globals,
    lexer: &Lexer,
) -> Result<(), String> {
    match type_.clone() {
        Type::Int => {
            let value = value.resolve_types(function, globals, lexer)?;
            function.add_instruction(Instruction::Printf(
                Value::Global(globals.new_string("%lld\n")),
                [value].to_vec(),
            ))
        }
        Type::Int32 => {
            let value = value.resolve_types(function, globals, lexer)?;
            function.add_instruction(Instruction::Printf(
                Value::Global(globals.new_string("%d\n")),
                [value].to_vec(),
            ))
        }
        Type::String => {
            let value = value.resolve_types(function, globals, lexer)?;
            function.add_instruction(Instruction::Putstr(value))
        }
        Type::Bool => {
            let var = function.new_var(Type::String);
            let value = value.resolve_types(function, globals, lexer)?;
            function.add_instruction(Instruction::If(
                value,
                Scope::new(false),
                Scope::new(false),
                Vec::from([Phi {
                    result_var: var,
                    result_type: Type::String,
                    case1: Value::Global(globals.new_string("true")),
                    case2: Value::Global(globals.new_string("false")),
                }]),
            ));
            function.add_instruction(Instruction::Putstr(Value::Variable(var)));
        }
        Type::Tuple(types) => {
            let value = value.resolve_types(function, globals, lexer)?;
            for (i, element_type) in types.into_iter().enumerate() {
                let element_var = function.new_var(element_type.clone());
                function.add_instruction(Instruction::ExtractValue(
                    value.clone(),
                    type_.clone(),
                    i as i64,
                    element_var,
                ));
                resolve_print(
                    Value::Variable(element_var),
                    element_type,
                    function,
                    globals,
                    lexer,
                )?;
            }
        }
        Type::FnPtr(_, _) | Type::Ptr(_) => function.add_instruction(Instruction::Putstr(
            Value::Global(globals.new_string(&display_type(&type_, globals))),
        )),
        Type::Typ => {
            if let Value::Type(type_) = value.resolve_types(function, globals, lexer)? {
                function.add_instruction(Instruction::Putstr(Value::Global(
                    globals.new_string(&display_type(&type_, globals)),
                )));
            } else {
                panic!("Only Value::Type can be pf type Type");
            }
        }
        Type::TypVar(_) => panic!("resolve_actual_type returned type var"),
    }
    Result::Ok(())
}

fn resolve_input(
    type_: Type,
    result_var: i64,
    location: Location,
    function: &mut Function,
    globals: &mut Globals,
    lexer: &Lexer,
) -> Result<(), String> {
    match globals.resolve_actual_type(&type_, lexer)? {
        Type::Int => todo!("implement input for ints"),
        Type::Int32 => todo!("implement input for int32s"),
        Type::String => function.add_instruction(Instruction::GetsS(
            Value::Global("__string_buf".to_owned()),
            Value::IntLiteral(256),
            Option::Some(result_var),
        )),
        Type::Bool => {
            let strcmp_result = function.new_var(Type::Int32);
            function.add_instruction(Instruction::GetsS(
                Value::Global("__string_buf".to_owned()),
                Value::IntLiteral(256),
                Option::None,
            ));
            function.add_instruction(Instruction::Strcmp(
                Value::Global("__string_buf".to_owned()),
                Value::Global(globals.new_string("true")),
                strcmp_result,
            ));
            function.add_instruction(Instruction::Relational32(
                Relational::Eq,
                Value::Variable(strcmp_result),
                Value::IntLiteral(0),
                result_var,
            ));
        }
        Type::Tuple(_) => todo!("input lists"),
        Type::Ptr(_) | Type::FnPtr(_, _) | Type::Typ => {
            return Result::Err(lexer.make_error_report(
                location,
                &format!("can't input a {}", display_type(&type_, globals)),
            ))
        }
        Type::TypVar(_) => panic!("resolve_actual_type returned type var"),
    }
    Result::Ok(())
}

impl Instruction {
    fn resolve_types(
        self,
        function: &mut Function,
        globals: &mut Globals,
        lexer: &Lexer,
    ) -> Result<(), String> {
        match self {
            Self::Bogus => panic!("bogus instruction got to type resolution"),
            Self::Arithemtic(op, lhs, rhs, result_var) => {
                let lhs = lhs.resolve_types(function, globals, lexer)?;
                let rhs = rhs.resolve_types(function, globals, lexer)?;
                function.add_instruction(Self::Arithemtic(op, lhs, rhs, result_var))
            }
            Self::Relational(op, lhs, rhs, result_var) => {
                let lhs = lhs.resolve_types(function, globals, lexer)?;
                let rhs = rhs.resolve_types(function, globals, lexer)?;
                function.add_instruction(Self::Relational(op, lhs, rhs, result_var))
            }
            Self::Relational32(op, lhs, rhs, result_var) => {
                let lhs = lhs.resolve_types(function, globals, lexer)?;
                let rhs = rhs.resolve_types(function, globals, lexer)?;
                function.add_instruction(Self::Relational32(op, lhs, rhs, result_var))
            }
            Self::Logical(op, lhs, rhs, result_var) => {
                let lhs = lhs.resolve_types(function, globals, lexer)?;
                let rhs = rhs.resolve_types(function, globals, lexer)?;
                function.add_instruction(Self::Logical(op, lhs, rhs, result_var))
            }
            Self::Not(value, result_var) => {
                let value = value.resolve_types(function, globals, lexer)?;
                function.add_instruction(Self::Not(value, result_var))
            }
            Self::Alloca(value, type_, result_var) => {
                let value = value.resolve_types(function, globals, lexer)?;
                function.add_instruction(Self::Alloca(
                    value,
                    globals.resolve_actual_type(&type_, lexer)?,
                    result_var,
                ))
            }
            Self::Load(ptr, type_, result_var) => {
                let ptr = ptr.resolve_types(function, globals, lexer)?;
                function.add_instruction(Self::Load(
                    ptr,
                    globals.resolve_actual_type(&type_, lexer)?,
                    result_var,
                ))
            }
            Self::Store(ptr, type_, value) => {
                let ptr = ptr.resolve_types(function, globals, lexer)?;
                let value = value.resolve_types(function, globals, lexer)?;
                function.add_instruction(Self::Store(
                    ptr,
                    globals.resolve_actual_type(&type_, lexer)?,
                    value,
                ))
            }
            Self::InsertValue(tuple, tuple_type, value, index, result_var) => {
                let tuple = tuple.resolve_types(function, globals, lexer)?;
                let value = value.resolve_types(function, globals, lexer)?;
                function.add_instruction(Self::InsertValue(
                    tuple,
                    globals.resolve_actual_type(&tuple_type, lexer)?,
                    value,
                    index,
                    result_var,
                ))
            }
            Self::ExtractValue(tuple, tuple_type, index, result_var) => {
                let tuple = tuple.resolve_types(function, globals, lexer)?;
                function.add_instruction(Self::ExtractValue(
                    tuple,
                    globals.resolve_actual_type(&tuple_type, lexer)?,
                    index,
                    result_var,
                ))
            }
            Self::Print(value, type_) => resolve_print(value, type_, function, globals, lexer)?,
            Self::Putstr(value) => {
                let value = value.resolve_types(function, globals, lexer)?;
                function.add_instruction(Self::Putstr(value))
            }
            Self::Printf(fmt_string, args) => {
                let fmt_string = fmt_string.resolve_types(function, globals, lexer)?;
                let args = args
                    .into_iter()
                    .map(|arg| arg.resolve_types(function, globals, lexer))
                    .collect::<Result<Vec<Value>, String>>()?;
                function.add_instruction(Self::Printf(fmt_string, args))
            }
            Self::Input(result_var, type_, location) => {
                resolve_input(type_, result_var, location, function, globals, lexer)?
            }
            Self::GetsS(buf, size, result_var) => {
                let buf = buf.resolve_types(function, globals, lexer)?;
                let size = size.resolve_types(function, globals, lexer)?;
                function.add_instruction(Self::GetsS(buf, size, result_var))
            }
            Self::Strcmp(lhs, rhs, result_var) => {
                let lhs = lhs.resolve_types(function, globals, lexer)?;
                let rhs = rhs.resolve_types(function, globals, lexer)?;
                function.add_instruction(Self::Strcmp(lhs, rhs, result_var))
            }
            Self::Exit(value) => {
                let value = value.resolve_types(function, globals, lexer)?;
                function.add_instruction(Self::Exit(value))
            }
            Self::Call(fn_ptr, arg_types, arg_values, result_types, result_vars) => {
                let fn_ptr = fn_ptr.resolve_types(function, globals, lexer)?;
                let mut new_arg_types = Vec::with_capacity(arg_types.len());
                for arg_type in arg_types {
                    new_arg_types.push(globals.resolve_actual_type(&arg_type, lexer)?);
                }

                let mut new_result_types = Vec::with_capacity(result_types.len());
                for result_type in result_types {
                    new_result_types.push(globals.resolve_actual_type(&result_type, lexer)?);
                }

                function.add_instruction(Self::Call(
                    fn_ptr,
                    new_arg_types,
                    arg_values,
                    new_result_types,
                    result_vars,
                ))
            }
            Self::Return(values, types) => {
                let mut new_types = Vec::with_capacity(types.len());
                for type_ in types {
                    new_types.push(globals.resolve_actual_type(&type_, lexer)?);
                }

                let values = values
                    .into_iter()
                    .map(|value| value.resolve_types(function, globals, lexer))
                    .collect::<Result<Vec<Value>, String>>()?;

                function.add_instruction(Self::Return(values, new_types))
            }
            Self::If(condition, then_scope, else_scope, phis) => {
                let mut new_phis = Vec::with_capacity(phis.len());
                for phi in phis {
                    new_phis.push(phi.resolve_types(function, globals, lexer)?)
                }

                let instruction = Self::If(
                    condition.resolve_types(function, globals, lexer)?,
                    then_scope.resolve_types(function, globals, lexer)?,
                    else_scope.resolve_types(function, globals, lexer)?,
                    new_phis,
                );
                function.add_instruction(instruction);
            }
            Self::Loop(phis, body_scope) => {
                let mut new_phis = Vec::with_capacity(phis.len());
                for phi in phis {
                    new_phis.push(phi.resolve_types(function, globals, lexer)?)
                }

                let instruction = Self::Loop(
                    new_phis,
                    body_scope.resolve_types(function, globals, lexer)?,
                );
                function.add_instruction(instruction);
            }
            Self::While(phis, test_scope, test, body_scope) => {
                let mut new_phis = Vec::with_capacity(phis.len());
                for phi in phis {
                    new_phis.push(phi.resolve_types(function, globals, lexer)?)
                }

                let instruction = Self::While(
                    new_phis,
                    test_scope.resolve_types(function, globals, lexer)?,
                    test.resolve_types(function, globals, lexer)?,
                    body_scope.resolve_types(function, globals, lexer)?,
                );
                function.add_instruction(instruction);
            }
        };
        Result::Ok(())
    }
}
