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
    FnPtr(Vec<Type>, Vec<Type>),
    List, // TODO: implement lists of type other than Type
    Typ,
    TypVar(i64),
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
    Zeroed(Type),
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

    fn resolve_types(self, globals: &Globals, lexer: &Lexer) -> Result<Self, String> {
        Result::Ok(match self {
            Self::ListLiteral(types) => Self::ListLiteral(
                types
                    .iter()
                    .map(|type_| globals.resolve_actual_type(type_, lexer))
                    .collect::<Result<Vec<Type>, String>>()?,
            ),
            Self::Type(type_) => Self::Type(globals.resolve_actual_type(&type_, lexer)?),
            Self::Zeroed(type_) => Self::Zeroed(globals.resolve_actual_type(&type_, lexer)?),
            _ => self,
        })
    }
}

pub struct Globals {
    global_types: HashMap<String, Type>,

    pub strings: Vec<String>,
    pub lambdas: Vec<Function>,

    type_vars: HashMap<i64, Type>,
    type_var_locations: HashMap<i64, Location>,
    last_type_var: i64,
}

impl Globals {
    pub fn new() -> Self {
        Self {
            global_types: HashMap::new(),
            strings: Vec::new(),
            lambdas: Vec::new(),
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
            Type::FnPtr(arg_types, result_types) => {
                format!(
                    "fn ({}) -> ({})",
                    self.display_type_list(&arg_types, globals),
                    self.display_type_list(&result_types, globals)
                )
            }
            Type::List => "List".to_owned(),
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
        display_type_list(&types, globals)
    }

    pub fn resolve_types(&self, globals: &Globals, lexer: &Lexer) -> Result<Self, String> {
        let mut new_self = self.clone();
        for instruction in &mut new_self
            .scopes
            .last_mut()
            .expect("resolve_types expects a scope to exist")
            .ir
        {
            *instruction = mem::take(instruction).resolve_types(globals, lexer)?;
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
        Value::Type(_) => Type::Typ,
        Value::Variable(index) => globals.resolve_type(&function.var_types[index]),
        Value::Arg(index) => globals.resolve_type(&function.arg_types[*index as usize]),
        Value::Global(name) => globals.resolve_type(&globals.global_types[name]),
        Value::Zeroed(type_) => globals.resolve_type(type_),
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
    fn resolve_types(self, globals: &Globals, lexer: &Lexer) -> Result<Self, String> {
        Result::Ok(Phi {
            result_var: self.result_var,
            result_type: globals.resolve_type(&self.result_type),
            case1: self.case1.resolve_types(globals, lexer)?,
            case2: self.case2.resolve_types(globals, lexer)?,
        })
    }
}

#[derive(Debug, Clone, Default)]
pub enum Instruction {
    #[default]
    Bogus,

    Arithemtic(Arithemtic, Value, Value, i64),
    Relational(Relational, Value, Value, i64),
    Logical(Logical, Value, Value, i64),
    Not(Value, i64),

    Putstr(Value),
    Printf(Value, Vec<Value>),
    Input(Type, i64),
    Exit(Value),

    Call(Value, Vec<Type>, Vec<Value>, Vec<Type>, Vec<i64>),

    If(Value, Scope, Scope, Vec<Phi>),
    Loop(Vec<Phi>, Scope),
    While(Vec<Phi>, Scope, Value, Scope),
    Return(Vec<Value>, Vec<Type>),
}

impl Instruction {
    fn resolve_types(self, globals: &Globals, lexer: &Lexer) -> Result<Self, String> {
        Result::Ok(match self {
            Self::Bogus => panic!("bogus instruction got to type resolution"),
            Self::Arithemtic(op, lhs, rhs, result_var) => Self::Arithemtic(
                op,
                lhs.resolve_types(globals, lexer)?,
                rhs.resolve_types(globals, lexer)?,
                result_var,
            ),
            Self::Relational(op, lhs, rhs, result_var) => Self::Relational(
                op,
                lhs.resolve_types(globals, lexer)?,
                rhs.resolve_types(globals, lexer)?,
                result_var,
            ),
            Self::Logical(op, lhs, rhs, result_var) => Self::Logical(
                op,
                lhs.resolve_types(globals, lexer)?,
                rhs.resolve_types(globals, lexer)?,
                result_var,
            ),
            Self::Not(value, result_var) => {
                Self::Not(value.resolve_types(globals, lexer)?, result_var)
            }
            Self::Putstr(value) => Self::Putstr(value.resolve_types(globals, lexer)?),
            Self::Printf(fmt_string, args) => Self::Printf(
                fmt_string.resolve_types(globals, lexer)?,
                args.into_iter()
                    .map(|arg| arg.resolve_types(globals, lexer))
                    .collect::<Result<Vec<Value>, String>>()?,
            ),
            Self::Input(type_, result_var) => {
                Self::Input(globals.resolve_actual_type(&type_, lexer)?, result_var)
            }
            Self::Exit(value) => Self::Exit(value.resolve_types(globals, lexer)?),
            Self::Call(fn_ptr, arg_types, arg_values, result_types, result_vars) => {
                let mut new_arg_types = Vec::with_capacity(arg_types.len());
                for arg_type in arg_types {
                    new_arg_types.push(globals.resolve_actual_type(&arg_type, lexer)?);
                }

                let mut new_result_types = Vec::with_capacity(result_types.len());
                for result_type in result_types {
                    new_result_types.push(globals.resolve_actual_type(&result_type, lexer)?);
                }

                Self::Call(
                    fn_ptr.resolve_types(globals, lexer)?,
                    new_arg_types,
                    arg_values,
                    new_result_types,
                    result_vars,
                )
            }
            Self::Return(values, types) => {
                let mut new_types = Vec::with_capacity(types.len());
                for type_ in types {
                    new_types.push(globals.resolve_actual_type(&type_, lexer)?);
                }
                Self::Return(
                    values
                        .into_iter()
                        .map(|value| value.resolve_types(globals, lexer))
                        .collect::<Result<Vec<Value>, String>>()?,
                    new_types,
                )
            }
            Self::If(condition, then_scope, else_scope, phis) => {
                let mut then_scope = then_scope;
                for instruction in &mut then_scope.ir {
                    *instruction = mem::take(instruction).resolve_types(globals, lexer)?;
                }

                let mut else_scope = else_scope;
                for instruction in &mut else_scope.ir {
                    *instruction = mem::take(instruction).resolve_types(globals, lexer)?;
                }

                let mut new_phis = Vec::with_capacity(phis.len());
                for phi in phis {
                    new_phis.push(phi.resolve_types(globals, lexer)?)
                }

                Self::If(
                    condition.resolve_types(globals, lexer)?,
                    then_scope,
                    else_scope,
                    new_phis,
                )
            }
            Self::Loop(phis, body_scope) => {
                let mut body_scope = body_scope;
                for instruction in &mut body_scope.ir {
                    *instruction = mem::take(instruction).resolve_types(globals, lexer)?;
                }

                let mut new_phis = Vec::with_capacity(phis.len());
                for phi in phis {
                    new_phis.push(phi.resolve_types(globals, lexer)?)
                }

                Self::Loop(new_phis, body_scope)
            }
            Self::While(phis, test_scope, test, body_scope) => {
                let mut test_scope = test_scope;
                for instruction in &mut test_scope.ir {
                    *instruction = mem::take(instruction).resolve_types(globals, lexer)?;
                }

                let mut body_scope = body_scope;
                for instruction in &mut body_scope.ir {
                    *instruction = mem::take(instruction).resolve_types(globals, lexer)?;
                }

                let mut new_phis = Vec::with_capacity(phis.len());
                for phi in phis {
                    new_phis.push(phi.resolve_types(globals, lexer)?)
                }

                Self::While(
                    new_phis,
                    test_scope,
                    test.resolve_types(globals, lexer)?,
                    body_scope,
                )
            }
        })
    }
}
