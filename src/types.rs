use crate::lex::Lexer;
use crate::lex::Location;

use crate::ir::Function;
use crate::ir::Globals;
use crate::ir::Instruction;
use crate::ir::Phi;
use crate::ir::Relational;
use crate::ir::Scope;
use crate::ir::Value;

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

fn resolve_types_value(
    value: Value,
    function: &mut Function,
    globals: &Globals,
    lexer: &Lexer,
) -> Result<Value, String> {
    Result::Ok(match value {
        Value::Tuple(values, types) => {
            let values = values
                .into_iter()
                .map(|value| resolve_types_value(value, function, globals, lexer))
                .collect::<Result<Vec<Value>, String>>()?;
            let self_type = Type::Tuple(
                types
                    .iter()
                    .map(|type_| resolve_actual_type(type_, globals, lexer))
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
                built_tuple = Value::Variable(next_var);
            }
            built_tuple
        }
        Value::Type(type_) => Value::Type(resolve_actual_type(&type_, globals, lexer)?),
        Value::Zeroed(type_, location) => match resolve_actual_type(&type_, globals, lexer)? {
            Type::Int => Value::IntLiteral(0),
            Type::Int32 => Value::Int32Literal(0),
            Type::Bool => Value::BoolLiteral(false),
            Type::String | Type::Ptr(_) | Type::FnPtr(_, _) => {
                return Result::Err(lexer.make_error_report(
                    location,
                    &format!(
                        "Value of type {} can't be null",
                        display_type(&type_, globals)
                    ),
                ))
            }
            Type::Tuple(types) => Value::Tuple(
                types
                    .iter()
                    .map(|type_| {
                        resolve_types_value(
                            Value::Zeroed(type_.clone(), location),
                            function,
                            globals,
                            lexer,
                        )
                    })
                    .collect::<Result<Vec<Value>, String>>()?,
                types,
            ),
            Type::Typ => panic!("types can't be used in runtime"),
            Type::TypVar(_) => panic!("unresolved type var got to code gen"),
        },
        Value::Length(value, location) => {
            let value = resolve_types_value(*value, function, globals, lexer)?;
            let type_ = type_of(&value, function, globals);
            if let Type::Tuple(types) = type_ {
                Value::IntLiteral(types.len() as i64)
            } else {
                return Result::Err(lexer.make_error_report(
                    location,
                    &format!("expected Tuple, found {}", display_type(&type_, globals)),
                ));
            }
        }
        _ => value,
    })
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
        match resolve_type(type_, globals) {
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

pub fn resolve_types_scope(
    scope: &Scope,
    function: &mut Function,
    globals: &mut Globals,
    lexer: &Lexer,
) -> Result<Scope, String> {
    function.new_scope(scope.create_borrowed_vars);
    for instruction in scope.ir.clone() {
        resolve_types_instruction(instruction, function, globals, lexer)?;
    }

    let mut new_self = function.scopes.pop().expect("scope is created above");
    new_self.no_return = scope.no_return;
    Result::Ok(new_self)
}

pub fn resolve_types_function(
    mut function: Function,
    globals: &mut Globals,
    lexer: &Lexer,
) -> Result<Function, String> {
    for scope in mem::take(&mut function.scopes) {
        let new_scope = resolve_types_scope(&scope, &mut function, globals, lexer)?;
        function.scopes.push(new_scope);
    }
    Result::Ok(function)
}

pub fn type_of(value: &Value, function: &Function, globals: &Globals) -> Type {
    match value {
        Value::IntLiteral(_) | Value::Length(_, _) => Type::Int,
        Value::Int32Literal(_) => Type::Int32,
        Value::BoolLiteral(_) => Type::Bool,
        Value::Tuple(_, types) => Type::Tuple(types.clone()),
        Value::Type(_) => Type::Typ,
        Value::Variable(index) => resolve_type(&function.var_types[index], globals),
        Value::Arg(index) => resolve_type(&function.arg_types[*index as usize], globals),
        Value::Global(name) => resolve_type(&globals.global_types[name], globals),
        Value::Function(name) => Type::FnPtr(
            globals.functions[name]
                .arg_types
                .iter()
                .map(|type_| resolve_type(type_, globals))
                .collect(),
            globals.functions[name]
                .result_types
                .iter()
                .map(|type_| resolve_type(type_, globals))
                .collect(),
        ),
        Value::Zeroed(type_, _) => resolve_type(type_, globals),
        Value::Undefined => todo!("make undefined know its type"),
    }
}

fn resolve_types_phi(
    phi: Phi,
    function: &mut Function,
    globals: &mut Globals,
    lexer: &Lexer,
) -> Result<Phi, String> {
    Result::Ok(Phi {
        result_var: phi.result_var,
        result_type: resolve_type(&phi.result_type, globals),
        case1: resolve_types_value(phi.case1, function, globals, lexer)?,
        case2: resolve_types_value(phi.case2, function, globals, lexer)?,
    })
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
            let value = resolve_types_value(value, function, globals, lexer)?;
            function.add_instruction(Instruction::Printf(
                Value::Global(globals.new_string("%lld\n")),
                [value].to_vec(),
            ))
        }
        Type::Int32 => {
            let value = resolve_types_value(value, function, globals, lexer)?;
            function.add_instruction(Instruction::Printf(
                Value::Global(globals.new_string("%d\n")),
                [value].to_vec(),
            ))
        }
        Type::String => {
            let value = resolve_types_value(value, function, globals, lexer)?;
            function.add_instruction(Instruction::Putstr(value))
        }
        Type::Bool => {
            let var = function.new_var(Type::String);
            let value = resolve_types_value(value, function, globals, lexer)?;

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
            let value = resolve_types_value(value, function, globals, lexer)?;

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
            if let Value::Type(type_) = resolve_types_value(value, function, globals, lexer)? {
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
    match resolve_actual_type(&type_, globals, lexer)? {
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

fn resolve_types_instruction(
    instruction: Instruction,
    function: &mut Function,
    globals: &mut Globals,
    lexer: &Lexer,
) -> Result<(), String> {
    match instruction {
        Instruction::Bogus => panic!("bogus instruction got to type resolution"),
        Instruction::Arithemtic(op, lhs, rhs, result_var) => {
            let lhs = resolve_types_value(lhs, function, globals, lexer)?;
            let rhs = resolve_types_value(rhs, function, globals, lexer)?;
            function.add_instruction(Instruction::Arithemtic(op, lhs, rhs, result_var))
        }
        Instruction::Relational(op, lhs, rhs, result_var) => {
            let lhs = resolve_types_value(lhs, function, globals, lexer)?;
            let rhs = resolve_types_value(rhs, function, globals, lexer)?;
            function.add_instruction(Instruction::Relational(op, lhs, rhs, result_var))
        }
        Instruction::Relational32(op, lhs, rhs, result_var) => {
            let lhs = resolve_types_value(lhs, function, globals, lexer)?;
            let rhs = resolve_types_value(rhs, function, globals, lexer)?;
            function.add_instruction(Instruction::Relational32(op, lhs, rhs, result_var))
        }
        Instruction::Logical(op, lhs, rhs, result_var) => {
            let lhs = resolve_types_value(lhs, function, globals, lexer)?;
            let rhs = resolve_types_value(rhs, function, globals, lexer)?;
            function.add_instruction(Instruction::Logical(op, lhs, rhs, result_var))
        }
        Instruction::Not(value, result_var) => {
            let value = resolve_types_value(value, function, globals, lexer)?;
            function.add_instruction(Instruction::Not(value, result_var))
        }
        Instruction::Alloca(value, type_, result_var) => {
            let value = resolve_types_value(value, function, globals, lexer)?;
            function.add_instruction(Instruction::Alloca(
                value,
                resolve_actual_type(&type_, globals, lexer)?,
                result_var,
            ))
        }
        Instruction::Load(ptr, type_, result_var) => {
            let ptr = resolve_types_value(ptr, function, globals, lexer)?;
            function.add_instruction(Instruction::Load(
                ptr,
                resolve_actual_type(&type_, globals, lexer)?,
                result_var,
            ))
        }
        Instruction::Store(ptr, type_, value) => {
            let ptr = resolve_types_value(ptr, function, globals, lexer)?;
            let value = resolve_types_value(value, function, globals, lexer)?;
            function.add_instruction(Instruction::Store(
                ptr,
                resolve_actual_type(&type_, globals, lexer)?,
                value,
            ))
        }
        Instruction::InsertValue(tuple, tuple_type, value, index, result_var) => {
            let tuple = resolve_types_value(tuple, function, globals, lexer)?;
            let value = resolve_types_value(value, function, globals, lexer)?;
            function.add_instruction(Instruction::InsertValue(
                tuple,
                resolve_actual_type(&tuple_type, globals, lexer)?,
                value,
                index,
                result_var,
            ))
        }
        Instruction::ExtractValue(tuple, tuple_type, index, result_var) => {
            let tuple = resolve_types_value(tuple, function, globals, lexer)?;
            function.add_instruction(Instruction::ExtractValue(
                tuple,
                resolve_actual_type(&tuple_type, globals, lexer)?,
                index,
                result_var,
            ))
        }
        Instruction::Print(value, type_) => resolve_print(value, type_, function, globals, lexer)?,
        Instruction::Putstr(value) => {
            let value = resolve_types_value(value, function, globals, lexer)?;
            function.add_instruction(Instruction::Putstr(value))
        }
        Instruction::Printf(fmt_string, args) => {
            let fmt_string = resolve_types_value(fmt_string, function, globals, lexer)?;
            let args = args
                .into_iter()
                .map(|arg| resolve_types_value(arg, function, globals, lexer))
                .collect::<Result<Vec<Value>, String>>()?;
            function.add_instruction(Instruction::Printf(fmt_string, args))
        }
        Instruction::Input(result_var, type_, location) => {
            resolve_input(type_, result_var, location, function, globals, lexer)?
        }
        Instruction::GetsS(buf, size, result_var) => {
            let buf = resolve_types_value(buf, function, globals, lexer)?;
            let size = resolve_types_value(size, function, globals, lexer)?;
            function.add_instruction(Instruction::GetsS(buf, size, result_var))
        }
        Instruction::Strcmp(lhs, rhs, result_var) => {
            let lhs = resolve_types_value(lhs, function, globals, lexer)?;
            let rhs = resolve_types_value(rhs, function, globals, lexer)?;
            function.add_instruction(Instruction::Strcmp(lhs, rhs, result_var))
        }
        Instruction::Exit(value) => {
            let value = resolve_types_value(value, function, globals, lexer)?;
            function.add_instruction(Instruction::Exit(value))
        }
        Instruction::Call(fn_ptr, arg_types, arg_values, result_types, result_vars) => {
            let fn_ptr = resolve_types_value(fn_ptr, function, globals, lexer)?;
            let mut new_arg_types = Vec::with_capacity(arg_types.len());
            for arg_type in arg_types {
                new_arg_types.push(resolve_actual_type(&arg_type, globals, lexer)?);
            }

            let mut new_result_types = Vec::with_capacity(result_types.len());
            for result_type in result_types {
                new_result_types.push(resolve_actual_type(&result_type, globals, lexer)?);
            }

            function.add_instruction(Instruction::Call(
                fn_ptr,
                new_arg_types,
                arg_values,
                new_result_types,
                result_vars,
            ))
        }
        Instruction::Return(values, types) => {
            let mut new_types = Vec::with_capacity(types.len());
            for type_ in types {
                new_types.push(resolve_actual_type(&type_, globals, lexer)?);
            }

            let values = values
                .into_iter()
                .map(|value| resolve_types_value(value, function, globals, lexer))
                .collect::<Result<Vec<Value>, String>>()?;

            function.add_instruction(Instruction::Return(values, new_types))
        }
        Instruction::If(condition, then_scope, else_scope, phis) => {
            let mut new_phis = Vec::with_capacity(phis.len());
            for phi in phis {
                new_phis.push(resolve_types_phi(phi, function, globals, lexer)?)
            }

            let instruction = Instruction::If(
                resolve_types_value(condition, function, globals, lexer)?,
                resolve_types_scope(&then_scope, function, globals, lexer)?,
                resolve_types_scope(&else_scope, function, globals, lexer)?,
                new_phis,
            );
            function.add_instruction(instruction);
        }
        Instruction::Loop(phis, body_scope) => {
            let mut new_phis = Vec::with_capacity(phis.len());
            for phi in phis {
                new_phis.push(resolve_types_phi(phi, function, globals, lexer)?)
            }

            let instruction = Instruction::Loop(
                new_phis,
                resolve_types_scope(&body_scope, function, globals, lexer)?,
            );
            function.add_instruction(instruction);
        }
        Instruction::While(phis, test_scope, test, body_scope) => {
            let mut new_phis = Vec::with_capacity(phis.len());
            for phi in phis {
                new_phis.push(resolve_types_phi(phi, function, globals, lexer)?)
            }

            let instruction = Instruction::While(
                new_phis,
                resolve_types_scope(&test_scope, function, globals, lexer)?,
                resolve_types_value(test, function, globals, lexer)?,
                resolve_types_scope(&body_scope, function, globals, lexer)?,
            );
            function.add_instruction(instruction);
        }
    };
    Result::Ok(())
}

pub fn resolve_type(type_: &Type, globals: &Globals) -> Type {
    match type_ {
        Type::TypVar(i) => globals.type_vars.get(i).unwrap_or(type_).clone(),
        Type::FnPtr(arg_types, result_types) => Type::FnPtr(
            arg_types
                .iter()
                .map(|arg_type| resolve_type(arg_type, globals))
                .collect(),
            result_types
                .iter()
                .map(|result_type| resolve_type(result_type, globals))
                .collect(),
        ),
        _ => type_.clone(),
    }
}

pub fn resolve_actual_type(type_: &Type, globals: &Globals, lexer: &Lexer) -> Result<Type, String> {
    let resolved_type = resolve_type(type_, globals);
    if let Type::TypVar(i) = resolved_type {
        Result::Err(lexer.make_error_report(globals.type_var_locations[&i], "Ambigous type"))
    } else {
        Result::Ok(resolved_type)
    }
}

pub fn merge_types(type1: &Type, type2: &Type, globals: &mut Globals) -> bool {
    match type1 {
        Type::TypVar(i) => {
            if let Some(new_type1) = globals.type_vars.get(i) {
                merge_types(&new_type1.clone(), type2, globals)
            } else {
                if type2 != type1 {
                    globals.type_vars.insert(*i, type2.clone());
                }
                true
            }
        }
        Type::FnPtr(arg_types1, result_types1) => {
            if let Type::FnPtr(arg_types2, result_types2) = type2 {
                let arg_types_match = merge_type_lists(arg_types1, arg_types2, globals);
                let result_types_match = merge_type_lists(result_types1, result_types2, globals);
                arg_types_match && result_types_match
            } else {
                false
            }
        }
        _ => match type2 {
            Type::TypVar(_) => merge_types(type2, type1, globals),
            Type::FnPtr(_, _) => false,
            _ => type1 == type2,
        },
    }
}

pub fn merge_type_lists(types1: &[Type], types2: &[Type], globals: &mut Globals) -> bool {
    if types1.len() == types2.len() {
        let mut types_match = true;
        for (type1, type2) in zip(types1, types2) {
            if !merge_types(type1, type2, globals) {
                types_match = false;
            }
        }
        types_match
    } else {
        false
    }
}
