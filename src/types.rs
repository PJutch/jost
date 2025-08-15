use crate::ir::Arithemtic;
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
use std::cmp::max;
use std::iter::zip;
use std::mem;
use std::ops::Deref;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Type {
    Int,
    Int32,
    Bool,
    String,
    Ptr(Box<Type>),
    FnPtr(Vec<Type>, Vec<Type>),
    Tuple(Vec<Type>),
    Array(Box<Type>, i64),
    Slice(Box<Type>),
    Vec(Box<Type>),
    Typ,
    TypVar(i64),
}

fn align_offset(offset: i64, alignment: i64) -> i64 {
    if offset % alignment == 0 {
        offset
    } else {
        offset - offset % alignment + alignment
    }
}

impl Type {
    pub fn compiletime_len(&self) -> i64 {
        match self {
            Type::Tuple(types) => types.len() as i64,
            Type::Array(_, size) => *size,
            _ => panic!("value doesn't have a length"),
        }
    }

    pub fn element_type(&self, index: i64) -> &Type {
        match self {
            Type::Tuple(types) => &types[index as usize],
            Type::Array(element_type, _) => element_type.as_ref(),
            _ => panic!("type can't be indexed"),
        }
    }

    pub fn all_elements_type(&self) -> &Type {
        match self {
            Type::Ptr(type_) | Type::Array(type_, _) | Type::Slice(type_) | Type::Vec(type_) => {
                type_.as_ref()
            }
            Type::Tuple(_) => panic!("tuple elements are of different types"),
            Type::TypVar(_) => todo!("handle type vars"),
            _ => panic!("type has no elements"),
        }
    }

    pub fn index_type_statically(
        &self,
        index: i64,
        globals: &Globals,
        lexer: &Lexer,
        location: Location,
    ) -> Result<&Type, String> {
        match self {
            Type::Tuple(types) => types.get(index as usize).ok_or_else(|| {
                lexer.make_error_report(
                    location,
                    &format!(
                        "index {index} is out of bounds for {}",
                        display_type(self, globals)
                    ),
                )
            }),
            Type::Array(element_type, size) => {
                if (0..*size).contains(&index) {
                    Result::Ok(element_type.as_ref())
                } else {
                    Result::Err(lexer.make_error_report(
                        location,
                        &format!(
                            "index {index} is out of bounds for {}",
                            display_type(self, globals)
                        ),
                    ))
                }
            }
            _ => Result::Err(lexer.make_error_report(
                location,
                &format!("{} can't be indexed", display_type(self, globals)),
            )),
        }
    }

    pub fn index_type_dinamically(
        &self,
        globals: &mut Globals,
        lexer: &Lexer,
        location: Location,
    ) -> Result<&Type, String> {
        match self {
            Type::Array(element_type, _) => Result::Ok(element_type),
            Type::Tuple(types) => {
                if types
                    .iter()
                    .all(|type_| merge_types(type_, &types[0], globals))
                {
                    Result::Ok(&types[0])
                } else {
                    Result::Err(lexer.make_error_report(
                        location,
                        &format!(
                            "{} can't be indexed dinamically",
                            display_type(self, globals)
                        ),
                    ))
                }
            }
            _ => Result::Err(lexer.make_error_report(
                location,
                &format!("{} can't be indexed", display_type(self, globals)),
            )),
        }
    }

    fn alignment(&self) -> Result<i64, String> {
        Result::Ok(match self {
            Type::Int | Type::String | Type::Ptr(_) | Type::FnPtr(_, _) => 8,
            Type::Int32 => 4,
            Type::Bool => 1,
            Type::Tuple(types) => {
                let mut alignment = 1;
                for type_ in types {
                    alignment = max(alignment, type_.alignment()?);
                }
                alignment
            }
            Type::Array(type_, _) => type_.alignment()?,
            Type::Slice(type_) => slice_underlying_type(type_.deref().clone()).alignment()?,
            Type::Vec(type_) => vec_underlying_type(type_.deref().clone()).alignment()?,
            Type::Typ => {
                return Result::Err("types don't have a runtime representation".to_owned())
            }
            Type::TypVar(_) => {
                return Result::Err("trying to get alignment of a type var".to_owned())
            }
        })
    }

    pub fn byte_size(&self) -> Result<i64, String> {
        Result::Ok(match self {
            Type::Int | Type::String | Type::Ptr(_) | Type::FnPtr(_, _) => 8,
            Type::Int32 => 4,
            Type::Bool => 1,
            Type::Tuple(types) => {
                let mut size = 0;
                for type_ in types {
                    size = align_offset(size, type_.alignment()?) + type_.byte_size()?;
                }
                align_offset(size, self.alignment()?)
            }
            Type::Array(type_, size) => type_.byte_size()? * size,
            Type::Slice(type_) => slice_underlying_type(type_.deref().clone()).byte_size()?,
            Type::Vec(type_) => vec_underlying_type(type_.deref().clone()).byte_size()?,
            Type::Typ => {
                return Result::Err("types don't have a runtime representation".to_owned())
            }
            Type::TypVar(_) => return Result::Err("trying to get size of a type var".to_owned()),
        })
    }
}

pub fn slice_underlying_type(element_type: Type) -> Type {
    Type::Tuple(Vec::from([Type::Ptr(Box::from(element_type)), Type::Int]))
}

pub fn vec_underlying_type(element_type: Type) -> Type {
    Type::Tuple(Vec::from([Type::Slice(Box::from(element_type)), Type::Int]))
}

fn check_can_be_zeroed(
    type_: &Type,
    globals: &Globals,
    lexer: &Lexer,
    location: Location,
) -> Result<(), String> {
    match type_ {
        Type::Int | Type::Int32 | Type::Bool | Type::Slice(_) | Type::Vec(_) => Result::Ok(()),
        Type::Ptr(_) | Type::String | Type::FnPtr(_, _) | Type::Typ => {
            Result::Err(lexer.make_error_report(
                location,
                &format!(
                    "value of type {} can't be zeroed",
                    display_type(type_, globals)
                ),
            ))
        }
        Type::Tuple(types) => {
            for type_ in types {
                check_can_be_zeroed(type_, globals, lexer, location)?;
            }
            Result::Ok(())
        }
        Type::Array(element_type, _) => check_can_be_zeroed(element_type, globals, lexer, location),
        Type::TypVar(_) => panic!("unresolved type var can't be checked if it can be zeroed"),
    }
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
            let types = types
                .iter()
                .map(|type_| resolve_actual_type(type_, globals, lexer))
                .collect::<Result<Vec<Type>, String>>()?;

            let mut built_tuple = Value::Undefined;
            for (i, value) in values.into_iter().enumerate() {
                let next_var = function.new_var(Type::Tuple(types.clone()));
                function.add_instruction(Instruction::InsertValue(
                    built_tuple,
                    Type::Tuple(types.clone()),
                    value,
                    types[i].clone(),
                    i as i64,
                    next_var,
                ));
                built_tuple = Value::Variable(next_var);
            }
            built_tuple
        }
        Value::Array(values, type_) => {
            let values = values
                .into_iter()
                .map(|value| resolve_types_value(value, function, globals, lexer))
                .collect::<Result<Vec<Value>, String>>()?;
            let type_ = resolve_actual_type(&type_, globals, lexer)?;

            let array_type = Type::Array(Box::from(type_.clone()), values.len() as i64);
            let mut built_array = Value::Undefined;
            for (i, value) in values.into_iter().enumerate() {
                let next_var = function.new_var(array_type.clone());
                function.add_instruction(Instruction::InsertValue(
                    built_array,
                    array_type.clone(),
                    value,
                    type_.clone(),
                    i as i64,
                    next_var,
                ));
                built_array = Value::Variable(next_var);
            }
            built_array
        }
        Value::Slice(ptr, size) => {
            let ptr = resolve_types_value(*ptr, function, globals, lexer)?;
            let size = resolve_types_value(*size, function, globals, lexer)?;

            let element_type = type_of(&ptr, function, globals).all_elements_type().clone();
            let slice_type = Type::Slice(Box::from(element_type.clone()));
            let ptr_type = Type::Ptr(Box::from(element_type.clone()));

            let with_ptr_var = function.new_var(slice_type.clone());
            function.add_instruction(Instruction::InsertValue(
                Value::Undefined,
                slice_underlying_type(element_type.clone()),
                ptr,
                ptr_type,
                0,
                with_ptr_var,
            ));

            let result_var = function.new_var(slice_type);
            function.add_instruction(Instruction::InsertValue(
                Value::Variable(with_ptr_var),
                slice_underlying_type(element_type),
                size,
                Type::Int,
                1,
                result_var,
            ));

            Value::Variable(result_var)
        }
        Value::Vec(slice, size) => {
            let slice = resolve_types_value(*slice, function, globals, lexer)?;
            let size = resolve_types_value(*size, function, globals, lexer)?;

            let element_type = type_of(&slice, function, globals)
                .all_elements_type()
                .clone();
            let vec_type = Type::Vec(Box::from(element_type.clone()));
            let slice_type = Type::Slice(Box::from(element_type.clone()));

            let with_slice_var = function.new_var(vec_type.clone());
            function.add_instruction(Instruction::InsertValue(
                Value::Undefined,
                vec_underlying_type(element_type.clone()),
                slice,
                slice_type,
                0,
                with_slice_var,
            ));

            let result_var = function.new_var(vec_type);
            function.add_instruction(Instruction::InsertValue(
                Value::Variable(with_slice_var),
                vec_underlying_type(element_type),
                size,
                Type::Int,
                1,
                result_var,
            ));

            Value::Variable(result_var)
        }
        Value::Type(type_) => Value::Type(resolve_actual_type(&type_, globals, lexer)?),
        Value::Zeroed(ref type_, location) => {
            check_can_be_zeroed(
                &resolve_actual_type(type_, globals, lexer)?,
                globals,
                lexer,
                location,
            )?;
            value
        }
        Value::Length(value, location) => {
            let value = resolve_types_value(*value, function, globals, lexer)?;
            let type_ = type_of(&value, function, globals);
            match type_ {
                Type::Tuple(types) => Value::IntLiteral(types.len() as i64),
                Type::Array(_, size) => Value::IntLiteral(size),
                Type::Slice(element_type) => {
                    let result_var = function.new_var(Type::Int);
                    function.add_instruction(Instruction::ExtractValue(
                        value,
                        slice_underlying_type(*element_type),
                        Type::Int,
                        1,
                        result_var,
                    ));
                    Value::Variable(result_var)
                }
                Type::Vec(element_type) => {
                    let result_var = function.new_var(Type::Int);
                    function.add_instruction(Instruction::ExtractValue(
                        value,
                        vec_underlying_type(*element_type),
                        Type::Int,
                        1,
                        result_var,
                    ));
                    Value::Variable(result_var)
                }
                _ => {
                    return Result::Err(lexer.make_error_report(
                        location,
                        &format!(
                            "expected Tuple or Array, found {}",
                            display_type(&type_, globals)
                        ),
                    ))
                }
            }
        }
        Value::SizeOf(type_) => {
            Value::IntLiteral(resolve_actual_type(&type_, globals, lexer)?.byte_size()?)
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
            Type::Array(type_, size) => format!(
                "{} {size} Array",
                self.display_type(type_.as_ref(), globals)
            ),
            Type::Slice(type_) => format!("{} Slice", self.display_type(type_.as_ref(), globals)),
            Type::Vec(type_) => format!("{} Vec", self.display_type(type_.as_ref(), globals)),
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
        Value::IntLiteral(_) | Value::Length(_, _) | Value::SizeOf(_) => Type::Int,
        Value::Int32Literal(_) => Type::Int32,
        Value::BoolLiteral(_) => Type::Bool,
        Value::Tuple(_, types) => Type::Tuple(types.clone()),
        Value::Array(values, type_) => Type::Array(Box::from(type_.clone()), values.len() as i64),
        Value::Slice(ptr, _) => Type::Slice(Box::from(
            type_of(ptr, function, globals).all_elements_type().clone(),
        )),
        Value::Vec(ptr, _) => Type::Vec(Box::from(
            type_of(ptr, function, globals).all_elements_type().clone(),
        )),
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
    let type_ = resolve_actual_type(&type_, globals, lexer)?;
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

            for (i, element_type) in types.iter().enumerate() {
                let element_type = resolve_actual_type(element_type, globals, lexer)?;

                let element_var = function.new_var(element_type.clone());
                function.add_instruction(Instruction::ExtractValue(
                    value.clone(),
                    type_.clone(),
                    types[i].clone(),
                    i as i64,
                    element_var,
                ));

                resolve_print(
                    Value::Variable(element_var),
                    element_type.clone(),
                    function,
                    globals,
                    lexer,
                )?;
            }
        }
        Type::Array(element_type, size) => {
            let value = resolve_types_value(value, function, globals, lexer)?;
            for i in 0..size {
                let element_var = function.new_var(element_type.deref().clone());
                function.add_instruction(Instruction::ExtractValue(
                    value.clone(),
                    type_.clone(),
                    element_type.deref().clone(),
                    i,
                    element_var,
                ));
                resolve_print(
                    Value::Variable(element_var),
                    element_type.deref().clone(),
                    function,
                    globals,
                    lexer,
                )?;
            }
        }
        Type::Slice(_) => todo!("implement print for slice"),
        Type::Vec(_) => todo!("implement print for vec"),
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

fn resolve_clone(
    value: Value,
    type_: Type,
    result_var: i64,
    function: &mut Function,
    lexer: &Lexer,
    location: Location,
) -> Result<bool, String> {
    match &type_ {
        Type::Ptr(type_) => {
            let size = match type_.as_ref() {
                Type::Typ => {
                    return Result::Err(
                        lexer.make_error_report(location, "types can't be put into memory"),
                    )
                }
                Type::TypVar(_) => panic!("this type var should be checked and resolved in caller"),
                _ => type_.byte_size()?,
            };

            function.add_instruction(Instruction::Malloc(Value::IntLiteral(size), result_var));

            // TODO: clone contents
            function.add_instruction(Instruction::Memcopy(
                value,
                Value::Variable(result_var),
                Value::IntLiteral(size),
            ));

            Result::Ok(true)
        }
        Type::Tuple(types) => {
            let mut clonable = false;
            for (i, element_type) in types.iter().enumerate() {
                let element_var = function.new_var(element_type.clone());
                function.add_instruction(Instruction::ExtractValue(
                    value.clone(),
                    type_.clone(),
                    element_type.clone(),
                    i as i64,
                    element_var,
                ));

                if resolve_clone(
                    Value::Variable(element_var),
                    element_type.clone(),
                    result_var,
                    function,
                    lexer,
                    location,
                )? {
                    clonable = true;
                }
            }
            Result::Ok(clonable)
        }
        Type::Array(_, _) => todo!("clone array"),
        Type::Slice(element_type) => {
            let ptr_type = Type::Ptr(element_type.clone());
            let ptr_var = function.new_var(ptr_type.clone());
            function.add_instruction(Instruction::ExtractValue(
                value.clone(),
                slice_underlying_type(element_type.deref().clone()),
                ptr_type.clone(),
                0,
                ptr_var,
            ));

            let element_size = match element_type.as_ref() {
                Type::Typ => {
                    return Result::Err(
                        lexer.make_error_report(location, "types can't be put into memory"),
                    )
                }
                Type::TypVar(_) => panic!("this type var should be checked and resolved in caller"),
                _ => type_.byte_size()?,
            };

            let element_count_var = function.new_var(Type::Int);
            function.add_instruction(Instruction::ExtractValue(
                value.clone(),
                slice_underlying_type(element_type.deref().clone()),
                Type::Int,
                1,
                element_count_var,
            ));

            let allocation_size_var = function.new_var(Type::Int);
            function.add_instruction(Instruction::Arithemtic(
                Arithemtic::Mul,
                Value::IntLiteral(element_size),
                Value::Variable(element_count_var),
                allocation_size_var,
            ));

            let new_ptr_var = function.new_var(ptr_type.clone());
            function.add_instruction(Instruction::Malloc(
                Value::Variable(allocation_size_var),
                new_ptr_var,
            ));

            // TODO: clone slice contents
            function.add_instruction(Instruction::Memcopy(
                Value::Variable(ptr_var),
                Value::Variable(new_ptr_var),
                Value::Variable(allocation_size_var),
            ));

            function.add_instruction(Instruction::InsertValue(
                value,
                slice_underlying_type(element_type.deref().clone()),
                Value::Variable(new_ptr_var),
                ptr_type,
                0,
                result_var,
            ));

            Result::Ok(true)
        }
        Type::Vec(element_type) => resolve_clone(
            value,
            vec_underlying_type(element_type.deref().clone()),
            result_var,
            function,
            lexer,
            location,
        ),
        _ => Result::Ok(false),
    }
}

fn resolve_destroy(value: Value, type_: Type, function: &mut Function) -> bool {
    match &type_ {
        Type::Ptr(_) => {
            // TODO: destroy contents
            function.add_instruction(Instruction::Free(value));
            true
        }
        Type::Tuple(types) => {
            let mut destroyable = false;
            for (i, element_type) in types.iter().enumerate() {
                let element_var = function.new_var(element_type.clone());
                function.add_instruction(Instruction::ExtractValue(
                    value.clone(),
                    type_.clone(),
                    element_type.clone(),
                    i as i64,
                    element_var,
                ));

                if resolve_destroy(Value::Variable(element_var), element_type.clone(), function) {
                    destroyable = true;
                }
            }
            destroyable
        }
        Type::Array(_, _) => todo!("destroy array"),
        Type::Slice(element_type) => {
            // TODO: destroy slice contents
            resolve_destroy(
                value,
                slice_underlying_type(element_type.deref().clone()),
                function,
            )
        }
        Type::Vec(element_type) => {
            // TODO: destroy vec contents
            resolve_destroy(
                value,
                vec_underlying_type(element_type.deref().clone()),
                function,
            )
        }
        _ => false,
    }
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
        Type::Tuple(_) | Type::Array(_, _) | Type::Slice(_) | Type::Vec(_) => todo!("input lists"),
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
        Instruction::Alloca(type_, result_var) => function.add_instruction(Instruction::Alloca(
            resolve_actual_type(&type_, globals, lexer)?,
            result_var,
        )),
        Instruction::AllocaN(type_, value, result_var) => {
            let type_ = resolve_actual_type(&type_, globals, lexer)?;
            let value = resolve_types_value(value, function, globals, lexer)?;
            function.add_instruction(Instruction::AllocaN(type_, value, result_var));
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
        Instruction::Memcopy(from, to, size) => {
            let from = resolve_types_value(from, function, globals, lexer)?;
            let to = resolve_types_value(to, function, globals, lexer)?;
            let size = resolve_types_value(size, function, globals, lexer)?;
            function.add_instruction(Instruction::Memcopy(from, to, size));
        }
        Instruction::Malloc(size, result_var) => {
            let size = resolve_types_value(size, function, globals, lexer)?;
            function.add_instruction(Instruction::Malloc(size, result_var));
        }
        Instruction::Realloc(ptr, size, result_var) => {
            let ptr = resolve_types_value(ptr, function, globals, lexer)?;
            let size = resolve_types_value(size, function, globals, lexer)?;
            function.add_instruction(Instruction::Realloc(ptr, size, result_var));
        }
        Instruction::Free(ptr) => {
            let ptr = resolve_types_value(ptr, function, globals, lexer)?;
            function.add_instruction(Instruction::Free(ptr));
        }
        Instruction::Clone(value, type_, result_var, location) => {
            if !resolve_clone(
                resolve_types_value(value, function, globals, lexer)?,
                type_.clone(),
                result_var,
                function,
                lexer,
                location,
            )? {
                return Result::Err(lexer.make_error_report(
                    location,
                    &format!(
                        "value of type {} doesn't need to be destroyed",
                        display_type(&type_, globals)
                    ),
                ));
            }
        }
        Instruction::Destroy(value, type_, location) => {
            if !resolve_destroy(
                resolve_types_value(value, function, globals, lexer)?,
                type_.clone(),
                function,
            ) {
                return Result::Err(lexer.make_error_report(
                    location,
                    &format!(
                        "value of type {} doesn't need to be destroyed",
                        display_type(&type_, globals)
                    ),
                ));
            }
        }
        Instruction::InsertValue(tuple, tuple_type, value, value_type, index, result_var) => {
            let tuple = resolve_types_value(tuple, function, globals, lexer)?;
            let value = resolve_types_value(value, function, globals, lexer)?;
            function.add_instruction(Instruction::InsertValue(
                tuple,
                resolve_actual_type(&tuple_type, globals, lexer)?,
                value,
                resolve_actual_type(&value_type, globals, lexer)?,
                index,
                result_var,
            ))
        }
        Instruction::ExtractValue(tuple, tuple_type, value_type, index, result_var) => {
            let tuple = resolve_types_value(tuple, function, globals, lexer)?;
            function.add_instruction(Instruction::ExtractValue(
                tuple,
                resolve_actual_type(&tuple_type, globals, lexer)?,
                resolve_actual_type(&value_type, globals, lexer)?,
                index,
                result_var,
            ))
        }
        Instruction::InsertValueDyn(tuple, tuple_type, value, value_type, index, result_var) => {
            let tuple = resolve_types_value(tuple, function, globals, lexer)?;
            let tuple_type = resolve_actual_type(&tuple_type, globals, lexer)?;
            let value = resolve_types_value(value, function, globals, lexer)?;
            let value_type = resolve_actual_type(&value_type, globals, lexer)?;

            let ptr_var = function.new_var(Type::Ptr(Box::from(tuple_type.clone())));
            function.add_instruction(Instruction::Alloca(tuple_type.clone(), ptr_var));
            function.add_instruction(Instruction::Store(
                Value::Variable(ptr_var),
                tuple_type.clone(),
                tuple,
            ));

            let viewed_through_type = if let Type::Tuple(types) = &tuple_type {
                Type::Array(Box::from(value_type.clone()), types.len() as i64)
            } else {
                tuple_type.clone()
            };

            let element_ptr_var = function.new_var(Type::Ptr(Box::from(value_type.clone())));
            function.add_instruction(Instruction::GetElementPtr(
                viewed_through_type,
                Value::Variable(ptr_var),
                index,
                element_ptr_var,
            ));

            function.add_instruction(Instruction::Store(
                Value::Variable(element_ptr_var),
                value_type,
                value,
            ));

            function.add_instruction(Instruction::Load(
                Value::Variable(ptr_var),
                tuple_type,
                result_var,
            ));
        }
        Instruction::ExtractValueDyn(tuple, tuple_type, value_type, index, result_var) => {
            let tuple = resolve_types_value(tuple, function, globals, lexer)?;
            let tuple_type = resolve_actual_type(&tuple_type, globals, lexer)?;
            let value_type = resolve_actual_type(&value_type, globals, lexer)?;

            let ptr_var = function.new_var(Type::Ptr(Box::from(tuple_type.clone())));
            function.add_instruction(Instruction::Alloca(tuple_type.clone(), ptr_var));
            function.add_instruction(Instruction::Store(
                Value::Variable(ptr_var),
                tuple_type.clone(),
                tuple,
            ));

            let viewed_through_type = if let Type::Tuple(types) = &tuple_type {
                Type::Array(Box::from(value_type.clone()), types.len() as i64)
            } else {
                tuple_type.clone()
            };

            let element_ptr_var = function.new_var(Type::Ptr(Box::from(value_type.clone())));
            function.add_instruction(Instruction::GetElementPtr(
                viewed_through_type,
                Value::Variable(ptr_var),
                index,
                element_ptr_var,
            ));

            function.add_instruction(Instruction::Load(
                Value::Variable(element_ptr_var),
                value_type,
                result_var,
            ));
        }
        Instruction::GetElementPtr(type_, value, index, result_var) => {
            let type_ = resolve_actual_type(&type_, globals, lexer)?;
            let value = resolve_types_value(value, function, globals, lexer)?;
            let index = resolve_types_value(index, function, globals, lexer)?;
            function.add_instruction(Instruction::GetElementPtr(type_, value, index, result_var));
        }
        Instruction::GetNeighbourPtr(type_, value, index, result_var) => {
            let type_ = resolve_actual_type(&type_, globals, lexer)?;
            let value = resolve_types_value(value, function, globals, lexer)?;
            let index = resolve_types_value(index, function, globals, lexer)?;
            function.add_instruction(Instruction::GetNeighbourPtr(
                type_, value, index, result_var,
            ));
        }
        Instruction::Bitcast(value, from, to, result_var) => {
            let value = resolve_types_value(value, function, globals, lexer)?;
            function.add_instruction(Instruction::Bitcast(
                value,
                resolve_actual_type(&from, globals, lexer)?,
                resolve_actual_type(&to, globals, lexer)?,
                result_var,
            ));
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
        Type::Tuple(types) => Type::Tuple(
            types
                .iter()
                .map(|type_| resolve_type(type_, globals))
                .collect(),
        ),
        Type::Array(type_, size) => {
            Type::Array(Box::from(resolve_type(type_.as_ref(), globals)), *size)
        }
        Type::Ptr(type_) => Type::Ptr(Box::from(resolve_type(type_.as_ref(), globals))),
        Type::Slice(type_) => Type::Slice(Box::from(resolve_type(type_.as_ref(), globals))),
        Type::Vec(type_) => Type::Vec(Box::from(resolve_type(type_.as_ref(), globals))),
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

pub fn should_be_ptr(type_: Type, globals: &mut Globals) -> Option<Type> {
    match resolve_type(&type_, globals) {
        Type::Ptr(value_type) => Option::Some(*value_type),
        Type::TypVar(index) => {
            let value_type = Type::TypVar(globals.new_type_var(globals.type_var_locations[&index]));
            globals.type_vars.insert(index, value_type.clone());
            Option::Some(value_type)
        }
        _ => Option::None,
    }
}
