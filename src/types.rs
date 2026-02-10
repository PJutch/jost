use crate::compile::compile_arithmetic;
use crate::lex::Lexer;
use crate::lex::Location;

use crate::ir::Arithemtic;
use crate::ir::Function;
use crate::ir::Globals;
use crate::ir::Instruction;
use crate::ir::Phi;
use crate::ir::Relational;
use crate::ir::ResolveTypes;
use crate::ir::Scope;
use crate::ir::Value;

use crate::compile::compile_vec_get_ptr;

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
    Ref(Box<Type>),
    Ptr(Box<Type>),
    FnPtr(Vec<Type>, Vec<Type>),
    Tuple(Vec<Type>),
    Array(Box<Type>, i64),
    Slice(Box<Type>),
    Vec(Box<Type>),
    Struct(Fields),
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
            Type::Ref(type_)
            | Type::Ptr(type_)
            | Type::Array(type_, _)
            | Type::Slice(type_)
            | Type::Vec(type_) => type_.as_ref(),
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
            Type::Int | Type::String | Type::Ref(_) | Type::Ptr(_) | Type::FnPtr(_, _) => 8,
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
            Type::Struct(members) => members.clone().struct_underlying_type().alignment()?,
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
            Type::Int | Type::String | Type::Ref(_) | Type::Ptr(_) | Type::FnPtr(_, _) => 8,
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
            Type::Struct(members) => members.clone().struct_underlying_type().byte_size()?,
            Type::Typ => {
                return Result::Err("types don't have a runtime representation".to_owned())
            }
            Type::TypVar(_) => return Result::Err("trying to get size of a type var".to_owned()),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fields(Vec<(String, Type)>);

impl Fields {
    pub fn new() -> Self {
        Fields(Vec::new())
    }

    pub fn add_field(&mut self, name: String, type_: Type) {
        self.0.push((name, type_));
    }

    pub fn find_field(&self, name: &str) -> Option<&Type> {
        self.0
            .iter()
            .find(|(field_name, _)| field_name == name)
            .map(|(_, type_)| type_)
    }

    pub fn struct_underlying_type(self) -> Type {
        Type::Tuple(self.0.into_iter().map(|(_, type_)| type_).collect())
    }

    fn field_index(&self, field_name: &str) -> Result<i64, String> {
        Result::Ok(
            self.0
                .iter()
                .enumerate()
                .find(|(_, (name, _))| *name == field_name)
                .ok_or("field not found")?
                .0 as i64,
        )
    }
}

pub fn slice_underlying_type(element_type: Type) -> Type {
    Type::Tuple(Vec::from([Type::Ref(Box::from(element_type)), Type::Int]))
}

pub fn vec_underlying_type(element_type: Type) -> Type {
    Type::Tuple(Vec::from([
        Type::Ptr(Box::from(element_type)),
        Type::Int,
        Type::Int,
    ]))
}

fn check_can_be_zeroed(
    type_: &Type,
    globals: &Globals,
    lexer: &Lexer,
    location: Location,
) -> Result<(), String> {
    match type_ {
        Type::Int | Type::Int32 | Type::Bool | Type::Slice(_) | Type::Vec(_) => Result::Ok(()),
        Type::Ref(_) | Type::Ptr(_) | Type::String | Type::FnPtr(_, _) | Type::Typ => {
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
        Type::Struct(fields) => check_can_be_zeroed(
            &fields.clone().struct_underlying_type(),
            globals,
            lexer,
            location,
        ),
        Type::Array(element_type, _) => check_can_be_zeroed(element_type, globals, lexer, location),
        Type::TypVar(_) => panic!("unresolved type var can't be checked if it can be zeroed"),
    }
}

fn make_undefined(globals: &mut Globals) -> Value {
    let bogus_location = Location { start: -1, end: -1 };
    Value::Undefined(
        Type::TypVar(globals.new_type_var(bogus_location)),
        bogus_location,
    )
}

pub fn resolve_types_value(
    value: Value,
    function: &mut Function,
    globals: &mut Globals,
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

            let mut built_tuple = make_undefined(globals);
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
            let mut built_array = make_undefined(globals);
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
        Value::Slice(reference, size) => {
            let reference_type = type_of(&reference, function, globals);
            resolve_types_value(
                Value::Tuple(
                    Vec::from([*reference, *size]),
                    Vec::from([reference_type, Type::Int]),
                ),
                function,
                globals,
                lexer,
            )?
        }
        Value::Vec(ptr, size, capacity) => {
            let ptr_type = type_of(&ptr, function, globals);
            resolve_types_value(
                Value::Tuple(
                    Vec::from([*ptr, *size, *capacity]),
                    Vec::from([ptr_type, Type::Int, Type::Int]),
                ),
                function,
                globals,
                lexer,
            )?
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
            let type_ = resolve_actual_type(&type_of(&value, function, globals), globals, lexer)?;
            let value = resolve_types_value(*value, function, globals, lexer)?;
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
                            "expected Container, found {}",
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
            Type::Ref(type_) => format!("{} Ref", self.display_type(type_.as_ref(), globals)),
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
            Type::Struct(fields) => {
                let mut result = String::from("Struct (");

                let has_members = !fields.0.is_empty();
                for (name, type_) in fields.0 {
                    result += " ";
                    result += &name;
                    result += " ";
                    result += &self.display_type(&type_, globals);
                }

                if has_members {
                    result += " ";
                }
                result += ")";

                result
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
        Value::IntLiteral(_) | Value::Length(_, _) | Value::SizeOf(_) => Type::Int,
        Value::Int32Literal(_) => Type::Int32,
        Value::BoolLiteral(_) => Type::Bool,
        Value::Tuple(_, types) => Type::Tuple(types.clone()),
        Value::Array(values, type_) => Type::Array(Box::from(type_.clone()), values.len() as i64),
        Value::Slice(ptr, _) => Type::Slice(Box::from(
            type_of(ptr, function, globals).all_elements_type().clone(),
        )),
        Value::Vec(ptr, _, _) => Type::Vec(Box::from(
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
        Value::Undefined(type_, _) => resolve_type(type_, globals),
    }
}

pub fn resolve_types_phi(
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
) -> Result<(), String> {
    match type_.clone() {
        Type::Int => function.add_instruction(Instruction::Printf(
            Value::Global(globals.new_string("%lld\n")),
            [value].to_vec(),
        )),
        Type::Int32 => function.add_instruction(Instruction::Printf(
            Value::Global(globals.new_string("%d\n")),
            [value].to_vec(),
        )),
        Type::String => function.add_instruction(Instruction::Putstr(value)),
        Type::Bool => {
            let var = function.new_var(Type::String);
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
            for (i, element_type) in types.iter().enumerate() {
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
                )?;
            }
        }
        Type::Array(element_type, size) => {
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
                )?;
            }
        }
        Type::Slice(_) => todo!("implement print for slice"),
        Type::Vec(_) => todo!("implement print for vec"),
        Type::Struct(_) => todo!("implement print for struct"),
        Type::FnPtr(_, _) | Type::Ref(_) | Type::Ptr(_) => {
            function.add_instruction(Instruction::Putstr(Value::Global(
                globals.new_string(&display_type(&type_, globals)),
            )))
        }
        Type::Typ => {
            if let Value::Type(type_) = value {
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

fn has_destructor(type_: &Type) -> bool {
    match type_ {
        Type::Ptr(_) | Type::Vec(_) => true,
        Type::Tuple(types) => types.iter().any(has_destructor),
        Type::Array(element_type, _) => has_destructor(element_type.as_ref()),
        Type::TypVar(_) => panic!("type var should be resolved before calling this"),
        _ => false,
    }
}

fn resolve_clone(
    value: Value,
    type_: Type,
    result_var: i64,
    function: &mut Function,
) -> Result<bool, String> {
    match &type_ {
        Type::Ptr(type_) => {
            let size = type_.byte_size()?;
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
                )? {
                    clonable = true;
                }
            }
            Result::Ok(clonable)
        }
        Type::Array(_, _) => todo!("clone array"),
        Type::Vec(element_type) => {
            let (ptr_var, ptr_type) =
                compile_vec_get_ptr(value.clone(), element_type.deref().clone(), function);

            let element_size = element_type.byte_size()?;

            let capacity_var = function.new_var(Type::Int);
            function.add_instruction(Instruction::ExtractValue(
                value.clone(),
                slice_underlying_type(element_type.deref().clone()),
                Type::Int,
                2,
                capacity_var,
            ));

            let allocation_size_var = compile_arithmetic(
                Arithemtic::Mul,
                Value::IntLiteral(element_size),
                Value::Variable(capacity_var),
                function,
            );

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
    match type_ {
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
        Type::Struct(_) => todo!("input structs"),
        Type::Ref(_) | Type::Ptr(_) | Type::FnPtr(_, _) | Type::Typ => {
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
    match instruction.resolve_types(function, globals, lexer)? {
        Instruction::Bogus => panic!("bogus instruction got to type resolution"),
        Instruction::CheckNoDestructor(type_, location) => {
            if has_destructor(&type_) {
                return Result::Err(lexer.make_error_report(
                    location,
                    &format!(
                        "value of type {} should be properly cloned and destroyed",
                        display_type(&type_, globals)
                    ),
                ));
            }
        }
        Instruction::Clone(value, type_, result_var, location) => {
            if !resolve_clone(value, type_.clone(), result_var, function)? {
                return Result::Err(lexer.make_error_report(
                    location,
                    &format!(
                        "value of type {} doesn't need to be cloned",
                        display_type(&type_, globals)
                    ),
                ));
            }
        }
        Instruction::Destroy(value, type_, location) => {
            if !resolve_destroy(value, type_.clone(), function) {
                return Result::Err(lexer.make_error_report(
                    location,
                    &format!(
                        "value of type {} doesn't need to be destroyed",
                        display_type(&type_, globals)
                    ),
                ));
            }
        }
        Instruction::InsertValueDyn(tuple, tuple_type, value, value_type, index, result_var) => {
            let ptr_var = function.new_var(Type::Ref(Box::from(tuple_type.clone())));
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

            let element_ptr_var = function.new_var(Type::Ref(Box::from(value_type.clone())));
            function.add_instruction(Instruction::GetElementPtr(
                viewed_through_type,
                Value::Variable(ptr_var),
                Type::Int,
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
            let ptr_var = function.new_var(Type::Ref(Box::from(tuple_type.clone())));
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

            let element_ptr_var = function.new_var(Type::Ref(Box::from(value_type.clone())));
            function.add_instruction(Instruction::GetElementPtr(
                viewed_through_type,
                Value::Variable(ptr_var),
                Type::Int,
                index,
                element_ptr_var,
            ));

            function.add_instruction(Instruction::Load(
                Value::Variable(element_ptr_var),
                value_type,
                result_var,
            ));
        }
        Instruction::GetField(struct_value, fields, field_type, field_name, result_var) => {
            let underlying_type = fields.clone().struct_underlying_type();
            let index = fields.field_index(&field_name)?;

            function.add_instruction(Instruction::ExtractValue(
                struct_value,
                underlying_type,
                field_type,
                index,
                result_var,
            ));
        }
        Instruction::SetField(
            struct_value,
            fields,
            field_value,
            field_type,
            field_name,
            result_var,
        ) => {
            let underlying_type = fields.clone().struct_underlying_type();
            let index = fields.field_index(&field_name)?;

            function.add_instruction(Instruction::InsertValue(
                struct_value,
                underlying_type,
                field_value,
                field_type,
                index,
                result_var,
            ));
        }
        Instruction::GetFieldPtr(ptr_value, fields, _, field_name, result_var) => {
            let underlying_type = fields.clone().struct_underlying_type();
            let index = fields.field_index(&field_name)?;

            function.add_instruction(Instruction::GetElementPtr(
                underlying_type,
                ptr_value,
                Type::Int32,
                Value::Int32Literal(index as i32),
                result_var,
            ));
        }
        Instruction::Print(value, type_) => resolve_print(value, type_, function, globals)?,
        Instruction::Printf(fmt_string, args) => {
            function.add_instruction(Instruction::Printf(fmt_string, args))
        }
        Instruction::Input(result_var, type_, location) => {
            resolve_input(type_, result_var, location, function, globals, lexer)?
        }
        other_instruction => function.add_instruction(other_instruction),
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
        Type::Ref(type_) => Type::Ref(Box::from(resolve_type(type_.as_ref(), globals))),
        Type::Ptr(type_) => Type::Ptr(Box::from(resolve_type(type_.as_ref(), globals))),
        Type::Slice(type_) => Type::Slice(Box::from(resolve_type(type_.as_ref(), globals))),
        Type::Vec(type_) => Type::Vec(Box::from(resolve_type(type_.as_ref(), globals))),
        _ => type_.clone(),
    }
}

pub fn resolve_actual_type(type_: &Type, globals: &Globals, lexer: &Lexer) -> Result<Type, String> {
    let resolved_type = resolve_type(type_, globals);
    match resolved_type {
        Type::TypVar(i) => {
            Result::Err(lexer.make_error_report(globals.type_var_locations[&i], "Ambigous type"))
        }
        Type::Struct(members) => Result::Ok(members.struct_underlying_type()),
        _ => Result::Ok(resolved_type),
    }
}

pub fn resolve_actual_fields(
    fields: Fields,
    globals: &Globals,
    lexer: &Lexer,
) -> Result<Fields, String> {
    Result::Ok(Fields(
        fields
            .0
            .into_iter()
            .map(|(name, field_type)| {
                Result::Ok((name, resolve_actual_type(&field_type, globals, lexer)?))
            })
            .collect::<Result<Vec<_>, String>>()?,
    ))
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
        Type::Ref(element_type1) => match type2 {
            Type::Ref(element_type2) => {
                merge_types(element_type1.as_ref(), element_type2.as_ref(), globals)
            }
            Type::TypVar(_) => merge_types(type2, type1, globals),
            _ => false,
        },
        Type::Ptr(element_type1) => match type2 {
            Type::Ptr(element_type2) => {
                merge_types(element_type1.as_ref(), element_type2.as_ref(), globals)
            }
            Type::TypVar(_) => merge_types(type2, type1, globals),
            _ => false,
        },
        Type::FnPtr(arg_types1, result_types1) => match type2 {
            Type::FnPtr(arg_types2, result_types2) => {
                merge_type_lists(arg_types1, arg_types2, globals)
                    && merge_type_lists(result_types1, result_types2, globals)
            }
            Type::TypVar(_) => merge_types(type2, type1, globals),
            _ => false,
        },
        Type::Tuple(types1) => match type2 {
            Type::Tuple(types2) => merge_type_lists(types1, types2, globals),
            Type::Array(element_type2, size) => {
                types1.len() as i64 == *size
                    && types1
                        .iter()
                        .all(|element_type1| merge_types(element_type1, element_type2, globals))
            }
            Type::TypVar(_) => merge_types(type2, type1, globals),
            _ => false,
        },
        Type::Array(element_type1, size1) => match type2 {
            Type::Array(element_type2, size2) => {
                size1 == size2
                    && merge_types(element_type1.as_ref(), element_type2.as_ref(), globals)
            }
            Type::Tuple(_) | &Type::TypVar(_) => merge_types(type2, type1, globals),
            _ => false,
        },
        Type::Slice(element_type1) => match type2 {
            Type::Slice(element_type2) => {
                merge_types(element_type1.as_ref(), element_type2.as_ref(), globals)
            }
            Type::TypVar(_) => merge_types(type2, type1, globals),
            _ => false,
        },
        Type::Vec(element_type1) => match type2 {
            Type::Vec(element_type2) => {
                merge_types(element_type1.as_ref(), element_type2.as_ref(), globals)
            }
            Type::TypVar(_) => merge_types(type2, type1, globals),
            _ => false,
        },
        _ => match type2 {
            Type::TypVar(_) => merge_types(type2, type1, globals),
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

pub fn should_be_ref(type_: Type, globals: &mut Globals) -> Option<Type> {
    match resolve_type(&type_, globals) {
        Type::Ref(element_type) => Option::Some(*element_type),
        Type::TypVar(type_var) => {
            let element_var = globals.new_type_var(globals.type_var_locations[&type_var]);
            merge_types(
                &Type::TypVar(type_var),
                &Type::Ref(Box::new(Type::TypVar(element_var))),
                globals,
            );
            Option::Some(Type::TypVar(element_var))
        }
        _ => Option::None,
    }
}

pub fn should_be_struct(type_: Type, globals: &mut Globals) -> Option<Fields> {
    match resolve_type(&type_, globals) {
        Type::Struct(fields) => Option::Some(fields),
        _ => Option::None,
    }
}
