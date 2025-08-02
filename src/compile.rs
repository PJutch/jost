use crate::types::display_type;
use crate::types::display_type_list;
use crate::types::merge_types;
use crate::types::type_of;

use crate::lex::Lexer;
use crate::lex::Location;
use crate::lex::Word;

use crate::ir::Arithemtic;
use crate::ir::Function;
use crate::ir::Globals;
use crate::ir::Instruction;
use crate::ir::Logical;
use crate::ir::Phi;
use crate::ir::Relational;
use crate::ir::Value;

use crate::types::resolve_types_function;
use crate::types::Type;

use std::cmp;
use std::mem;

fn arithmetic_from_id(id: &str) -> Option<Arithemtic> {
    match id {
        "+" => Option::Some(Arithemtic::Add),
        "-" => Option::Some(Arithemtic::Sub),
        "*" => Option::Some(Arithemtic::Mul),
        "/" => Option::Some(Arithemtic::Div),
        "%" => Option::Some(Arithemtic::Mod),
        _ => Option::None,
    }
}

fn is_arithmetic_op(id: &str) -> bool {
    arithmetic_from_id(id).is_some()
}

fn relational_from_id(id: &str) -> Option<Relational> {
    match id {
        "==" => Option::Some(Relational::Eq),
        "!=" => Option::Some(Relational::Ne),
        "<" => Option::Some(Relational::Lt),
        "<=" => Option::Some(Relational::Le),
        ">" => Option::Some(Relational::Gt),
        ">=" => Option::Some(Relational::Ge),
        _ => Option::None,
    }
}

fn is_relational_op(id: &str) -> bool {
    relational_from_id(id).is_some()
}

fn logical_from_id(id: &str) -> Option<Logical> {
    match id {
        "&&" => Option::Some(Logical::And),
        "||" => Option::Some(Logical::Or),
        _ => Option::None,
    }
}

fn is_logical_op(id: &str) -> bool {
    logical_from_id(id).is_some()
}

fn compile_call(
    current_function: &mut Function,
    called_value: Value,
    globals: &Globals,
    lexer: &Lexer,
    location: Location,
) -> Result<(), String> {
    if let Type::FnPtr(arg_types, result_types) = type_of(&called_value, current_function, globals)
    {
        if arg_types.iter().enumerate().all(|(i, arg_type)| {
            current_function
                .nth_from_top((arg_types.len() - i - 1) as i64, globals)
                .is_some_and(|value| type_of(&value, current_function, globals) == *arg_type)
        }) {
            let mut args = Vec::new();
            for _ in 0..arg_types.len() {
                args.push(
                    current_function
                        .pop(globals)
                        .expect("stack len is checked above"),
                );
            }
            args.reverse();

            let mut results = Vec::new();
            for result_type in &result_types {
                let result_var = current_function.new_var(result_type.clone());
                current_function.push(Value::Variable(result_var));
                results.push(result_var);
            }

            current_function.add_instruction(Instruction::Call(
                called_value,
                arg_types.clone(),
                args,
                result_types,
                results,
            ));
            Result::Ok(())
        } else {
            Result::Err(lexer.make_error_report(
                location,
                &format!(
                    "expected ... {}, found {}",
                    display_type_list(&arg_types, globals),
                    current_function.stack_as_string(globals)
                ),
            ))
        }
    } else {
        Result::Err(lexer.make_error_report(
            location,
            &format!(
                "expected ... fn, found {}",
                current_function.stack_as_string(globals)
            ),
        ))
    }
}

fn do_type_assertion(
    function: &mut Function,
    globals: &mut Globals,
    lexer: &Lexer,
    location: Location,
) -> Result<(), String> {
    if let Some(value) = function.nth_from_top(1, globals) {
        if let Some(Value::Type(type_)) = function.pop(globals) {
            return if merge_types(&type_of(&value, function, globals), &type_, globals) {
                Result::Ok(())
            } else {
                Result::Err(lexer.make_error_report(
                    location,
                    &format!(
                        "expected ... {}, found {}",
                        display_type(&type_, globals),
                        function.stack_as_string(globals)
                    ),
                ))
            };
        }
    }

    Result::Err(lexer.make_error_report(
        location,
        &format!(
            "expected ... value Type, found {}",
            function.stack_as_string(globals)
        ),
    ))
}

fn compile_if(
    function: &mut Function,
    globals: &mut Globals,
    lexer: &mut Lexer,
    location: Location,
) -> Result<(), String> {
    let condition = function.pop_of_type(Type::Bool, globals, location, lexer)?;

    function.new_scope(false);
    lexer.consume_and_expect("(")?;
    compile_block(lexer, function, globals, false)?;

    let mut then_scope = function
        .scopes
        .pop()
        .expect("compile_if already created a then scope");

    function.new_scope(false);
    if lexer.try_consume("else") {
        lexer.consume_and_expect("(")?;
        compile_block(lexer, function, globals, false)?;
    }
    let mut else_scope = function
        .scopes
        .pop()
        .expect("compile_if already created an else scope");

    let mut then_returned = Vec::new();
    let mut else_returned = Vec::new();

    for i in 0..cmp::max(then_scope.n_borrowed, else_scope.n_borrowed) {
        let push_in_then = i >= then_scope.n_borrowed;
        let push_in_else = i >= else_scope.n_borrowed;

        let borrowed_value = function.pop(globals).expect(
            "to_borrow of one of the scopes is below us in the stack so there is a value to pop",
        );

        if push_in_then {
            then_returned.push(borrowed_value.clone());
        }

        if push_in_else {
            else_returned.push(borrowed_value);
        }
    }

    then_returned.reverse();
    while let Some(value) = then_scope.stack.pop() {
        then_returned.push(value);
    }

    else_returned.reverse();
    while let Some(value) = else_scope.stack.pop() {
        else_returned.push(value);
    }

    let mut phis = Vec::new();
    if !then_scope.no_return && !else_scope.no_return {
        let then_types: Vec<Type> = then_returned
            .iter()
            .map(|value| type_of(value, function, globals))
            .collect();

        let else_types: Vec<Type> = else_returned
            .iter()
            .map(|value| type_of(value, function, globals))
            .collect();

        if then_types != else_types {
            return Result::Err(lexer.make_error_report(
                location,
                &format!(
                    "then branch left {} on stack, but else branch left {}",
                    display_type_list(&then_types, globals),
                    display_type_list(&else_types, globals)
                ),
            ));
        }

        for i in 0..then_returned.len() {
            let result_var = function.new_var(then_types[i].clone());
            function.push(Value::Variable(result_var));
            phis.push(Phi {
                result_var,
                result_type: then_types[i].clone(),
                case1: then_returned[i].clone(),
                case2: else_returned[i].clone(),
            });
        }
    } else if !then_scope.no_return {
        for value in then_returned {
            function.push(value);
        }
    } else if !else_scope.no_return {
        for value in else_returned {
            function.push(value);
        }
    } else {
        function.mark_no_return();
    }

    function.add_instruction(Instruction::If(condition, then_scope, else_scope, phis));
    Result::Ok(())
}

fn compile_loop(
    function: &mut Function,
    globals: &mut Globals,
    lexer: &mut Lexer,
    location: Location,
) -> Result<(), String> {
    function.new_scope(true);
    lexer.consume_and_expect("(")?;
    compile_block(lexer, function, globals, false)?;
    let mut body_scope = function.scopes.pop().expect("scope was created above");

    if body_scope.no_return {
        return Result::Err(lexer.make_error_report(location, "loop body shouldn't be noreturn"));
    }

    let expected_types: Vec<Type> = (0..body_scope.n_borrowed)
        .map(|i| type_of(&body_scope.borrowed_vars[&i].1, function, globals))
        .collect();

    let actual_types: Vec<Type> = body_scope
        .stack
        .iter()
        .map(|value| type_of(value, function, globals))
        .collect();

    if expected_types != actual_types {
        return Result::Err(lexer.make_error_report(
            location,
            &format!(
                "loop body consumed {}, but returned {}",
                display_type_list(&expected_types, globals),
                display_type_list(&actual_types, globals)
            ),
        ));
    }

    let mut phis = Vec::new();
    for (i, (var, value)) in mem::take(&mut body_scope.borrowed_vars) {
        let i = i as usize;
        phis.push(Phi {
            result_var: var,
            result_type: type_of(&value, function, globals),
            case1: value,
            case2: if i < body_scope.stack.len() {
                body_scope.stack[body_scope.stack.len() - i - 1].clone()
            } else {
                Value::Variable(var)
            },
        });
    }

    function.add_instruction(Instruction::Loop(phis, body_scope));

    function.mark_no_return();

    Result::Ok(())
}

fn compile_while(
    function: &mut Function,
    globals: &mut Globals,
    lexer: &mut Lexer,
    location: Location,
) -> Result<(), String> {
    function.new_scope(true);
    lexer.consume_and_expect("(")?;
    compile_block(lexer, function, globals, false)?;

    let test = function.pop_of_type(
        Type::Bool,
        globals,
        Location::char_at(function.scopes.last().expect("scope was created above").end),
        lexer,
    )?;

    function.new_scope(false);
    lexer.consume_and_expect("(")?;
    compile_block(lexer, function, globals, false)?;

    let body_scope = function.scopes.pop().expect("scopes were created above");
    let mut test_scope = function.scopes.pop().expect("scopes were created above");

    if test_scope.no_return {
        return Result::Err(lexer.make_error_report(location, "while test can't be noreturn"));
    }

    if body_scope.no_return {
        return Result::Err(lexer.make_error_report(location, "while body can't be noreturn"));
    }

    let n_borrowed = body_scope.n_borrowed + test_scope.n_borrowed - test_scope.stack.len() as i64;

    let expected_types: Vec<Type> = (0..n_borrowed)
        .map(|i| type_of(&test_scope.borrowed_vars[&i].1, function, globals))
        .collect();

    let actual_types: Vec<Type> = test_scope
        .stack
        .iter()
        .map(|value| type_of(value, function, globals))
        .collect();

    if expected_types != actual_types {
        return Result::Err(lexer.make_error_report(
            location,
            &format!(
                "loop body consumed {}, but returned {}",
                display_type_list(&expected_types, globals),
                display_type_list(&actual_types, globals)
            ),
        ));
    }

    let mut phis = Vec::new();
    for (i, (var, value)) in mem::take(&mut test_scope.borrowed_vars) {
        let i = i as usize;
        phis.push(Phi {
            result_var: var,
            result_type: type_of(&value, function, globals),
            case1: value,
            case2: if i < body_scope.stack.len() {
                body_scope.stack[body_scope.stack.len() - i - 1].clone()
            } else if i < body_scope.stack.len() + test_scope.stack.len()
                - body_scope.n_borrowed as usize
            {
                test_scope.stack[test_scope.stack.len() + body_scope.stack.len()
                    - body_scope.n_borrowed as usize
                    - i
                    - 1]
                .clone()
            } else {
                Value::Variable(var)
            },
        });
    }

    for _ in 0..n_borrowed {
        function.pop(globals);
    }

    for value in &test_scope.stack {
        function.push(value.clone());
    }

    function.add_instruction(Instruction::While(phis, test_scope, test, body_scope));

    Result::Ok(())
}

fn compile_return(
    function: &mut Function,
    globals: &Globals,
    lexer: &Lexer,
    location: Location,
) -> Result<(), String> {
    let mut stack = Vec::new();
    while let Some(value) = function.pop(globals) {
        stack.push(value);
    }
    stack.reverse();

    let types: Vec<Type> = stack
        .iter()
        .map(|value| type_of(value, function, globals))
        .collect();
    if types == function.result_types {
        function.add_instruction(Instruction::Return(stack, types));
        function.mark_no_return();
        Result::Ok(())
    } else {
        Result::Err(lexer.make_error_report(
            location,
            &format!(
                "function returns {}, found {}",
                display_type_list(&function.result_types, globals),
                display_type_list(&types, globals)
            ),
        ))
    }
}

fn compile_store(
    function: &mut Function,
    globals: &mut Globals,
    lexer: &Lexer,
    location: Location,
) -> Result<(), String> {
    if let Some(ptr) = function.nth_from_top(1, globals) {
        if let Type::Ptr(value_type) = type_of(&ptr, function, globals) {
            if let Some(value) = function.nth_from_top(0, globals) {
                if merge_types(&type_of(&value, function, globals), &value_type, globals) {
                    let (ptr, value) = function.pop2_of_any_type(globals, location, lexer)?;
                    function.add_instruction(Instruction::Store(ptr, *value_type, value));
                    return Result::Ok(());
                }
            }
        }
    }
    Result::Err(lexer.make_error_report(
        location,
        &format!(
            "expected A Ptr A, found {}",
            function.stack_as_string(globals)
        ),
    ))
}

fn compile_append(
    function: &mut Function,
    globals: &mut Globals,
    lexer: &Lexer,
    location: Location,
) -> Result<(), String> {
    if let Some(value) = function.nth_from_top(0, globals) {
        if let Some(Value::Tuple(mut values, mut types)) = function.nth_from_top(1, globals) {
            function.pop(globals).expect("stack is checked above");
            function.pop(globals).expect("stack is checked above");

            types.push(type_of(&value, function, globals));
            values.push(value);

            function.push(Value::Tuple(values, types));
            return Result::Ok(());
        }
    }

    Result::Err(lexer.make_error_report(
        location,
        &format!(
            "expected ... ... Tuple Value, found {}",
            function.stack_as_string(globals)
        ),
    ))
}

fn compile_at(
    function: &mut Function,
    globals: &mut Globals,
    lexer: &Lexer,
    location: Location,
) -> Result<(), String> {
    if let Some(tuple) = function.nth_from_top(1, globals) {
        let type_ = type_of(&tuple, function, globals);
        if let Type::Tuple(types) = type_.clone() {
            if let Some(Value::IntLiteral(index)) = function.nth_from_top(0, globals) {
                if index >= 0 {
                    if let Some(value_type) = types.get(index as usize) {
                        function.pop(globals).expect("stack is checked above");
                        function.pop(globals).expect("stack is checked above");

                        let result_var = function.new_var(value_type.clone());
                        function.push(Value::Variable(result_var));
                        function.add_instruction(Instruction::ExtractValue(
                            tuple,
                            type_.clone(),
                            index,
                            result_var,
                        ));
                        return Result::Ok(());
                    }
                }
            }
        }
    }

    Result::Err(lexer.make_error_report(
        location,
        &format!(
            "expected ... Tuple ConstantIndex, found {}",
            function.stack_as_string(globals)
        ),
    ))
}

fn compile_set_at(
    function: &mut Function,
    globals: &mut Globals,
    lexer: &Lexer,
    location: Location,
) -> Result<(), String> {
    if let Some(tuple) = function.nth_from_top(2, globals) {
        let type_ = type_of(&tuple, function, globals);
        if let Type::Tuple(types) = type_.clone() {
            if let Some(value) = function.nth_from_top(1, globals) {
                if let Some(Value::IntLiteral(index)) = function.nth_from_top(0, globals) {
                    if index >= 0 && index as (usize) < types.len() {
                        function.pop(globals).expect("stack is checked above");
                        function.pop(globals).expect("stack is checked above");
                        function.pop(globals).expect("stack is checked above");

                        let mut new_values = Vec::new();
                        let mut new_types = Vec::new();

                        for (i, old_type) in types.into_iter().enumerate() {
                            if i == index as usize {
                                new_values.push(value.clone());
                                new_types.push(type_of(&value, function, globals));
                            } else {
                                let result_var = function.new_var(old_type.clone());
                                function.add_instruction(Instruction::ExtractValue(
                                    tuple.clone(),
                                    type_.clone(),
                                    i as i64,
                                    result_var,
                                ));
                                new_values.push(Value::Variable(result_var));

                                new_types.push(old_type);
                            }
                        }

                        function.push(Value::Tuple(new_values, new_types));
                        return Result::Ok(());
                    }
                }
            }
        }
    }

    Result::Err(lexer.make_error_report(
        location,
        &format!(
            "expected ... Tuple Value ConstantIndex, found {}",
            function.stack_as_string(globals)
        ),
    ))
}

fn compile_block(
    lexer: &mut Lexer,
    function: &mut Function,
    globals: &mut Globals,
    consume_all: bool,
) -> Result<(), String> {
    let mut last_pos = 0;
    while let Some((word, location)) = lexer.next_word() {
        if function.is_no_return() && word != Word::Id(")") {
            return Result::Err(lexer.make_error_report(location, "unreachable code"));
        }

        if let Word::Id(id) = word {
            if globals.functions.contains_key(id) {
                compile_call(
                    function,
                    Value::Function(id.to_owned()),
                    globals,
                    lexer,
                    location,
                )?;
                continue;
            }
        }

        match word {
            Word::Int(value) => {
                function.push(Value::IntLiteral(value));
            }
            Word::String(value) => {
                function.push(Value::Global(globals.new_string(value)));
            }
            Word::Id(id) if is_arithmetic_op(id) => {
                let (a, b) =
                    function.pop2_of_type(Type::Int, Type::Int, globals, location, lexer)?;

                let result_var = function.new_var(Type::Int);
                function.push(Value::Variable(result_var));

                function.add_instruction(Instruction::Arithemtic(
                    arithmetic_from_id(id).expect(
                        "arithmetic from_id should succeed because it's checked in pattern guard",
                    ),
                    a,
                    b,
                    result_var,
                ));
            }
            Word::Id(id) if is_relational_op(id) => {
                let (a, b) =
                    function.pop2_of_type(Type::Int, Type::Int, globals, location, lexer)?;

                let result_var = function.new_var(Type::Bool);
                function.push(Value::Variable(result_var));

                function.add_instruction(Instruction::Relational(
                    relational_from_id(id).expect(
                        "relational from_id should succeed because it's checked in pattern guard",
                    ),
                    a,
                    b,
                    result_var,
                ));
            }
            Word::Id(id) if is_logical_op(id) => {
                let (a, b) =
                    function.pop2_of_type(Type::Bool, Type::Bool, globals, location, lexer)?;

                let result_var = function.new_var(Type::Bool);
                function.push(Value::Variable(result_var));

                function.add_instruction(Instruction::Logical(
                    logical_from_id(id).expect(
                        "logical from_id should succeed because it's checked in pattern guard",
                    ),
                    a,
                    b,
                    result_var,
                ));
            }
            Word::Id("!") => {
                let value = function.pop_of_type(Type::Bool, globals, location, lexer)?;

                let result_var = function.new_var(Type::Bool);
                function.push(Value::Variable(result_var));

                function.add_instruction(Instruction::Not(value, result_var));
            }
            Word::Id("true") => {
                function.push(Value::BoolLiteral(true));
            }
            Word::Id("false") => {
                function.push(Value::BoolLiteral(false));
            }
            Word::Id("zeroed") => {
                function.push(Value::Zeroed(
                    Type::TypVar(globals.new_type_var(location)),
                    location,
                ));
            }
            Word::Id("dup") => {
                let value = function.pop_of_any_type(globals, location, lexer)?;
                function.push(value.clone());
                function.push(value);
            }
            Word::Id("pop") => {
                function.pop_of_any_type(globals, location, lexer)?;
            }
            Word::Id("swp") => {
                let (a, b) = function.pop2_of_any_type(globals, location, lexer)?;
                function.push(b);
                function.push(a);
            }
            Word::Id("over") => {
                let (a, b) = function.pop2_of_any_type(globals, location, lexer)?;
                function.push(a.clone());
                function.push(b);
                function.push(a);
            }
            Word::Id("rot") => {
                let [a, b, c] = function.pop3_of_any_type(globals, location, lexer)?;
                function.push(b);
                function.push(c);
                function.push(a);
            }
            Word::Id("print") => {
                let value = function.pop_of_any_type(globals, location, lexer)?;
                let type_ = type_of(&value, function, globals);
                function.add_instruction(Instruction::Print(value, type_));
            }
            Word::Id("input") => {
                let type_ = Type::TypVar(globals.new_type_var(location));
                let var = function.new_var(type_.clone());
                function.push(Value::Variable(var));
                function.add_instruction(Instruction::Input(var, type_, location));
            }
            Word::Id("exit") => {
                let mut stack = Vec::new();
                while let Some(value) = function.pop(globals) {
                    stack.push(value);
                }
                stack.reverse();

                let types: Vec<Type> = stack
                    .iter()
                    .map(|value| type_of(value, function, globals))
                    .collect();
                if types != [Type::Int] {
                    return Result::Err(format!(
                        "exit expects stack to be clean except single Int, found {}",
                        display_type_list(&types, globals)
                    ));
                }

                function.add_instruction(Instruction::Exit(
                    stack
                        .last()
                        .expect("stack is checked above to have an Int")
                        .clone(),
                ));
                function.mark_no_return();
            }
            Word::Id("return") => compile_return(function, globals, lexer, location)?,
            Word::Id("[]") => {
                function.push(Value::Tuple(Vec::new(), Vec::new()));
            }
            Word::Id(",") => compile_append(function, globals, lexer, location)?,
            Word::Id("at") => compile_at(function, globals, lexer, location)?,
            Word::Id("setat") => compile_set_at(function, globals, lexer, location)?,
            Word::Id("len") => {
                let tuple = function.pop_of_any_type(globals, location, lexer)?;
                function.push(Value::Length(Box::new(tuple), location));
            }
            Word::Id("(") => {
                let lambda = compile_function(lexer, globals, Vec::new(), Vec::new(), false)?;
                function.push(Value::Global(globals.new_lambda(lambda)));
            }
            Word::Id(")") => break,
            Word::Id("call") => {
                if let Some(called_value) = function.pop(globals) {
                    compile_call(function, called_value, globals, lexer, location)?;
                } else {
                    return Result::Err(
                        lexer.make_error_report(location, "no function on the stack"),
                    );
                }
            }
            Word::Id("if") => compile_if(function, globals, lexer, location)?,
            Word::Id("loop") => compile_loop(function, globals, lexer, location)?,
            Word::Id("while") => compile_while(function, globals, lexer, location)?,
            Word::Id("lambda") => {
                lexer.consume_and_expect("(")?;
                let (args, results) = function.pop_signature(globals, lexer, location)?;
                let lambda = compile_function(lexer, globals, args, results, false)?;
                function.push(Value::Global(globals.new_lambda(lambda)));
            }
            Word::Id("fn") => {
                let (id, location) = lexer.consume_id()?;
                if globals.functions.contains_key(id) {
                    return Result::Err(lexer.make_error_report(
                        location,
                        &format!("function {id} was already defined"),
                    ));
                }

                lexer.consume_and_expect("(")?;

                let (args, results) = function.pop_signature(globals, lexer, location)?;
                let new_function = compile_function(lexer, globals, args, results, false)?;
                globals.functions.insert(id.to_owned(), new_function);
            }
            Word::Id("Int") => {
                function.push(Value::Type(Type::Int));
            }
            Word::Id("String") => {
                function.push(Value::Type(Type::String));
            }
            Word::Id("Bool") => {
                function.push(Value::Type(Type::Bool));
            }
            Word::Id("Ptr") => {
                let type_ = function
                    .pop_of_type(Type::Typ, globals, location, lexer)?
                    .unwrap_type();
                function.push(Value::Type(Type::Ptr(Box::from(type_))));
            }
            Word::Id("alloca") => {
                let value = function.pop_of_any_type(globals, location, lexer)?;
                let type_ = type_of(&value, function, globals);
                let result_var = function.new_var(Type::Ptr(Box::from(type_.clone())));
                function.add_instruction(Instruction::Alloca(value, type_, result_var));
                function.push(Value::Variable(result_var));
            }
            Word::Id("load") => {
                let ptr = function.pop_of_any_type(globals, location, lexer)?;
                if let Type::Ptr(value_type) = type_of(&ptr, function, globals) {
                    let result_var = function.new_var(value_type.as_ref().clone());
                    function.add_instruction(Instruction::Load(ptr, *value_type, result_var));
                    function.push(Value::Variable(result_var));
                } else {
                    return Result::Err(lexer.make_error_report(
                        location,
                        &format!(
                            "expected A Ptr, found {}",
                            function.stack_as_string(globals)
                        ),
                    ));
                }
            }
            Word::Id("store") => compile_store(function, globals, lexer, location)?,
            Word::Id(":") => do_type_assertion(function, globals, lexer, location)?,
            Word::Id(id) => {
                return Err(lexer.make_error_report(location, &format!("Unknown word {id}")))
            }
        }
        last_pos = lexer.current_byte as i64;
    }

    function
        .scopes
        .last_mut()
        .expect("compile_block expects at least one scope to exist")
        .end = last_pos;

    if consume_all && !lexer.is_empty() {
        return Result::Err(lexer.make_error_report(
            Location::char_at(last_pos),
            "unexpected closing paranthesis",
        ));
    }

    Result::Ok(())
}

fn compile_function(
    lexer: &mut Lexer,
    globals: &mut Globals,
    arg_types: Vec<Type>,
    result_types: Vec<Type>,
    main: bool,
) -> Result<Function, String> {
    let mut function = Function::new(arg_types, result_types);
    compile_block(lexer, &mut function, globals, main)?;

    if !function.is_no_return() {
        if main {
            function.add_instruction(Instruction::Return(
                Vec::from([Value::IntLiteral(0)]),
                Vec::from([Type::Int32]),
            ));
        } else {
            let location = Location::char_at(function.get_single_scope().end);
            compile_return(&mut function, globals, lexer, location)?;
        }
    }

    Result::Ok(function)
}

pub fn compile_to_ir(lexer: &mut Lexer, globals: &mut Globals) -> Result<Function, String> {
    let mut main = compile_function(lexer, globals, Vec::new(), Vec::new(), true)?;
    main = resolve_types_function(main, globals, lexer)?;

    let mut lambdas = globals.lambdas.clone();
    for lambda in &mut lambdas {
        *lambda = resolve_types_function(mem::take(lambda), globals, lexer)?;
    }
    globals.lambdas = lambdas;

    let mut functions = globals.functions.clone();
    for function in functions.values_mut() {
        *function = resolve_types_function(mem::take(function), globals, lexer)?;
    }
    globals.functions = functions;

    Result::Ok(main)
}
