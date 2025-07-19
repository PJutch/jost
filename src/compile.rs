use crate::ir::display_type_list;
use crate::ir::type_of;

use crate::lex::Lexer;
use crate::lex::Location;
use crate::lex::Word;

use crate::ir;
use crate::ir::Arithemtic;
use crate::ir::Function;
use crate::ir::Globals;
use crate::ir::Instruction;
use crate::ir::Logical;
use crate::ir::Phi;
use crate::ir::Relational;
use crate::ir::Type;
use crate::ir::Value;

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
    globals: &Globals,
    lexer: &Lexer,
    location: Location,
) -> Result<(), String> {
    if let Some(fn_ptr) = current_function.nth_from_top(0, globals) {
        if let Type::FnPtr(arg_types, result_types) =
            ir::type_of(&fn_ptr, current_function, globals)
        {
            if arg_types.iter().enumerate().all(|(i, arg_type)| {
                current_function
                    .nth_from_top((arg_types.len() - i) as i64, globals)
                    .is_some_and(|value| type_of(&value, current_function, globals) == *arg_type)
            }) {
                let fn_ptr = current_function
                    .pop(globals)
                    .expect("stack len is checked above");

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
                    fn_ptr,
                    arg_types.clone(),
                    args,
                    result_types,
                    results,
                ));
                return Result::Ok(());
            }
        }
    }

    Result::Err(lexer.make_error_report(
        location,
        &format!(
            "expected ... args fn, found {}",
            current_function.stack_as_string(globals)
        ),
    ))
}

fn do_type_assertion(
    function: &mut Function,
    globals: &Globals,
    lexer: &Lexer,
    location: Location,
) -> Result<(), String> {
    if let Some(Value::Type(type_)) = function.nth_from_top(0, globals) {
        if let Some(value) = function.nth_from_top(1, globals) {
            if ir::type_of(&value, function, globals) != type_ {
                return Result::Err(lexer.make_error_report(
                    location,
                    &format!(
                        "expected ... {type_}, found {}",
                        function.stack_as_string(globals)
                    ),
                ));
            }
            function.pop(globals);
            return Result::Ok(());
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
                    ir::display_type_list(&then_types),
                    ir::display_type_list(&else_types)
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
                display_type_list(&expected_types),
                display_type_list(&actual_types)
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
                display_type_list(&expected_types),
                display_type_list(&actual_types)
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
                display_type_list(&function.result_types),
                display_type_list(&types)
            ),
        ))
    }
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
                match type_of(&value, function, globals) {
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
                        function.new_scope(false);
                        let then_scope = function.scopes.pop().expect("scope was created above");

                        function.new_scope(false);
                        let else_scope = function.scopes.pop().expect("scope was created above");

                        let var = function.new_var(Type::String);
                        function.add_instruction(Instruction::If(
                            value,
                            then_scope,
                            else_scope,
                            Vec::from([Phi {
                                result_var: var,
                                result_type: Type::String,
                                case1: Value::Global(globals.new_string("true")),
                                case2: Value::Global(globals.new_string("false")),
                            }]),
                        ));

                        function.add_instruction(Instruction::Putstr(Value::Variable(var)));
                    }
                    Type::List => {
                        if let Value::ListLiteral(types) = value {
                            function.add_instruction(Instruction::Putstr(Value::Global(
                                globals.new_string(&display_type_list(&types)),
                            )))
                        } else {
                            todo!("support list that aren't compile time lists of types")
                        }
                    }
                    Type::FnPtr(arg_types, result_types) => function.add_instruction(
                        Instruction::Putstr(Value::Global(globals.new_string(&format!(
                            "fn ({}) -> ({})",
                            display_type_list(&arg_types),
                            display_type_list(&result_types)
                        )))),
                    ),
                    Type::Type_ => {
                        if let Value::Type(type_) = value {
                            function.add_instruction(Instruction::Putstr(Value::Global(
                                globals.new_string(&type_.to_string()),
                            )))
                        } else {
                            panic!("Only Value::Type can be pf type Type");
                        }
                    }
                }
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
                        display_type_list(&types)
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
                function.push(Value::ListLiteral(Vec::new()));
            }
            Word::Id(",") => {
                // TODO: support lists of type other than type
                let (list, value) =
                    function.pop2_of_type(Type::List, Type::Type_, globals, location, lexer)?;

                let value = value.unwrap_type();
                let mut list = list.unwrap_list_literal();
                list.push(value);
                function.push(Value::ListLiteral(list));
            }
            Word::Id("(") => {
                let lambda = compile_function(lexer, globals, Vec::new(), Vec::new(), false)?;
                function.push(Value::Global(globals.new_lambda(lambda)));
            }
            Word::Id(")") => break,
            Word::Id("call") => compile_call(function, globals, lexer, location)?,
            Word::Id("if") => compile_if(function, globals, lexer, location)?,
            Word::Id("loop") => compile_loop(function, globals, lexer, location)?,
            Word::Id("while") => compile_while(function, globals, lexer, location)?,
            Word::Id("fn") => {
                lexer.consume_and_expect("(")?;

                let (args, results) =
                    function.pop2_of_type(Type::List, Type::List, globals, location, lexer)?;

                let lambda = compile_function(
                    lexer,
                    globals,
                    args.unwrap_list_literal(),
                    results.unwrap_list_literal(),
                    false,
                )?;
                function.push(Value::Global(globals.new_lambda(lambda)));
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
    compile_function(lexer, globals, Vec::new(), Vec::new(), true)
}
