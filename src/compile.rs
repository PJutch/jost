use crate::lex::Lexer;
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
    start: i64,
    end: i64,
) -> Result<(), String> {
    if let Some(pos) = current_function.top_stack_position() {
        let fn_ptr = current_function.at_stack_position(pos);
        if let Type::FnPtr(arg_types, result_types) = ir::type_of(fn_ptr, current_function, globals)
        {
            if current_function.has_given_types_after(&arg_types, pos, globals) {
                let fn_ptr = current_function.pop().expect("stack len is checked above");

                let mut args = Vec::new();
                for _ in 0..arg_types.len() {
                    args.push(current_function.pop().expect("stack len is checked above"));
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
        start,
        end,
        &format!(
            "expected ... fn, found {}",
            current_function.stack_as_string(globals)
        ),
    ))
}

fn do_type_assertion(
    function: &mut Function,
    globals: &Globals,
    lexer: &Lexer,
    start: i64,
    end: i64,
) -> Result<(), String> {
    if let Some(type_pos) = function.top_stack_position() {
        if let Some(value_pos) = function.decrement_stack_position(type_pos) {
            if let Value::Type(type_) = function.at_stack_position(type_pos) {
                let type_ = type_.clone();

                if ir::type_of(function.at_stack_position(value_pos), function, globals) != type_ {
                    return Result::Err(lexer.make_error_report(
                        start,
                        end,
                        &format!(
                            "expected ... {type_}, found {}",
                            function.stack_as_string(globals)
                        ),
                    ));
                }
                function.pop();
                return Result::Ok(());
            }
        }
    }

    Result::Err(lexer.make_error_report(
        start,
        end,
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
    start: i64,
    end: i64,
) -> Result<(), String> {
    lexer.consume_and_expect("(")?;
    let condition = function.pop_of_type(Type::Bool, globals, start, end, lexer)?;

    function.new_scope();
    compile_block(lexer, function, globals, false)?;

    let popped_scope = function
        .scopes
        .pop()
        .expect("pop_if expects at least one scope to exist");

    let mut borrowed_values = Vec::new();
    while function.top_stack_position() != popped_scope.to_borrow {
        borrowed_values.push(
            function.pop().expect(
                "popped_scope.to_borrow is below us in the stack so there is a value to pop",
            ),
        );
    }

    let mut expected_types = Vec::new();
    for value in &borrowed_values {
        expected_types.push(ir::type_of(value, function, globals));
    }

    let mut found_types = Vec::new();
    for value in &popped_scope.stack {
        found_types.push(ir::type_of(value, function, globals));
    }

    if expected_types != found_types {
        return Result::Err(lexer.make_error_report(
            start,
            end,
            &format!(
                "if is expected to return {}, got {}",
                ir::display_type_list(&expected_types),
                ir::display_type_list(&found_types)
            ),
        ));
    }

    let mut phis = Vec::new();
    for i in 0..popped_scope.stack.len() {
        let result_var = function.new_var(expected_types[i].clone());
        function.push(Value::Variable(result_var));
        phis.push(Phi {
            result_var,
            result_type: expected_types[i].clone(),
            case1: popped_scope.stack[i].clone(),
            case2: borrowed_values[i].clone(),
        });
    }

    function.add_instruction(Instruction::If(condition, popped_scope, phis));
    Result::Ok(())
}

fn compile_block(
    lexer: &mut Lexer,
    function: &mut Function,
    globals: &mut Globals,
    consume_all: bool,
) -> Result<(), String> {
    let mut last_pos = 0;
    while let Some(word) = lexer.next_word() {
        match word {
            Word::Int(value, _, _) => {
                function.push(Value::IntLiteral(value));
            }
            Word::String(value, _, _) => {
                function.push(Value::Global(globals.new_string(value)));
            }
            Word::Id(id, start, end) if is_arithmetic_op(id) => {
                let (a, b) =
                    function.pop2_of_type(Type::Int, Type::Int, globals, start, end, lexer)?;

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
            Word::Id(id, start, end) if is_relational_op(id) => {
                let (a, b) =
                    function.pop2_of_type(Type::Int, Type::Int, globals, start, end, lexer)?;

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
            Word::Id(id, start, end) if is_logical_op(id) => {
                let (a, b) =
                    function.pop2_of_type(Type::Bool, Type::Bool, globals, start, end, lexer)?;

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
            Word::Id("!", start, end) => {
                let value = function.pop_of_type(Type::Bool, globals, start, end, lexer)?;

                let result_var = function.new_var(Type::Bool);
                function.push(Value::Variable(result_var));

                function.add_instruction(Instruction::Not(value, result_var));
            }
            Word::Id("true", _, _) => {
                function.push(Value::BoolLiteral(true));
            }
            Word::Id("false", _, _) => {
                function.push(Value::BoolLiteral(false));
            }
            Word::Id("dup", start, end) => {
                let value = function.pop_of_any_type(globals, start, end, lexer)?;
                function.push(value.clone());
                function.push(value);
            }
            Word::Id("pop", start, end) => {
                function.pop_of_any_type(globals, start, end, lexer)?;
            }
            Word::Id("swp", start, end) => {
                let (a, b) = function.pop2_of_any_type(globals, start, end, lexer)?;
                function.push(b);
                function.push(a);
            }
            Word::Id("print", start, end) => {
                let value = function.pop_of_type(Type::String, globals, start, end, lexer)?;
                function.add_instruction(Instruction::Print(value));
            }
            Word::Id("[]", _, _) => {
                function.push(Value::ListLiteral(Vec::new()));
            }
            Word::Id(",", start, end) => {
                // TODO: support lists of type other than type
                let (list, value) =
                    function.pop2_of_type(Type::List, Type::Type_, globals, start, end, lexer)?;

                let value = value.unwrap_type();
                let mut list = list.unwrap_list_literal();
                list.push(value);
                function.push(Value::ListLiteral(list));
            }
            Word::Id("(", _, _) => {
                let lambda = compile_function(lexer, globals, Vec::new(), Vec::new(), false)?;
                function.push(Value::Global(globals.new_lambda(lambda)));
            }
            Word::Id(")", _, _) => break,
            Word::Id("call", start, end) => compile_call(function, globals, lexer, start, end)?,
            Word::Id("if", start, end) => compile_if(function, globals, lexer, start, end)?,
            Word::Id("fn", start, end) => {
                lexer.consume_and_expect("(")?;

                let (args, results) =
                    function.pop2_of_type(Type::List, Type::List, globals, start, end, lexer)?;

                let lambda = compile_function(
                    lexer,
                    globals,
                    args.unwrap_list_literal(),
                    results.unwrap_list_literal(),
                    false,
                )?;
                function.push(Value::Global(globals.new_lambda(lambda)));
            }
            Word::Id("Int", _, _) => {
                function.push(Value::Type(Type::Int));
            }
            Word::Id("String", _, _) => {
                function.push(Value::Type(Type::String));
            }
            Word::Id("Bool", _, _) => {
                function.push(Value::Type(Type::Bool));
            }
            Word::Id(":", start, end) => do_type_assertion(function, globals, lexer, start, end)?,
            Word::Id(id, start, end) => {
                return Err(lexer.make_error_report(start, end, &format!("Unknown word {id}")))
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
            last_pos,
            last_pos + 1,
            "unexpected closing paranthesis",
        ));
    }

    if !function.has_given_types_after(
        &function.result_types,
        function.over_top_stack_position(),
        globals,
    ) {
        return Result::Err(lexer.make_error_report(
            last_pos,
            last_pos + 1,
            &format!(
                "expected ... {}, found {}",
                ir::display_type_list(&function.result_types),
                function.stack_as_string(globals)
            ),
        ));
    }
    Result::Ok(())
}

fn compile_function(
    lexer: &mut Lexer,
    globals: &mut Globals,
    arg_types: Vec<Type>,
    result_types: Vec<Type>,
    consume_all: bool,
) -> Result<Function, String> {
    let mut function = Function::new(arg_types, result_types);
    compile_block(lexer, &mut function, globals, consume_all)?;
    Result::Ok(function)
}

pub fn compile_to_ir(lexer: &mut Lexer, globals: &mut Globals) -> Result<Function, String> {
    compile_function(lexer, globals, Vec::new(), Vec::new(), true)
}
