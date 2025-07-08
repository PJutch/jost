use crate::compile::Arithemtic;
use crate::compile::Globals;
use crate::compile::Instruction;
use crate::compile::Locals;
use crate::compile::Logical;
use crate::compile::Relational;
use crate::compile::Type;
use crate::compile::Value;

use core::panic;
use std::collections::HashMap;

struct GenerationContext {
    last_var_number: i64,
    var_numbers: HashMap<i64, i64>,
    last_control_flow: i64,
}

impl GenerationContext {
    fn new() -> Self {
        Self {
            last_var_number: 0,
            var_numbers: HashMap::new(),
            last_control_flow: 0,
        }
    }

    fn next_var_number(&mut self, var: i64) -> i64 {
        self.last_var_number += 1;
        self.var_numbers.insert(var, self.last_var_number);
        self.last_var_number
    }

    fn to_expression(&self, value: &Value) -> String {
        match value {
            Value::IntLiteral(value) => value.to_string(),
            Value::BoolLiteral(value) => (if *value { "true" } else { "false" }).to_owned(),
            Value::ListLiteral(_) => todo!("represent lists in runtime"),
            Value::Type(_) => panic!("types can't be used in runtime"),
            Value::Variable(index) | Value::Arg(index) => format!("%{}", self.var_numbers[index]),
            Value::Global(name) => format!("@{name}"),
        }
    }

    fn to_callable(&self, value: &Value) -> String {
        match value {
            Value::IntLiteral(_) => panic!("trying to call int literal"),
            Value::BoolLiteral(_) => panic!("trying to call bool literal"),
            Value::ListLiteral(_) => panic!("trying to call a list literal"),
            Value::Type(_) => panic!("trying to call a type"),
            Value::Variable(index) | Value::Arg(index) => format!("%{}", self.var_numbers[index]),
            Value::Global(name) => format!("@{name}"),
        }
    }

    fn next_contol_flow(&mut self) -> i64 {
        self.last_control_flow += 1;
        self.last_control_flow
    }
}

pub fn llvm_arithmetic(op: Arithemtic) -> &'static str {
    match op {
        Arithemtic::Add => "add",
        Arithemtic::Sub => "sub",
        Arithemtic::Mul => "mul",
        Arithemtic::Div => "div",
        Arithemtic::Mod => "mod",
    }
}

pub fn llvm_relational(op: Relational) -> &'static str {
    match op {
        Relational::Eq => "eq",
        Relational::Ne => "ne",
        Relational::Lt => "lt",
        Relational::Le => "le",
        Relational::Gt => "gt",
        Relational::Ge => "ge",
    }
}

fn to_llvm_type(type_: &Type) -> &'static str {
    match type_ {
        Type::Int => "i64",
        Type::Bool => "i1",
        Type::String => "ptr",
        Type::List => panic!("represent lists in runtime"),
        Type::FnPtr(_, _) => "ptr",
        Type::Type_ => panic!("types can't be used at runtime"),
    }
}

fn generate_instruction_llvm(
    instruction: &Instruction,
    context: &mut GenerationContext,
    locals: &Locals,
) -> Result<String, String> {
    for i in 0..locals.arg_types.len() {
        context.next_var_number(i as i64);
    }

    match instruction {
        Instruction::Arithemtic(op, a, b, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            Result::Ok(format!(
                "    %{result_var_number} = {} i64 {}, {}",
                llvm_arithmetic(*op),
                context.to_expression(a),
                context.to_expression(b),
            ))
        }
        Instruction::Relational(op, a, b, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            Result::Ok(format!(
                "    %{result_var_number} = icmp {} i64 {}, {}",
                llvm_relational(*op),
                context.to_expression(a),
                context.to_expression(b),
            ))
        }
        Instruction::Logical(op, a, b, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            match op {
                Logical::And => Result::Ok(format!(
                    "    %{result_var_number} = select i1 {}, i1 {}, i1 false",
                    context.to_expression(a),
                    context.to_expression(b)
                )),
                Logical::Or => Result::Ok(format!(
                    "    %{result_var_number} = select i1 {}, i1 true, i1 {}",
                    context.to_expression(a),
                    context.to_expression(b)
                )),
            }
        }
        Instruction::Not(value, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            Result::Ok(format!(
                "    %{result_var_number} = icmp eq i1 {}, false",
                context.to_expression(value)
            ))
        }
        Instruction::Print(value) => {
            context.next_var_number(-1);
            Result::Ok(format!(
                "    call i32 @puts(ptr {})",
                context.to_expression(value)
            ))
        }
        Instruction::Call(value, arg_types, args, results) => {
            let mut llvm = "    ".to_owned();

            if results.len() > 1 {
                todo!("support calls with multiple returns");
            } else if let Some(result_var) = results.first() {
                let result_var_number = context.next_var_number(*result_var);
                llvm += &format!(
                    "%{result_var_number} = call {} ",
                    to_llvm_type(&locals.var_types[result_var])
                );
            } else {
                llvm += "call void "
            }

            llvm += &context.to_callable(value);

            llvm += "(";
            for (i, arg) in args.iter().enumerate() {
                llvm += &format!(
                    "{}{} {}",
                    if i == 0 { "" } else { ", " },
                    to_llvm_type(&arg_types[i]),
                    context.to_expression(arg)
                );
            }
            llvm += ")";

            Result::Ok(llvm)
        }
        Instruction::If(value, lambda) => {
            let if_id = context.next_contol_flow();
            Result::Ok(format!(
                "    br i1 {}, label %if{if_id}_true, label %if{if_id}_end\nif{if_id}_true:\n{}    br label %if{if_id}_end\nif{if_id}_end:",
                context.to_expression(value), generate_function_llvm(lambda, context)?))
        }
    }
}

fn generate_function_llvm(
    locals: &Locals,
    context: &mut GenerationContext,
) -> Result<String, String> {
    let mut llvm = String::new();

    for instruction in &locals.ir {
        let word_ir = generate_instruction_llvm(instruction, context, locals)?;
        llvm += &word_ir;
        llvm += "\n";
    }

    Result::Ok(llvm)
}

fn generate_llvm_sig(name: &str, locals: &Locals) -> String {
    let mut llvm = "define ".to_owned();

    if locals.result_types.len() > 1 {
        panic!("support functions with multiple returns");
    } else if let Some(result_type) = locals.result_types.first() {
        llvm += to_llvm_type(result_type);
    } else {
        llvm += "void";
    }

    llvm += " ";
    llvm += name;

    llvm += "(";
    for (i, arg_type) in locals.arg_types.iter().enumerate() {
        if i > 0 {
            llvm += ", ";
        }
        llvm += to_llvm_type(arg_type);

        llvm += " %";
        llvm += &(i + 1).to_string();
    }
    llvm += ") {\n";

    llvm
}

fn generate_returns(locals: &Locals, context: &mut GenerationContext) -> String {
    if locals.result_values.len() > 1 {
        todo!("implement multiple result values from a function");
    } else if let Some(value) = locals.result_values.first() {
        format!(
            "    ret {} {}\n",
            to_llvm_type(
                locals
                    .result_types
                    .first()
                    .expect("result_types shouldn't be empty if result_values aren't")
            ),
            context.to_expression(value)
        )
    } else {
        "    ret void\n".to_owned()
    }
}

pub fn generate_llvm(locals: &Locals, globals: &Globals) -> Result<String, String> {
    let mut llvm =
        "target triple = \"x86_64-pc-windows-msvc19.40.33813\"\n\ndefine i32 @main() {\n"
            .to_owned();

    llvm += &generate_function_llvm(locals, &mut GenerationContext::new())?;
    llvm += "    ret i32 0\n}\n\n";

    for (i, lambda) in globals.lambdas.iter().enumerate() {
        llvm += &generate_llvm_sig(&format!("@__lambda{}", i + 1), lambda);

        let mut context = GenerationContext::new();
        llvm += &generate_function_llvm(lambda, &mut context)?;
        llvm += &generate_returns(lambda, &mut context);

        llvm += "}\n\n";
    }

    for (i, string) in globals.strings.iter().enumerate() {
        llvm += &format!(
            "@__string{} = constant [{} x i8] c\"{string}\\00\"\n",
            i + 1,
            string.len() + 1
        );
    }
    llvm += "\n";

    llvm += "declare i32 @puts(ptr)\n";
    Result::Ok(llvm)
}
