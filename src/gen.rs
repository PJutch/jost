use crate::ir::Arithemtic;
use crate::ir::Function;
use crate::ir::Globals;
use crate::ir::Instruction;
use crate::ir::Logical;
use crate::ir::Relational;
use crate::ir::Type;
use crate::ir::Value;

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

    fn next_var_number_anonymous(&mut self) -> i64 {
        self.last_var_number += 1;
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

fn to_llvm_type_multiple(types: &[Type]) -> String {
    if types.len() > 1 {
        let mut result = "{ ".to_owned();
        for (i, type_) in types.iter().enumerate() {
            if i > 0 {
                result += ", ";
            }

            result += to_llvm_type(type_);
        }
        result += " }";
        result
    } else if let Some(type_) = types.first() {
        to_llvm_type(type_).to_owned()
    } else {
        "void".to_owned()
    }
}

fn generate_instruction_llvm(
    instruction: &Instruction,
    context: &mut GenerationContext,
) -> Result<String, String> {
    match instruction {
        Instruction::Arithemtic(op, a, b, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            Result::Ok(format!(
                "    %{result_var_number} = {} i64 {}, {}\n",
                llvm_arithmetic(*op),
                context.to_expression(a),
                context.to_expression(b),
            ))
        }
        Instruction::Relational(op, a, b, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            Result::Ok(format!(
                "    %{result_var_number} = icmp {} i64 {}, {}\n",
                llvm_relational(*op),
                context.to_expression(a),
                context.to_expression(b),
            ))
        }
        Instruction::Logical(op, a, b, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            match op {
                Logical::And => Result::Ok(format!(
                    "    %{result_var_number} = select i1 {}, i1 {}, i1 false\n",
                    context.to_expression(a),
                    context.to_expression(b)
                )),
                Logical::Or => Result::Ok(format!(
                    "    %{result_var_number} = select i1 {}, i1 true, i1 {}\n",
                    context.to_expression(a),
                    context.to_expression(b)
                )),
            }
        }
        Instruction::Not(value, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            Result::Ok(format!(
                "    %{result_var_number} = icmp eq i1 {}, false\n",
                context.to_expression(value)
            ))
        }
        Instruction::Print(value) => {
            let var_number = context.next_var_number_anonymous();
            Result::Ok(format!(
                "    %{var_number} = call i32 @puts(ptr {})\n",
                context.to_expression(value)
            ))
        }
        Instruction::Exit(value) => {
            context.next_var_number_anonymous();
            Result::Ok(format!(
                "    call void @exit(i32 {})\n    unreachable\n",
                context.to_expression(value)
            ))
        }
        Instruction::Call(value, arg_types, args, result_types, results) => {
            let mut llvm = "    ".to_owned();
            let returned_type = to_llvm_type_multiple(result_types);

            let returned_var_number = if !results.is_empty() {
                let result_var_number = context.next_var_number_anonymous();
                llvm += &format!("%{result_var_number} = call {returned_type} ");
                Option::Some(result_var_number)
            } else {
                llvm += "call void ";
                Option::None
            };

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
            llvm += ")\n";

            if results.len() > 1 {
                let returned_var_number =
                    returned_var_number.expect("results.len() is checked above");
                for (i, result_var) in results.iter().enumerate() {
                    let var_number = context.next_var_number(*result_var);
                    llvm += &format!(
                        "    %{var_number} = extractvalue {returned_type} %{returned_var_number}, {i}\n"
                    );
                }
            } else if let Some(result_var) = results.first() {
                context.var_numbers.insert(
                    *result_var,
                    returned_var_number.expect("results are checked to not be empty above"),
                );
            }

            Result::Ok(llvm)
        }
        Instruction::If(condition, then_block, else_block, phis) => {
            let if_id = context.next_contol_flow();
            let mut llvm = format!(
                "    br label %if{if_id}_start\nif{if_id}_start:\n    br i1 {}, label %if{if_id}_true, label %if{if_id}_else\n",
                context.to_expression(condition)
            );

            llvm += &format!("if{if_id}_true:\n");
            for instruction in &then_block.ir {
                llvm += &generate_instruction_llvm(instruction, context)?;
            }
            llvm += &format!("    br label %if{if_id}_end\n");

            llvm += &format!("if{if_id}_else:\n");
            for instruction in &else_block.ir {
                llvm += &generate_instruction_llvm(instruction, context)?;
            }
            llvm += &format!("    br label %if{if_id}_end\n");

            llvm += &format!("if{if_id}_end:\n");
            for phi in phis {
                llvm += &format!(
                    "    %{} = phi {} [ {}, %if{if_id}_true ], [ {}, %if{if_id}_else ]\n",
                    context.next_var_number(phi.result_var),
                    to_llvm_type(&phi.result_type),
                    context.to_expression(&phi.case1),
                    context.to_expression(&phi.case2)
                )
            }

            Result::Ok(llvm)
        }
        Instruction::Loop(_, _) => todo!("implement loop"),
    }
}

fn generate_function_llvm(
    function: &Function,
    context: &mut GenerationContext,
    numbering_fix: bool,
) -> Result<String, String> {
    let mut llvm = String::new();

    for i in 0..function.arg_types.len() {
        context.next_var_number(i as i64);
    }
    if numbering_fix {
        context.next_var_number_anonymous();
    }

    for instruction in &function.get_single_scope().ir {
        let word_ir = generate_instruction_llvm(instruction, context)?;
        llvm += &word_ir;
    }

    Result::Ok(llvm)
}

fn generate_llvm_sig(name: &str, function: &Function) -> String {
    let mut llvm = "define ".to_owned();
    llvm += &to_llvm_type_multiple(&function.result_types);
    llvm += " ";
    llvm += name;

    llvm += "(";
    for (i, arg_type) in function.arg_types.iter().enumerate() {
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

fn generate_returns(function: &Function, context: &mut GenerationContext) -> String {
    let result_values = &function.get_single_scope().stack;
    let returned_type = to_llvm_type_multiple(&function.result_types);
    if result_values.len() > 1 {
        let mut result = "".to_owned();
        let mut current_struct = "undef".to_owned();
        for (i, value) in result_values.iter().enumerate() {
            let var_number = context.next_var_number_anonymous();
            result += &format!(
                "    %{var_number} = insertvalue {returned_type} {current_struct}, {} {}, {i}\n",
                to_llvm_type(&function.result_types[i]),
                context.to_expression(value)
            );
            current_struct = format!("%{var_number}")
        }
        result += &format!("    ret {returned_type} {current_struct}\n");
        result
    } else if let Some(value) = result_values.first() {
        format!(
            "    ret {} {}\n",
            returned_type,
            context.to_expression(value)
        )
    } else {
        "    ret void\n".to_owned()
    }
}

pub fn generate_llvm(
    function: &Function,
    globals: &Globals,
    numbering_fix: bool,
) -> Result<String, String> {
    let mut llvm =
        "target triple = \"x86_64-pc-windows-msvc19.40.33813\"\n\ndefine i32 @main() {\n"
            .to_owned();

    llvm += &generate_function_llvm(function, &mut GenerationContext::new(), numbering_fix)?;
    llvm += "    ret i32 0\n}\n\n";

    for (i, lambda) in globals.lambdas.iter().enumerate() {
        llvm += &generate_llvm_sig(&format!("@__lambda{}", i + 1), lambda);

        let mut context = GenerationContext::new();
        llvm += &generate_function_llvm(lambda, &mut context, numbering_fix)?;
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
    llvm += "declare void @exit(i32) noreturn\n";
    Result::Ok(llvm)
}
