use crate::ir::Arithemtic;
use crate::ir::Function;
use crate::ir::Globals;
use crate::ir::Instruction;
use crate::ir::Logical;
use crate::ir::Relational;
use crate::ir::Value;

use crate::types::Type;

use core::panic;
use std::collections::HashMap;

struct GenerationContext {
    generated: Vec<String>,
    last_var_number: i64,
    var_numbers: HashMap<i64, i64>,
    last_control_flow: i64,
    last_label: String,
}

impl GenerationContext {
    fn new() -> Self {
        Self {
            generated: Vec::from([String::new()]),
            last_var_number: 0,
            var_numbers: HashMap::new(),
            last_control_flow: 0,
            last_label: String::new(),
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
            Value::Int32Literal(value) => value.to_string(),
            Value::BoolLiteral(value) => (if *value { "true" } else { "false" }).to_owned(),
            Value::Tuple(_, _) => panic!("tuple literal got to code gen"),
            Value::Array(_, _) => panic!("array literal got to code gen"),
            Value::Slice(_, _) => panic!("slice literal got to code gen"),
            Value::Type(_) => panic!("types can't be used in runtime"),
            Value::Variable(index) | Value::Arg(index) => format!("%{}", self.var_numbers[index]),
            Value::Global(name) | Value::Function(name) => format!("@{name}"),
            Value::Undefined => "undef".to_owned(),
            Value::Zeroed(_, _) => "zeroinitializer".to_owned(),
            Value::Length(_, _) => panic!("length value got to code gen"),
            Value::SizeOf(_) => panic!("sizeof value got to code gen"),
        }
    }

    fn to_callable(&self, value: &Value) -> String {
        match value {
            Value::IntLiteral(_) => panic!("trying to call int literal"),
            Value::Int32Literal(_) => panic!("trying to call int32 literal"),
            Value::BoolLiteral(_) => panic!("trying to call bool literal"),
            Value::Tuple(_, _) => panic!("trying to call a tuple"),
            Value::Array(_, _) => panic!("trying to call an array"),
            Value::Slice(_, _) => panic!("trying to call a slice"),
            Value::Type(_) => panic!("trying to call a type"),
            Value::Variable(index) | Value::Arg(index) => format!("%{}", self.var_numbers[index]),
            Value::Global(name) | Value::Function(name) => format!("@{name}"),
            Value::Zeroed(_, _) => panic!("trying to call a null fn ptr"),
            Value::Undefined => "undef".to_owned(),
            Value::Length(_, _) => panic!("trying to call a length value"),
            Value::SizeOf(_) => panic!("trying to call a sizeof value"),
        }
    }

    fn next_contol_flow(&mut self) -> i64 {
        self.last_control_flow += 1;
        self.last_control_flow
    }

    fn append(&mut self, code: &str) {
        *self
            .generated
            .last_mut()
            .expect("at least one piece of code should exist") += code;
    }

    fn new_block(&mut self) {
        self.generated.push(String::new());
    }

    fn pop_block(&mut self) -> String {
        self.generated
            .pop()
            .expect("at least one piece of code should exist")
    }

    fn clear(&mut self) {
        self.last_var_number = 0;
        self.last_control_flow = 0;

        self.var_numbers.clear();
    }

    fn label(&mut self, type_: &str, subtype: &str, id: i64) {
        let label = format!("{type_}{id}_{subtype}");

        self.append(&label);
        self.append(":\n");

        self.last_label = label;
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
        Relational::Lt => "slt",
        Relational::Le => "sle",
        Relational::Gt => "sgt",
        Relational::Ge => "sge",
    }
}

fn to_llvm_type(type_: &Type) -> String {
    match type_ {
        Type::Int => "i64".to_owned(),
        Type::Int32 => "i32".to_owned(),
        Type::Bool => "i1".to_owned(),
        Type::String | Type::Ptr(_) | Type::FnPtr(_, _) => "ptr".to_owned(),
        Type::Tuple(types) => {
            let mut type_string = "{".to_owned();
            for (i, type_) in types.iter().enumerate() {
                if i > 0 {
                    type_string += ",";
                }
                type_string += " ";
                type_string += &to_llvm_type(type_);
            }
            if !types.is_empty() {
                type_string += " ";
            }
            type_string += "}";
            type_string
        }
        Type::Array(type_, size) => format!("[{size} x {}]", to_llvm_type(type_)),
        Type::Slice(_) => "{ ptr, i64}".to_owned(),
        Type::Typ => panic!("types can't be used at runtime"),
        Type::TypVar(_) => panic!("unresolved type var found in code gen"),
    }
}
fn to_llvm_type_multiple(types: &[Type]) -> String {
    if types.len() > 1 {
        let mut result = "{ ".to_owned();
        for (i, type_) in types.iter().enumerate() {
            if i > 0 {
                result += ", ";
            }

            result += &to_llvm_type(type_);
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
) -> Result<(), String> {
    match instruction {
        Instruction::Bogus => panic!("bogus instruction got to code gen"),
        Instruction::Arithemtic(op, a, b, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            context.append(&format!(
                "    %{result_var_number} = {} i64 {}, {}\n",
                llvm_arithmetic(*op),
                context.to_expression(a),
                context.to_expression(b),
            ));
        }
        Instruction::Relational(op, a, b, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            context.append(&format!(
                "    %{result_var_number} = icmp {} i64 {}, {}\n",
                llvm_relational(*op),
                context.to_expression(a),
                context.to_expression(b),
            ))
        }
        Instruction::Relational32(op, a, b, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            context.append(&format!(
                "    %{result_var_number} = icmp {} i32 {}, {}\n",
                llvm_relational(*op),
                context.to_expression(a),
                context.to_expression(b),
            ))
        }
        Instruction::Logical(op, a, b, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            match op {
                Logical::And => context.append(&format!(
                    "    %{result_var_number} = select i1 {}, i1 {}, i1 false\n",
                    context.to_expression(a),
                    context.to_expression(b)
                )),
                Logical::Or => context.append(&format!(
                    "    %{result_var_number} = select i1 {}, i1 true, i1 {}\n",
                    context.to_expression(a),
                    context.to_expression(b)
                )),
            }
        }
        Instruction::Not(value, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            context.append(&format!(
                "    %{result_var_number} = icmp eq i1 {}, false\n",
                context.to_expression(value)
            ))
        }
        Instruction::Alloca(value, type_, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            context.append(&format!(
                "    %{result_var_number} = alloca {}\n",
                to_llvm_type(type_)
            ));
            context.append(&format!(
                "    store {} {}, ptr %{result_var_number}\n",
                to_llvm_type(type_),
                context.to_expression(value)
            ));
        }
        Instruction::Load(ptr, type_, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            context.append(&format!(
                "    %{result_var_number} = load {}, ptr {}\n",
                to_llvm_type(type_),
                context.to_expression(ptr)
            ));
        }
        Instruction::Store(ptr, type_, value) => {
            context.append(&format!(
                "    store {} {}, ptr {}\n",
                to_llvm_type(type_),
                context.to_expression(value),
                context.to_expression(ptr)
            ));
        }
        Instruction::Malloc(size, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            context.append(&format!(
                "    %{result_var_number} = call ptr @malloc(i64 {})\n",
                context.to_expression(size)
            ));
        }
        Instruction::Free(ptr) => {
            context.append(&format!(
                "    call void @free(ptr {})\n",
                context.to_expression(ptr)
            ));
        }
        Instruction::InsertValue(tuple, tuple_type, value, value_type, index, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            context.append(&format!(
                "    %{result_var_number} = insertvalue {} {}, {} {}, {index}\n",
                to_llvm_type(tuple_type),
                context.to_expression(tuple),
                to_llvm_type(value_type),
                context.to_expression(value),
            ));
        }
        Instruction::ExtractValue(tuple, tuple_type, _, index, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            context.append(&format!(
                "    %{result_var_number} = extractvalue {} {}, {index}\n",
                to_llvm_type(tuple_type),
                context.to_expression(tuple),
            ));
        }
        Instruction::InsertValueDyn(_, _, _, _, _, _) => {
            panic!("Dynamic insertvalue got to codegen")
        }
        Instruction::ExtractValueDyn(_, _, _, _, _) => {
            panic!("Dynamic extractvalue got to codegen")
        }
        Instruction::GetElementPtr(type_, ptr, index, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            context.append(&format!(
                "    %{result_var_number} = getelementptr {}, ptr {}, i64 0, i64 {}\n",
                to_llvm_type(type_),
                context.to_expression(ptr),
                context.to_expression(index)
            ));
        }
        Instruction::GetNeighbourPtr(type_, ptr, index, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            context.append(&format!(
                "    %{result_var_number} = getelementptr {}, ptr {}, i64 {}\n",
                to_llvm_type(type_),
                context.to_expression(ptr),
                context.to_expression(index)
            ));
        }
        Instruction::Bitcast(value, from, to, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            context.append(&format!(
                "    %{result_var_number} = bitcast {} {} to {}\n",
                to_llvm_type(from),
                context.to_expression(value),
                to_llvm_type(to)
            ));
        }
        Instruction::Print(_, _) => panic!("print instruction got to code gen"),
        Instruction::Input(_, _, _) => panic!("input instruction got to code gen"),
        Instruction::Putstr(value) => {
            let var_number = context.next_var_number_anonymous();
            context.append(&format!(
                "    %{var_number} = call i32 @puts(ptr {})\n",
                context.to_expression(value)
            ))
        }
        Instruction::Printf(format_string, args) => {
            let var_number = context.next_var_number_anonymous();
            context.append("    %");
            context.append(&var_number.to_string());
            context.append(" = call i32 @printf(ptr ");
            context.append(&context.to_expression(format_string));
            for arg in args {
                // TODO: support argument types other than Int
                context.append(", i64 ");
                context.append(&context.to_expression(arg));
            }
            context.append(")\n");
        }
        Instruction::GetsS(buf, size, result_var) => {
            context.append("    ");
            if let Some(var) = result_var {
                let var_number = context.next_var_number(*var);
                context.append(&format!("%{var_number} = "));
            } else {
                context.next_var_number_anonymous();
            }
            context.append("call ptr @gets_s(ptr ");
            context.append(&context.to_expression(buf));
            context.append(", i64 ");
            context.append(&context.to_expression(size));
            context.append(")\n");
        }
        Instruction::Strcmp(lhs, rhs, result_var) => {
            let result_var_number = context.next_var_number(*result_var);
            context.append("    %");
            context.append(&result_var_number.to_string());
            context.append(" = call i32 @strcmp(ptr ");
            context.append(&context.to_expression(lhs));
            context.append(", ptr ");
            context.append(&context.to_expression(rhs));
            context.append(")\n");
        }
        Instruction::Exit(value) => {
            context.next_var_number_anonymous();
            context.append(&format!(
                "    call void @exit(i32 {})\n    unreachable\n",
                context.to_expression(value)
            ))
        }
        Instruction::Call(value, arg_types, args, result_types, results) => {
            context.append("    ");
            let returned_type = to_llvm_type_multiple(result_types);

            let returned_var_number = if !results.is_empty() {
                let result_var_number = context.next_var_number_anonymous();
                context.append(&format!("%{result_var_number} = call {returned_type} "));
                Option::Some(result_var_number)
            } else {
                context.append("call void ");
                Option::None
            };

            context.append(&context.to_callable(value));

            context.append("(");
            for (i, arg) in args.iter().enumerate() {
                context.append(&format!(
                    "{}{} {}",
                    if i == 0 { "" } else { ", " },
                    to_llvm_type(&arg_types[i]),
                    context.to_expression(arg)
                ));
            }
            context.append(")\n");

            if results.len() > 1 {
                let returned_var_number =
                    returned_var_number.expect("results.len() is checked above");
                for (i, result_var) in results.iter().enumerate() {
                    let var_number = context.next_var_number(*result_var);
                    context.append(&format!(
                        "    %{var_number} = extractvalue {returned_type} %{returned_var_number}, {i}\n"
                    ));
                }
            } else if let Some(result_var) = results.first() {
                context.var_numbers.insert(
                    *result_var,
                    returned_var_number.expect("results are checked to not be empty above"),
                );
            }
        }
        Instruction::If(condition, then_block, else_block, phis) => {
            let if_id = context.next_contol_flow();

            context.append(&format!(
                "    br i1 {}, label %if{if_id}_true, label %if{if_id}_false\n",
                context.to_expression(condition)
            ));

            context.label("if", "true", if_id);
            for instruction in &then_block.ir {
                generate_instruction_llvm(instruction, context)?
            }
            if !then_block.no_return {
                context.append(&format!("    br label %if{if_id}_end\n"));
            }
            let then_label = context.last_label.clone();

            context.label("if", "false", if_id);
            for instruction in &else_block.ir {
                generate_instruction_llvm(instruction, context)?;
            }
            if !else_block.no_return {
                context.append(&format!("    br label %if{if_id}_end\n"));
            }
            let else_label = context.last_label.clone();

            context.label("if", "end", if_id);
            for phi in phis {
                let code = format!(
                    "    %{} = phi {} [ {}, %{then_label} ], [ {}, %{else_label} ]\n",
                    context.next_var_number(phi.result_var),
                    to_llvm_type(&phi.result_type),
                    context.to_expression(&phi.case1),
                    context.to_expression(&phi.case2)
                );
                context.append(&code);
            }
        }
        Instruction::Loop(phis, body_scope) => {
            let start_label = context.last_label.clone();

            let loop_id = context.next_contol_flow();
            context.append(&format!("    br label %loop{loop_id}_body\n"));
            context.label("loop", "body", loop_id);

            let phi_var_numbers: Vec<i64> = phis
                .iter()
                .map(|phi| context.next_var_number(phi.result_var))
                .collect();

            context.new_block();
            for instruction in &body_scope.ir {
                generate_instruction_llvm(instruction, context)?;
            }
            let body_llvm = context.pop_block();
            let body_label = context.last_label.clone();

            for (i, phi) in phis.iter().enumerate() {
                context.append(&format!(
                    "    %{} = phi {} [ {}, %{start_label} ], [ {}, %{body_label} ]\n",
                    phi_var_numbers[i],
                    to_llvm_type(&phi.result_type),
                    context.to_expression(&phi.case1),
                    context.to_expression(&phi.case2)
                ));
            }

            context.append(&body_llvm);

            context.append(&format!("    br label %loop{loop_id}_body\n"));
        }
        Instruction::While(phis, test_scope, test, body_scope) => {
            let start_label = context.last_label.clone();

            let while_id = context.next_contol_flow();
            context.append(&format!("    br label %while{while_id}_test\n"));
            context.label("while", "test", while_id);

            let mut phi_var_numbers = Vec::new();
            for phi in phis {
                phi_var_numbers.push(context.next_var_number(phi.result_var));
            }

            context.new_block();
            for instruction in &test_scope.ir {
                generate_instruction_llvm(instruction, context)?;
            }
            let test_llvm = context.pop_block();

            context.new_block();
            context.label("while", "body", while_id);
            for instruction in &body_scope.ir {
                generate_instruction_llvm(instruction, context)?;
            }
            let body_llvm = context.pop_block();
            let body_label = context.last_label.clone();

            for (i, phi) in phis.iter().enumerate() {
                context.append(&format!(
                    "    %{} = phi {} [ {}, %{start_label} ], [ {}, %{body_label} ]\n",
                    phi_var_numbers[i],
                    to_llvm_type(&phi.result_type),
                    context.to_expression(&phi.case1),
                    context.to_expression(&phi.case2)
                ));
            }

            context.append(&test_llvm);
            context.append(&format!(
                "    br i1 {}, label %while{while_id}_body, label %while{while_id}_end\n",
                context.to_expression(test)
            ));
            context.append(&body_llvm);
            context.append(&format!("    br label %while{while_id}_test\n"));
            context.label("while", "end", while_id);
        }
        Instruction::Return(values, types) => {
            let returned_type = to_llvm_type_multiple(types);
            if values.len() > 1 {
                let mut current_struct = "undef".to_owned();
                for (i, value) in values.iter().enumerate() {
                    let var_number = context.next_var_number_anonymous();
                    context.append(&format!(
                        "    %{var_number} = insertvalue {returned_type} {current_struct}, {} {}, {i}\n",
                        to_llvm_type(&types[i]),
                        context.to_expression(value)
                    ));
                    current_struct = format!("%{var_number}")
                }
                context.append(&format!("    ret {returned_type} {current_struct}\n"));
            } else if let Some(value) = values.first() {
                context.append(&format!(
                    "    ret {} {}\n",
                    returned_type,
                    context.to_expression(value)
                ));
            } else {
                context.append("    ret void\n");
            }
        }
    }
    Result::Ok(())
}

fn generate_function_llvm(
    function: &Function,
    context: &mut GenerationContext,
    numbering_fix: bool,
) -> Result<(), String> {
    for i in 0..function.arg_types.len() {
        context.next_var_number(i as i64);
    }
    if numbering_fix {
        context.next_var_number_anonymous();
    }

    context.append("entry:\n");
    context.last_label = "entry".to_owned();

    for instruction in &function.get_single_scope().ir {
        generate_instruction_llvm(instruction, context)?;
    }

    Result::Ok(())
}

fn generate_llvm_sig(name: &str, function: &Function, context: &mut GenerationContext) {
    context.append("define ");
    context.append(&to_llvm_type_multiple(&function.result_types));
    context.append(" ");
    context.append(name);

    context.append("(");
    for (i, arg_type) in function.arg_types.iter().enumerate() {
        if i > 0 {
            context.append(", ");
        }
        context.append(&to_llvm_type(arg_type));

        context.append(" %");
        context.append(&(i + 1).to_string());
    }
    context.append(") {\n");
}

pub fn generate_llvm(
    function: &Function,
    globals: &Globals,
    numbering_fix: bool,
) -> Result<String, String> {
    let mut context = GenerationContext::new();
    context
        .append("target triple = \"x86_64-pc-windows-msvc19.40.33813\"\n\ndefine i32 @main() {\n");

    generate_function_llvm(function, &mut context, numbering_fix)?;
    context.append("    ret i32 0\n}\n\n");

    for (i, lambda) in globals.lambdas.iter().enumerate() {
        context.clear();
        generate_llvm_sig(&format!("@__lambda{}", i + 1), lambda, &mut context);

        generate_function_llvm(lambda, &mut context, numbering_fix)?;

        context.append("}\n\n");
    }

    for (name, function) in &globals.functions {
        context.clear();
        generate_llvm_sig(&("@".to_owned() + name), function, &mut context);

        generate_function_llvm(function, &mut context, numbering_fix)?;

        context.append("}\n\n");
    }

    for (i, string) in globals.strings.iter().enumerate() {
        context.append(&format!(
            "@__string{} = constant [{} x i8] c\"{string}\\00\"\n",
            i + 1,
            string.len() + 1
        ));
    }
    context.append("\n");

    context.append("declare i32 @puts(ptr)\n");
    context.append("declare void @exit(i32) noreturn\n");
    context.append("declare i32 @printf(ptr, ...)\n");
    context.append("declare ptr @gets_s(ptr, i64)\n");
    context.append("declare i32 @strcmp(ptr, ptr)\n");
    context.append("declare ptr @malloc(i64)\n");
    context.append("declare void @free(ptr)\n");

    context.append("@__string_buf = global [256 x i8] zeroinitializer, align 1\n");
    context.append("@__string_true = constant [5 x i8] c\"true\\00\"\n");

    Result::Ok(context.pop_block())
}
