use crate::compile::Arithemtic;
use crate::compile::Globals;
use crate::compile::Instruction;
use crate::compile::Locals;
use crate::compile::Logical;
use crate::compile::Relational;
use crate::compile::Value;

use std::collections::HashMap;

struct GenerationContext {
    last_var_number: i64,
    var_numbers: HashMap<i64, i64>,
}

impl GenerationContext {
    fn new() -> Self {
        Self {
            last_var_number: 0,
            var_numbers: HashMap::new(),
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
            Value::Variable(index) => format!("%{}", self.var_numbers[index]),
            Value::Global(name) => format!("ptr @{name}"),
        }
    }

    fn to_callable(&self, value: &Value) -> String {
        match value {
            Value::IntLiteral(_) => panic!("trying to call int literal"),
            Value::BoolLiteral(_) => panic!("trying to call bool literal"),
            Value::Variable(index) => format!("%{}", self.var_numbers[index]),
            Value::Global(name) => format!("@{name}"),
        }
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

fn generate_instruction_llvm(
    instruction: &Instruction,
    context: &mut GenerationContext,
) -> Result<String, String> {
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
                "    call i32 @puts({})",
                context.to_expression(value)
            ))
        }
        Instruction::Call(value) => {
            Result::Ok(format!("    call void {}()", context.to_callable(value)))
        }
    }
}

fn generate_function_llvm(locals: &Locals) -> Result<String, String> {
    let mut llvm = String::new();

    let mut context = GenerationContext::new();
    for instruction in &locals.ir {
        let word_ir = generate_instruction_llvm(instruction, &mut context)?;
        llvm += &word_ir;
        llvm += "\n";
    }
    Result::Ok(llvm)
}

pub fn generate_llvm(locals: &Locals, globals: &Globals) -> Result<String, String> {
    let mut llvm =
        "target triple = \"x86_64-pc-windows-msvc19.40.33813\"\n\ndefine i32 @main() {\n"
            .to_owned();
    llvm += &generate_function_llvm(locals)?;
    llvm += "    ret i32 0\n}\n\n";

    for (i, lambda) in globals.lambdas.iter().enumerate() {
        llvm += &format!("define void @__lambda{}() {{\n", i + 1);
        llvm += &generate_function_llvm(lambda)?;
        llvm += "    ret void\n}\n\n";
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
