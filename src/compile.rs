use crate::lex::Lexer;
use crate::lex::Word;
use core::panic;
use std::collections::HashMap;
use std::fmt::Display;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Type {
    Int,
    Bool,
    String,
    FnPtr(Vec<Type>, Vec<Type>),
    List, // TODO: implement lists of type other than Type
    Type_,
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => f.write_str("Int"),
            Type::Bool => f.write_str("Bool"),
            Type::String => f.write_str("String"),
            Type::FnPtr(arg_types, result_types) => {
                f.write_str("fn (")?;
                for (i, arg_type) in arg_types.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    f.write_fmt(format_args!("{arg_type}"))?;
                }
                f.write_str(") -> (")?;
                for (i, result_type) in result_types.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    f.write_fmt(format_args!("{result_type}"))?;
                }
                f.write_str(")")
            }
            Type::List => f.write_str("List"),
            Type::Type_ => f.write_str("Type"),
        }
    }
}

fn display_type_list(types: &[Type]) -> String {
    let mut s = "".to_owned();
    for (i, type_) in types.iter().enumerate() {
        if i > 0 {
            s += " ";
        }
        s += &format!("{type_}");
    }
    s
}

#[derive(Clone, Debug)]
pub enum Value {
    IntLiteral(i64),
    BoolLiteral(bool),
    ListLiteral(Vec<Type>), // TODO: implement lists of type other than Type
    Type(Type),
    Variable(i64),
    Arg(i64),
    Global(String),
}

impl Value {
    fn unwrap_type(self) -> Type {
        match self {
            Value::Type(type_) => type_,
            _ => panic!("unwrap type assumed that value {self:?} is a type"),
        }
    }

    fn unwrap_list_literal(self) -> Vec<Type> {
        match self {
            Value::ListLiteral(types) => types,
            _ => panic!("unwrap list literal assumes that value {self:?} is a list literal"),
        }
    }
}

pub struct Globals {
    global_types: HashMap<String, Type>,
    pub strings: Vec<String>,
    pub lambdas: Vec<Function>,
}

impl Globals {
    pub fn new() -> Self {
        Self {
            global_types: HashMap::new(),
            strings: Vec::new(),
            lambdas: Vec::new(),
        }
    }

    fn new_string(&mut self, s: &str) -> String {
        self.strings.push(s.to_owned());

        let global_name = format!("__string{}", self.strings.len());
        self.global_types.insert(global_name.clone(), Type::String);
        global_name
    }

    fn new_lambda(&mut self, lambda: Function) -> String {
        let global_name = format!("__lambda{}", self.lambdas.len() + 1);
        self.global_types.insert(
            global_name.clone(),
            Type::FnPtr(lambda.arg_types.clone(), lambda.result_types.clone()),
        );

        self.lambdas.push(lambda);

        global_name
    }
}

#[derive(Debug, Clone, Copy)]
struct StackPosition {
    scope: usize,
    item: usize,
}

#[derive(Debug)]
pub struct Scope {
    pub stack: Vec<Value>,
    pub ir: Vec<Instruction>,

    to_borrow: Option<StackPosition>,
}

pub struct Function {
    pub scopes: Vec<Scope>,

    last_var: i64,
    pub var_types: HashMap<i64, Type>,

    pub arg_types: Vec<Type>,
    pub result_types: Vec<Type>,
}

impl Function {
    fn new(arg_types: Vec<Type>, result_types: Vec<Type>) -> Self {
        let n_args = arg_types.len();

        let mut function = Self {
            scopes: Vec::new(),
            last_var: n_args as i64,
            var_types: HashMap::new(),
            arg_types,
            result_types,
        };

        function.new_scope();

        for i in 0..n_args {
            function.push(Value::Arg(i as i64));
        }

        function
    }

    fn over_top_stack_position(&self) -> StackPosition {
        StackPosition {
            scope: self.scopes.len(),
            item: 0,
        }
    }

    fn top_stack_position(&self) -> Option<StackPosition> {
        self.decrement_stack_position(self.over_top_stack_position())
    }

    fn decrement_stack_position(&self, mut pos: StackPosition) -> Option<StackPosition> {
        while pos.item == 0 && pos.scope > 0 {
            if let Some(scope) = self.scopes.get(pos.scope) {
                pos = scope.to_borrow?;
            } else {
                pos.scope -= 1;
                pos.item = self.scopes[pos.scope].stack.len();
            }
        }

        if pos.item != 0 {
            pos.item -= 1;
            Option::Some(pos)
        } else {
            Option::None
        }
    }

    fn at_scope_position(&self, pos: StackPosition) -> &Value {
        &self.scopes[pos.scope].stack[pos.item]
    }

    fn new_scope(&mut self) {
        self.scopes.push(Scope {
            stack: Vec::new(),
            ir: Vec::new(),
            to_borrow: self.top_stack_position(),
        });
    }

    fn pop_scope(&mut self) -> Option<Scope> {
        self.scopes.pop()
    }

    pub fn get_single_scope(&self) -> &Scope {
        if self.scopes.len() > 1 {
            panic!(
                "get_single_scope expects function to have a single scope, it has {}",
                self.scopes.len()
            );
        }
        self.scopes
            .first()
            .expect("get_single_scope expects function to have a scope")
    }

    fn push(&mut self, value: Value) {
        self.scopes
            .last_mut()
            .expect("push expects at least one scope to exist")
            .stack
            .push(value);
    }

    fn pop(&mut self) -> Option<Value> {
        if let Some(last_scope) = self.scopes.last_mut() {
            if let Some(value) = last_scope.stack.pop() {
                return Option::Some(value);
            }

            last_scope.to_borrow.map(|pos| {
                let result = self.at_scope_position(pos).clone();
                self.scopes
                    .last_mut()
                    .expect("scope existing is checked above")
                    .to_borrow = self.decrement_stack_position(pos);
                result
            })
        } else {
            Option::None
        }
    }

    fn add_instruction(&mut self, instruction: Instruction) {
        self.scopes
            .last_mut()
            .expect("add_instruction expects at least one scope to exist")
            .ir
            .push(instruction);
    }

    fn new_var(&mut self, type_: Type) -> i64 {
        self.last_var += 1;
        self.var_types.insert(self.last_var, type_);
        self.last_var
    }

    fn stack_as_string(&self, globals: &Globals) -> String {
        let mut types = Vec::new();

        let mut pos = StackPosition {
            scope: self.scopes.len(),
            item: 0,
        };
        while let Some(new_pos) = self.decrement_stack_position(pos) {
            pos = new_pos;
            types.push(type_of(self.at_scope_position(pos), self, globals));
        }

        types.reverse();

        display_type_list(&types)
    }

    fn pop_of_type(
        &mut self,
        type_: Type,
        globals: &Globals,
        start: i64,
        end: i64,
        lexer: &Lexer,
    ) -> Result<Value, String> {
        if let Some(pos) = self.top_stack_position() {
            let value = self.at_scope_position(pos);
            if type_of(value, self, globals) == type_ {
                return Result::Ok(self.pop().expect("stack is checked to not be empty"));
            }
        }

        Result::Err(lexer.make_error_report(
            start,
            end,
            &format!(
                "expected ... {type_}, found {}",
                self.stack_as_string(globals)
            ),
        ))
    }

    fn pop2_of_type(
        &mut self,
        type1: Type,
        type2: Type,
        globals: &Globals,
        start: i64,
        end: i64,
        lexer: &Lexer,
    ) -> Result<(Value, Value), String> {
        if let Some(pos2) = self.top_stack_position() {
            if let Some(pos1) = self.decrement_stack_position(pos2) {
                if type_of(self.at_scope_position(pos1), self, globals) == type1
                    && type_of(self.at_scope_position(pos2), self, globals) == type2
                {
                    let value2 = self.pop().expect("stack is checked to have 2 values");
                    let value1 = self.pop().expect("stack is checked to have 2 values");
                    return Result::Ok((value1, value2));
                }
            }
        }

        Result::Err(lexer.make_error_report(
            start,
            end,
            &format!(
                "expected ... {type1} {type2}, found {}",
                self.stack_as_string(globals)
            ),
        ))
    }

    fn has_given_types_after(
        &self,
        types: &[Type],
        mut pos: StackPosition,
        globals: &Globals,
    ) -> bool {
        for type_ in types.iter().rev() {
            if let Some(new_pos) = self.decrement_stack_position(pos) {
                pos = new_pos;
                if type_of(self.at_scope_position(pos), self, globals) == *type_ {
                    continue;
                }
            }

            return false;
        }
        true
    }

    fn pop_of_any_type(
        &mut self,
        globals: &Globals,
        start: i64,
        end: i64,
        lexer: &Lexer,
    ) -> Result<Value, String> {
        if let Some(value) = self.pop() {
            return Result::Ok(value);
        }

        Result::Err(lexer.make_error_report(
            start,
            end,
            &format!("expected ... A, found {}", self.stack_as_string(globals)),
        ))
    }

    fn pop2_of_any_type(
        &mut self,
        globals: &Globals,
        start: i64,
        end: i64,
        lexer: &Lexer,
    ) -> Result<(Value, Value), String> {
        if let Some(pos) = self.top_stack_position() {
            if self.decrement_stack_position(pos).is_some() {
                let value2 = self.pop().expect("stack is checked to have 2 values");
                let value1 = self.pop().expect("stack is checked to have 2 values");
                return Result::Ok((value1, value2));
            }
        }

        Result::Err(lexer.make_error_report(
            start,
            end,
            &format!("expected ... A A, found {}", self.stack_as_string(globals)),
        ))
    }
}

fn print_function_ir(function: &Function) {
    for (i, scope) in function.scopes.iter().enumerate() {
        println!("  scope {i}");
        for instruction in &scope.ir {
            println!("    {instruction:?}");
        }
    }
}

pub fn print_ir(function: &Function, globals: &Globals) {
    println!("main");
    print_function_ir(function);
    for (i, lambda) in globals.lambdas.iter().enumerate() {
        println!("__lambda{}", i + 1);
        print_function_ir(lambda);
    }
}

fn type_of(value: &Value, function: &Function, globals: &Globals) -> Type {
    match value {
        Value::IntLiteral(_) => Type::Int,
        Value::BoolLiteral(_) => Type::Bool,
        Value::ListLiteral(_) => Type::List,
        Value::Type(_) => Type::Type_,
        Value::Variable(index) => function.var_types[index].clone(),
        Value::Arg(index) => function.arg_types[*index as usize].clone(),
        Value::Global(name) => globals.global_types[name].clone(),
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Arithemtic {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

impl Arithemtic {
    fn from_id(id: &str) -> Option<Self> {
        match id {
            "+" => Option::Some(Self::Add),
            "-" => Option::Some(Self::Sub),
            "*" => Option::Some(Self::Mul),
            "/" => Option::Some(Self::Div),
            "%" => Option::Some(Self::Mod),
            _ => Option::None,
        }
    }

    fn knows_id(id: &str) -> bool {
        Self::from_id(id).is_some()
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Relational {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl Relational {
    fn from_id(id: &str) -> Option<Self> {
        match id {
            "==" => Option::Some(Self::Eq),
            "!=" => Option::Some(Self::Ne),
            "<" => Option::Some(Self::Lt),
            "<=" => Option::Some(Self::Le),
            ">" => Option::Some(Self::Gt),
            ">=" => Option::Some(Self::Ge),
            _ => Option::None,
        }
    }

    fn knows_id(id: &str) -> bool {
        Self::from_id(id).is_some()
    }
}

#[derive(Debug)]
pub enum Logical {
    And,
    Or,
}

impl Logical {
    fn from_id(id: &str) -> Option<Self> {
        match id {
            "&&" => Option::Some(Self::And),
            "||" => Option::Some(Self::Or),
            _ => Option::None,
        }
    }

    fn knows_id(id: &str) -> bool {
        Self::from_id(id).is_some()
    }
}

#[derive(Debug)]
pub enum Instruction {
    Arithemtic(Arithemtic, Value, Value, i64),
    Relational(Relational, Value, Value, i64),
    Logical(Logical, Value, Value, i64),
    Not(Value, i64),
    Print(Value),
    Call(Value, Vec<Type>, Vec<Value>, Vec<Type>, Vec<i64>),
    If(Value, Scope),
}

fn compile_call(
    current_function: &mut Function,
    globals: &Globals,
    lexer: &Lexer,
    start: i64,
    end: i64,
) -> Result<(), String> {
    if let Some(pos) = current_function.top_stack_position() {
        let fn_ptr = current_function.at_scope_position(pos);
        if let Type::FnPtr(arg_types, result_types) = type_of(fn_ptr, current_function, globals) {
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
            if let Value::Type(type_) = function.at_scope_position(type_pos) {
                let type_ = type_.clone();

                if type_of(function.at_scope_position(value_pos), function, globals) != type_ {
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
            Word::Id(id, start, end) if Arithemtic::knows_id(id) => {
                let (a, b) =
                    function.pop2_of_type(Type::Int, Type::Int, globals, start, end, lexer)?;

                let result_var = function.new_var(Type::Int);
                function.push(Value::Variable(result_var));

                function.add_instruction(Instruction::Arithemtic(
                    Arithemtic::from_id(id).expect(
                        "arithmetic from_id should succeed because it's checked in pattern guard",
                    ),
                    a,
                    b,
                    result_var,
                ));
            }
            Word::Id(id, start, end) if Relational::knows_id(id) => {
                let (a, b) =
                    function.pop2_of_type(Type::Int, Type::Int, globals, start, end, lexer)?;

                let result_var = function.new_var(Type::Bool);
                function.push(Value::Variable(result_var));

                function.add_instruction(Instruction::Relational(
                    Relational::from_id(id).expect(
                        "relational from_id should succeed because it's checked in pattern guard",
                    ),
                    a,
                    b,
                    result_var,
                ));
            }
            Word::Id(id, start, end) if Logical::knows_id(id) => {
                let (a, b) =
                    function.pop2_of_type(Type::Bool, Type::Bool, globals, start, end, lexer)?;

                let result_var = function.new_var(Type::Bool);
                function.push(Value::Variable(result_var));

                function.add_instruction(Instruction::Logical(
                    Logical::from_id(id).expect(
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
            Word::Id("if", start, end) => {
                lexer.consume_and_expect("(")?;
                let condition = function.pop_of_type(Type::Bool, globals, start, end, lexer)?;
                function.new_scope();
                compile_block(lexer, function, globals, false)?;
                let block = function
                    .pop_scope()
                    .expect("scope should becreated by compile block");
                function.add_instruction(Instruction::If(condition, block));
            }
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
                display_type_list(&function.result_types),
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
