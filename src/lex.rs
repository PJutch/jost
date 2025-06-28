#[derive(Debug)]
pub enum Word<'a> {
    Id(&'a str, i64, i64),
    Int(i64, i64, i64),
    String(&'a str, i64, i64),
}

fn get_byte(s: &str, index: usize) -> Option<u8> {
    s.as_bytes().get(index).copied()
}

fn parse_token(code: &str, start: i64, end: i64) -> Option<Word> {
    let token = &code[(start as usize)..(end as usize)];
    if token.bytes().all(|c| c.is_ascii_whitespace()) {
        Option::None
    } else if token.bytes().all(|c| c.is_ascii_digit()) {
        let mut value = 0i64;
        for digit in token.bytes() {
            value *= 10;
            value += (digit - b'0') as i64
        }
        Option::Some(Word::Int(value, start, end))
    } else {
        Option::Some(Word::Id(token, start, end))
    }
}

pub struct Lexer<'a, 'b> {
    code: &'a str,
    file_name: &'b str,
    pub current_byte: usize,
}

impl<'a, 'b> Lexer<'a, 'b> {
    pub fn new(code: &'a str, file_name: &'b str) -> Self {
        Self {
            code,
            file_name,
            current_byte: 0,
        }
    }

    pub fn next_word(&mut self) -> Option<Word<'a>> {
        let mut token_start = self.current_byte;
        let mut quoted = false;
        while self.current_byte <= self.code.len() {
            let current_byte = self.current_byte;
            self.current_byte += 1;

            if get_byte(self.code, current_byte).is_some_and(|c| c == b'"') {
                if quoted {
                    return Option::Some(Word::String(
                        &self.code[token_start..current_byte],
                        token_start as i64,
                        current_byte as i64,
                    ));
                }
                token_start = self.current_byte;
                quoted = true;
            } else if !quoted
                && get_byte(self.code, current_byte)
                    .is_none_or(|c| c == b')' && token_start + 1 < current_byte)
            {
                if let Option::Some(token) =
                    parse_token(self.code, token_start as i64, current_byte as i64)
                {
                    self.current_byte -= 1;
                    return Option::Some(token);
                }
                token_start = current_byte + 1;
            } else if !quoted
                && get_byte(self.code, current_byte).is_none_or(|c| c.is_ascii_whitespace())
            {
                if let Option::Some(token) =
                    parse_token(self.code, token_start as i64, current_byte as i64)
                {
                    return Option::Some(token);
                }
                token_start = self.current_byte;
            }
        }
        Option::None
    }

    pub fn is_empty(&self) -> bool {
        for i in self.current_byte..self.code.len() {
            if get_byte(self.code, i).is_some_and(|c| !c.is_ascii_whitespace()) {
                return false;
            }
        }
        true
    }

    pub fn debug_print(code: &'a str) {
        let mut lexer = Self::new(code, "");
        while let Some(word) = lexer.next_word() {
            println!("{word:?}");
        }
    }

    fn get_line_column(&self, position: i64) -> (i64, i64) {
        let mut current_line = 0;
        let mut last_line_start = 0;
        for (i, char) in self.code.bytes().enumerate() {
            if char == b'\n' {
                current_line += 1;
                last_line_start = (i + 1) as i64;
            }

            if i as i64 > position {
                break;
            }
        }
        (current_line, position - last_line_start)
    }

    pub fn make_error_report(&self, position: i64, message: &str) -> String {
        let (line, column) = self.get_line_column(position);
        let line = line + 1;
        let column = column + 1;
        format!("{}:{line}:{column}:[{position}]: {message}", self.file_name)
    }
}
