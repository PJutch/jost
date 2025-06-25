#[derive(Debug)]
pub enum Word<'a> {
    Id(&'a str),
    Int(i64),
    String(&'a str),
}

fn get_byte(s: &str, index: usize) -> Option<u8> {
    s.as_bytes().get(index).copied()
}

fn parse_token(token: &str) -> Option<Word> {
    if token.bytes().all(|c| c.is_ascii_whitespace()) {
        Option::None
    } else if token.bytes().all(|c| c.is_ascii_digit()) {
        let mut value = 0i64;
        for digit in token.bytes() {
            value *= 10;
            value += (digit - b'0') as i64
        }
        Option::Some(Word::Int(value))
    } else {
        Option::Some(Word::Id(token))
    }
}

pub struct Lexer<'a> {
    code: &'a str,
    current_byte: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(code: &'a str) -> Self {
        Self {
            code,
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
                    return Option::Some(Word::String(&self.code[token_start..current_byte]));
                }
                token_start = self.current_byte;
                quoted = true;
            } else if !quoted
                && get_byte(self.code, current_byte)
                    .is_none_or(|c| c == b')' && token_start + 1 < current_byte)
            {
                if let Option::Some(token) = parse_token(&self.code[token_start..current_byte]) {
                    self.current_byte -= 1;
                    return Option::Some(token);
                }
                token_start = current_byte;
            } else if !quoted && get_byte(self.code, current_byte).is_none_or(|c| c == b'(') {
                if let Option::Some(token) = parse_token(&self.code[token_start..=current_byte]) {
                    return Option::Some(token);
                }
                token_start = self.current_byte;
            } else if !quoted
                && get_byte(self.code, current_byte).is_none_or(|c| c.is_ascii_whitespace())
            {
                if let Option::Some(token) = parse_token(&self.code[token_start..current_byte]) {
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
        let mut lexer = Self::new(code);
        while let Some(word) = lexer.next_word() {
            println!("{word:?}");
        }
    }
}
