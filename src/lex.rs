#[derive(Debug, PartialEq, Eq)]
pub enum Word<'a> {
    Id(&'a str),
    Int(i64),
    String(&'a str),
}

#[derive(Debug, Clone, Copy)]
pub struct Location {
    start: i64,
    end: i64,
}

impl Location {
    pub fn char_at(position: i64) -> Location {
        Location {
            start: position,
            end: position + 1,
        }
    }
}

fn get_byte(s: &str, index: usize) -> Option<u8> {
    s.as_bytes().get(index).copied()
}

fn parse_token(code: &str, start: i64, end: i64) -> Option<(Word, Location)> {
    let token = &code[(start as usize)..(end as usize)];
    if token.bytes().all(|c| c.is_ascii_whitespace()) {
        Option::None
    } else if token.bytes().all(|c| c.is_ascii_digit()) {
        let mut value = 0i64;
        for digit in token.bytes() {
            value *= 10;
            value += (digit - b'0') as i64
        }
        Option::Some((Word::Int(value), Location { start, end }))
    } else {
        Option::Some((Word::Id(token), Location { start, end }))
    }
}

fn underline(start: i64, end: i64) -> String {
    let mut s = "".to_owned();
    for _ in 0..start {
        s += " ";
    }
    for _ in start..end {
        s += "^";
    }
    s
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

    pub fn next_word(&mut self) -> Option<(Word<'a>, Location)> {
        let mut token_start = self.current_byte;
        let mut quoted = false;
        while self.current_byte <= self.code.len() {
            let current_byte = self.current_byte;
            self.current_byte += 1;

            if get_byte(self.code, current_byte).is_some_and(|c| c == b'"') {
                if quoted {
                    return Option::Some((
                        Word::String(&self.code[token_start..current_byte]),
                        Location {
                            start: token_start as i64,
                            end: current_byte as i64,
                        },
                    ));
                }
                token_start = self.current_byte;
                quoted = true;
            } else if !quoted
                && get_byte(self.code, current_byte)
                    .is_none_or(|c| c == b')' && token_start < current_byte)
            {
                if let Option::Some(token) =
                    parse_token(self.code, token_start as i64, current_byte as i64)
                {
                    self.current_byte -= 1;
                    return Option::Some(token);
                }
                token_start = current_byte + 1;
            } else if !quoted && get_byte(self.code, current_byte).is_some_and(|c| c == b'(') {
                if let Option::Some(token) =
                    parse_token(self.code, token_start as i64, (current_byte + 1) as i64)
                {
                    return Option::Some(token);
                }
                panic!("token contains a non-whitespace ( by construction")
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
        while let Some((word, location)) = lexer.next_word() {
            println!("{word:?} at {location:?}");
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

    fn nth_line(&self, line: i64) -> &'a str {
        let mut current_line = 0;
        let mut last_line_start = 0;

        let mut target_line_start = 0;
        let mut target_line_end = 0;

        for (i, char) in self.code.bytes().enumerate() {
            if char == b'\n' {
                current_line += 1;
                last_line_start = i + 1;
            }

            if current_line == line {
                target_line_start = last_line_start;
                target_line_end = self.code.len() - 1;
            } else if current_line == line + 1 {
                target_line_end = last_line_start - 1;
                break;
            }
        }

        &self.code[target_line_start..target_line_end]
    }

    pub fn make_error_report(&self, location: Location, message: &str) -> String {
        let (line, column) = self.get_line_column(location.start);
        format!(
            "{}:{}:{}:[{}]: {message}\n{}\n{}",
            self.file_name,
            line + 1,
            column + 1,
            location.start,
            self.nth_line(line),
            underline(column, column + location.end - location.start)
        )
    }

    pub fn consume_and_expect(&mut self, expected: &str) -> Result<(), String> {
        if let Some((Word::Id(id), location)) = self.next_word() {
            if id == expected {
                Result::Ok(())
            } else {
                Result::Err(
                    self.make_error_report(location, &format!("expected {expected}, found {id}")),
                )
            }
        } else {
            Result::Err(self.make_error_report(
                Location::char_at(self.current_byte as i64),
                &format!("expected {expected}, found eof"),
            ))
        }
    }

    pub fn try_consume(&mut self, expected: &str) -> bool {
        let old_current_byte = self.current_byte;

        if let Some((Word::Id(id), _)) = self.next_word() {
            if id == expected {
                return true;
            }
        }

        self.current_byte = old_current_byte;
        false
    }
}
