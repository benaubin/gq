use std::borrow::Cow;

use super::{ParserError, ParserErrorKind, Position, Token};

macro_rules! punctuator {
    [ ! ] => { TokenContent::Exclamation };
    [ $ ] => { TokenContent::DollarSign };
    ( () ) => { (TokenContent::LeftParen, TokenContent::RightParen) };
    [ ... ] => { TokenContent::Ellipses };
    [ : ] => { TokenContent::Colon };
    [ = ] => { TokenContent::Equals };
    [ @ ] => { TokenContent::At };
    [ [] ] => { (TokenContent::LeftBracket, TokenContent::RightBracket) };
    ( {} ) => { (TokenContent::LeftCurlyBracket, TokenContent::RightCurlyBracket) };
    [ | ] => { TokenContent::Pipe };
}

pub struct Tokenizer<'src> {
    source: &'src str,
    pos: Position,

    peeked: Option<Result<Token<'src>, ParserError>>,
}

impl<'src> Tokenizer<'src> {
    pub fn new(source: &'src str) -> Self {
        Tokenizer {
            source,
            pos: Position {
                idx: 0,
                line: 1,
                line_start_idx: 0,
            },
            peeked: None
        }
    }

    #[inline]
    pub const fn pos(&self) -> Position {
        self.pos
    }

    pub fn peek_token(&mut self) -> Option<Result<&Token<'src>, ParserError>> {
        self.peeked = self.next();
        self.peeked.as_ref().map(|peeked| match peeked {
            Ok(token) => Ok(token),
            Err(err) => Err(err.clone()),
        })
    }

    #[inline]
    fn peek_byte(&self) -> Option<u8> {
        self.source.as_bytes().get(self.pos.idx).map(|b| *b)
    }

    #[inline]
    fn peek_next_byte(&self) -> Option<u8> {
        self.source.as_bytes().get(self.pos.idx + 1).map(|b| *b)
    }

    #[inline]
    fn peek_bytes(&self, len: usize) -> Option<&[u8]> {
        self.source.as_bytes().get(self.pos.idx..)?.get(..len)
    }

    fn handle_line_terminator(&mut self) {
        debug_assert!(matches!(self.peek_byte(), Some(b'\r') | Some(b'\n')));

        // line terminator

        // test for \r\n, which should be treated as a single line terminator
        if let Some(b"\r\n") = self.peek_bytes(2) {
            // skip an extra character, in order to treat the \r\n as a single line terminator
            self.pos.idx += 1;
        }

        self.pos.line += 1;
        self.pos.line_start_idx = self.pos.idx + 1;
    }

    fn skip_ignored(&mut self) {
        loop {
            const UNICODE_BOM: &[u8] = "\u{FEFF}".as_bytes();
            const UNICODE_BOM_0: u8 = UNICODE_BOM[0];

            let byte = match self.peek_byte() {
                Some(b) => b,
                None => return,
            };

            match byte {
                UNICODE_BOM_0 if self.peek_bytes(UNICODE_BOM.len()) == Some(UNICODE_BOM) => {
                    // unicode byte order mark, ignored
                }
                b'\t' | b' ' | b',' => { /* whitespace or ignored comma, ignored */ }
                b'\r' | b'\n' => self.handle_line_terminator(),
                b'#' => {
                    // comment
                    // skip characters until newline
                    while !matches!(
                        self.source.as_bytes().get(self.pos.idx + 1),
                        None | Some(b'\r') | Some(b'\n')
                    ) {
                        self.pos.idx += 1;
                    }
                }
                _ => return,
            }

            self.pos.idx += 1;
        }
    }
}

impl<'src> Iterator for Tokenizer<'src> {
    type Item = Result<Token<'src>, ParserError>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(peeked) = self.peeked.take() {
            return Some(peeked);
        }

        self.skip_ignored();

        let byte = self.peek_byte()?;

        let start_pos = self.pos;

        let token = match byte {
            b'!' => punctuator![!],
            b'$' => punctuator! [ $ ],
            b'(' => punctuator![()].0,
            b')' => punctuator![()].1,
            b'.' if self.peek_bytes(3) == Some(b"...") => {
                self.pos.idx += 2; // shift two extra positions
                punctuator! [ ... ]
            }
            b':' => punctuator! [ : ],
            b'=' => punctuator! [ = ],
            b'@' => punctuator! [ @ ],
            b'[' => punctuator![[]].0,
            b']' => punctuator![[]].1,
            b'{' => punctuator![{}].0,
            b'}' => punctuator![{}].1,
            b'|' => punctuator! [ | ],
            b'A'..=b'Z' | b'a'..=b'z' | b'_' => {
                // name

                while matches!(
                    self.peek_next_byte(),
                    Some(b'A'..=b'Z') | Some(b'0'..=b'9') | Some(b'a'..=b'z') | Some(b'_')
                ) {
                    self.pos.idx += 1;
                }

                TokenContent::Name(&self.source[start_pos.idx..=self.pos.idx])
            }
            b'-' | b'0'..=b'9' => {
                while matches!(self.peek_next_byte(), Some(b'0'..=b'9')) {
                    self.pos.idx += 1;
                }

                // track if we have a float to determine parsing strategy
                let mut is_float = false;

                // parse fractional part
                if matches!(self.peek_next_byte(), Some(b'.')) {
                    self.pos.idx += 1;

                    while matches!(self.peek_next_byte(), Some(b'0'..=b'9')) {
                        self.pos.idx += 1;
                    }

                    is_float = true;
                }

                // parse exponent part
                if matches!(self.peek_next_byte(), Some(b'E') | Some(b'e')) {
                    self.pos.idx += 1;

                    if matches!(self.peek_next_byte(), Some(b'+') | Some(b'-')) {
                        self.pos.idx += 1;
                    }

                    while matches!(self.peek_next_byte(), Some(b'0'..=b'9')) {
                        self.pos.idx += 1;
                    }

                    is_float = true;
                }

                let num = &self.source[start_pos.idx..=self.pos.idx];

                if is_float {
                    match num.parse::<f32>() {
                        Ok(num) => TokenContent::FloatValue(num),
                        Err(_) => {
                            return Some(Err(ParserErrorKind::Invalid("float").at(start_pos)))
                        }
                    }
                } else {
                    match num.parse::<i32>() {
                        Ok(num) => TokenContent::IntValue(num),
                        Err(_) => return Some(Err(ParserErrorKind::Invalid("int").at(start_pos))),
                    }
                }
            }
            b'"' => {
                if self.peek_bytes(3) == Some(br#"""""#) {
                    // block string

                    // move position forward from <">"" to ""<">
                    self.pos.idx += 2;

                    let mut lines: Vec<Cow<'src, str>> = Vec::new();

                    {
                        // collect lines
                        let mut string_start = self.pos.idx + 1;
                        let mut current_line = None::<String>;

                        // call on the character after a line to push the previous line onto the lines list

                        macro_rules! push_last_line {
                            {} => {
                                let line_tail = &self.source[string_start..self.pos.idx];
                                let line = match current_line.take() {
                                    Some(mut line) => {
                                        line.push_str(line_tail);
                                        Cow::Owned(line)
                                    }
                                    None => Cow::Borrowed(line_tail),
                                };
                                lines.push(line);
                            }
                        }

                        loop {
                            let byte = match self.peek_next_byte() {
                                Some(byte) => byte,
                                None => {
                                    return Some(Err(
                                        ParserErrorKind::Unexpected("EOF").at(self.pos)
                                    ))
                                }
                            };

                            match byte {
                                b'"' => {
                                    if let Some(potential_str) = self.peek_bytes(4) {
                                        let triple_quote = potential_str[1] == b'"'
                                            && potential_str[2] == b'"'
                                            && potential_str[3] == b'"';
                                        if triple_quote {
                                            if potential_str[0] == b'\\' {
                                                // escaped triple quote

                                                let str = current_line.get_or_insert(String::new());

                                                str.push_str(
                                                    &self.source[string_start..self.pos.idx],
                                                );
                                                str.push_str(r#"""""#);

                                                self.pos.idx += 2; // skip an extra 2 bytes, from <*>""" to *"<">"

                                                string_start = self.pos.idx + 2;
                                            } else {
                                                self.pos.idx += 1;
                                                push_last_line!();
                                                // ending triple quote
                                                break;
                                            }
                                        }
                                    }
                                    self.pos.idx += 1; // from <*>" to *<">
                                }
                                b'\r' | b'\n' => {
                                    self.pos.idx += 1; // from <*>\n to *<\n>

                                    push_last_line!();

                                    self.handle_line_terminator();

                                    string_start = self.pos.idx + 1;
                                }
                                _ => {
                                    self.pos.idx += 1;
                                }
                            }
                        }
                    }

                    // find the min whitespace of all lines except the first
                    let common_ident = lines
                        .iter()
                        .skip(1)
                        .map(|line| {
                            // count whitespace
                            line.bytes()
                                .take_while(|b| matches!(b, b'\t' | b' '))
                                .count()
                        })
                        .min();

                    // remove the common whitespace from all lines except the first
                    if let Some(common_ident) = common_ident {
                        for line in lines.iter_mut().skip(1) {
                            *line = match line {
                                Cow::Borrowed(line) => Cow::Borrowed(&line[common_ident..]),
                                Cow::Owned(line) => Cow::Owned(line[common_ident..].to_owned()),
                            }
                        }
                    }

                    fn just_whitespace(line: &str) -> bool {
                        line.bytes().all(|b| matches!(b, b'\t' | b' '))
                    }

                    // remove lines from back which are only white space
                    while lines
                        .last()
                        .map(|line| just_whitespace(line))
                        .unwrap_or(false)
                    {
                        lines.pop();
                    }

                    let lines = lines.into_iter();

                    // remove lines upfront which are just whitespace
                    let lines =
                        lines.skip_while(|line| line.bytes().all(|b| matches!(b, b'\t' | b' ')));

                    // concatenate the lines, trimming whitespace
                    let formatted = lines
                        .reduce(|mut out, line| {
                            out.to_mut().push_str("\n");
                            out.to_mut().push_str(&*line);
                            out
                        })
                        .unwrap_or_default();

                    // move past the ending triple quote, from <">"" to ""<">
                    self.pos.idx += 3;

                    TokenContent::StringValue(formatted)
                } else {
                    // regular string

                    let mut line = None;

                    let mut str_pos = self.pos.idx + 1;

                    loop {
                        self.pos.idx += 1;

                        let byte = match self.peek_byte() {
                            Some(byte) => byte,
                            None => {
                                return Some(Err(ParserErrorKind::Unexpected("EOF").at(self.pos)))
                            }
                        };

                        match byte {
                            b'\n' | b'\t' => {
                                return Some(Err(
                                    ParserErrorKind::Unexpected("newline").at(self.pos)
                                ))
                            }
                            b'\\' => {
                                // escape

                                let line = line.get_or_insert(String::new());
                                line.push_str(&self.source[str_pos..self.pos.idx]);

                                // from <\>n to \<n>
                                self.pos.idx += 1;

                                let byte = match self.peek_byte() {
                                    Some(byte) => byte,
                                    None => {
                                        return Some(Err(
                                            ParserErrorKind::Unexpected("EOF").at(self.pos)
                                        ))
                                    }
                                };

                                match byte {
                                    b'"' => {
                                        line.push('"');
                                    }
                                    b'/' => {
                                        line.push('/');
                                    }
                                    b'\\' => {
                                        line.push('\\');
                                    }
                                    b'b' => {
                                        line.push('\u{0008}');
                                    }
                                    b'f' => {
                                        line.push('\u{000C}');
                                    }
                                    b'n' => {
                                        line.push('\n');
                                    }
                                    b'r' => {
                                        line.push('\r');
                                    }
                                    b't' => {
                                        line.push('\r');
                                    }
                                    b'u' => {
                                        // unicode codepoint

                                        // from \<u>DDDD to \u<D>DDD
                                        self.pos.idx += 1;

                                        let codepoint = self
                                            .peek_bytes(4)
                                            .and_then(|codepoint| {
                                                std::str::from_utf8(codepoint).ok()
                                            })
                                            .and_then(|codepoint| {
                                                u32::from_str_radix(codepoint, 16).ok()
                                            })
                                            .and_then(|codepoint| std::char::from_u32(codepoint));

                                        match codepoint {
                                            Some(codepoint) => line.push(codepoint),
                                            None => {
                                                return Some(Err(ParserErrorKind::Invalid(
                                                    "Unicode escape",
                                                )
                                                .at(self.pos)))
                                            }
                                        }

                                        // from \u<D>DDD to \uDDD<D>
                                        self.pos.idx += 3;
                                    }
                                    _ => {
                                        return Some(Err(ParserErrorKind::Unexpected(
                                            "Invalid escape code",
                                        )
                                        .at(self.pos)))
                                    }
                                }

                                str_pos = self.pos.idx + 1;
                            }
                            b'"' => break, // end of string
                            _ => {}
                        }
                    }

                    let val = &self.source[str_pos..self.pos.idx];

                    let val = match line {
                        Some(mut line) => {
                            line.push_str(val);
                            Cow::Owned(line)
                        }
                        None => Cow::Borrowed(val),
                    };

                    TokenContent::StringValue(val)
                }
            }
            _ => return Some(Err(ParserErrorKind::Invalid("character").at(start_pos))),
        };

        self.pos.idx += 1;

        Some(Ok(Token {
            content: token,
            pos: start_pos,
        }))
    }
}

#[derive(PartialEq, Clone, Debug)]
pub enum TokenContent<'src> {
    Exclamation,
    DollarSign,
    LeftParen,
    RightParen,
    Ellipses,
    Colon,
    Equals,
    At,
    LeftBracket,
    RightBracket,
    LeftCurlyBracket,
    Pipe,
    RightCurlyBracket,
    /// /[_A-Za-z][_0-9A-Za-z]*/
    Name(&'src str),
    IntValue(i32),
    FloatValue(f32),
    StringValue(Cow<'src, str>),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let mut tokenizer = Tokenizer::new("5");

        let token = tokenizer.next().unwrap().unwrap();

        assert_eq!(
            token,
            Token {
                content: TokenContent::IntValue(5),
                pos: Position {
                    idx: 0,
                    line_start_idx: 0,
                    line: 1
                }
            }
        )
    }

    #[test]
    fn test_whitespace_remover() {
        let mut tokenizer = Tokenizer::new(
            "
        6
        
          $",
        );

        let token = tokenizer.next().unwrap().unwrap();

        assert_eq!(
            token,
            Token {
                content: TokenContent::IntValue(6),
                pos: Position {
                    idx: 9,
                    line_start_idx: 1,
                    line: 2
                }
            }
        );

        let token = tokenizer.next().unwrap().unwrap();

        assert_eq!(token.pos.line(), 4);
        assert_eq!(token.pos.column(), 11);
    }

    macro_rules! expect_tokens {
        (
            $source:literal

            $(
                $( @[$line:literal : $col:literal] )?

                $content:expr
            ),+
        ) => {{
            let mut tokenizer = Tokenizer::new($source);

            $(
                let token = tokenizer.next().unwrap().unwrap();
                assert_eq!(
                    token.content,
                    $content
                );

                $(
                    assert_eq!(token.pos.line(), $line);
                    assert_eq!(token.pos.column(), $col);
                )?
            )+

            if let Some(token) = tokenizer.next() { panic!("expected end of tokenizer, found: {:?}", token)}
        }};
    }

    #[test]
    fn test_simple_string() {
        expect_tokens! {
            r#" "test foobar" "test \" \\\n \u263A" aaaa   "#

            TokenContent::StringValue(Cow::Borrowed("test foobar")),
            TokenContent::StringValue(Cow::Borrowed("test \" \\\n ☺")),
            TokenContent::Name("aaaa")
        }
    }

    #[test]
    fn test_block_string() {
        expect_tokens! {
            r#" """hello""" """
             block
            string
            """ 

            """
            ""this works!""\n\n
            """
            
            """
            block string
            with
            escaped \""" quote
            \"""""""#

            TokenContent::StringValue(Cow::Borrowed("hello")),
            TokenContent::StringValue(Cow::Borrowed(" block\nstring")),
            TokenContent::StringValue(Cow::Borrowed("\"\"this works!\"\"\\n\\n")),
            @[9:13] TokenContent::StringValue(Cow::Borrowed("block string\nwith\nescaped \"\"\" quote\n\"\"\""))
        }
    }

    #[test]
    fn test_block_string_rn() {
        expect_tokens! {
            " \"\"\"hello\r\n world\"\"\" "

            TokenContent::StringValue(Cow::Borrowed("hello\nworld"))
        }
    }

    #[test]
    fn test_assortment() {
        expect_tokens! {
            " ! $ ( ) ... : = \r @, [ ] { } | _abc 12345 -17.0e3 \"hello\" \"hello\\n\" \n # comment \r\n $"

            TokenContent::Exclamation,
            TokenContent::DollarSign,
            TokenContent::LeftParen,
            TokenContent::RightParen,
            TokenContent::Ellipses,
            TokenContent::Colon,
            TokenContent::Equals,
            @[2:2] TokenContent::At,
            TokenContent::LeftBracket,
            TokenContent::RightBracket,
            TokenContent::LeftCurlyBracket,
            TokenContent::RightCurlyBracket,
            TokenContent::Pipe,
            TokenContent::Name("_abc"),
            TokenContent::IntValue(12345),
            TokenContent::FloatValue(-17.0e3),
            TokenContent::StringValue(Cow::Borrowed("hello")),
            TokenContent::StringValue(Cow::Borrowed("hello\n")),
            @[4:2] TokenContent::DollarSign
        }
    }
}
