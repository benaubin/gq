mod tokenizer;

pub struct Token<'src> {
    content: tokenizer::TokenContent<'src>,
    pos: Position,
}

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct Position {
    /// The index of the next character
    idx: usize,
    /// The current line (new line characters are considered part of the prior line)
    line: usize,
    /// The byte position after the last encountered new line character (may be past the end of the source)
    line_start_idx: usize,
}

pub enum ParserErrorKind {
    VariableInConstInput,
    UndefinedVariable,
    VariableOutsideOperation,
    Invalid(&'static str),
    Unexpected(&'static str),
    Expected(&'static str),
    Other(&'static str),
    Serde(String)
}

impl ParserErrorKind {
    #[inline]
    fn at(self, pos: Position) -> ParserError {
        ParserError {
            kind: self,
            locations: vec![pos]
        }
    }
}

pub struct ParserError {
    kind: ParserErrorKind,
    locations: Vec<Position>
}