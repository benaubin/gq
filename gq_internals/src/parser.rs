mod tokenizer;

#[derive(Debug, PartialEq)]
pub struct Token<'src> {
    content: tokenizer::TokenContent<'src>,
    pos: Position,
}

#[derive(PartialEq, Eq, Copy, Clone)]
pub struct Position {
    /// The index of the next character
    idx: usize,
    /// The current line (new line characters are considered part of the prior line)
    line: usize,
    /// The byte position after the last encountered new line character (may be past the end of the source)
    line_start_idx: usize,
}
impl Position {
    fn line(&self) -> usize {
        self.line
    }
    fn column(&self) -> usize {
        self.idx.saturating_sub(self.line_start_idx) + 1
    }
}


impl std::fmt::Debug for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line(), self.column())
    }
}

#[derive(Debug)]
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

#[derive(Debug)]
pub struct ParserError {
    kind: ParserErrorKind,
    locations: Vec<Position>
}