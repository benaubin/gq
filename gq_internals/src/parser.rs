mod tokenizer;
mod const_val;

use thiserror::Error;

#[derive(Debug, PartialEq, Clone)]
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


impl std::fmt::Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line(), self.column())
    }
}

impl std::fmt::Debug for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line(), self.column())
    }
}

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum ParserErrorKind {
    #[error("Variable in const input")]
    VariableInConstInput,
    #[error("Invalid {0}")]
    Invalid(&'static str),
    #[error("Unexpected {0}")]
    Unexpected(&'static str),
    #[error("Expected {0}")]
    Expected(&'static str),
    #[error("{0}")]
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
    #[inline]
    fn unknown_location(self) -> ParserError {
        ParserError {
            kind: self,
            locations: vec![]
        }
    }
}
#[derive(Debug, Clone)]
pub struct ParserError {
    kind: ParserErrorKind,
    locations: Vec<Position>
}

impl std::fmt::Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("ParserError at [")?;
        for loc in self.locations.iter() {
            loc.fmt(f)?;
            f.write_str("; ")?;
        }
        f.write_str("]: ")?;
        self.kind.fmt(f)
    }
}

impl std::error::Error for ParserError {}

impl serde::de::Error for ParserError {
    fn custom<T>(msg: T) -> Self where T: std::fmt::Display {
        ParserError { kind: ParserErrorKind::Serde( msg.to_string() ), locations: vec![] }
    }
}
