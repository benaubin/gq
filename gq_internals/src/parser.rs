mod tokenizer;
mod const_val;

use thiserror::Error;

#[derive(Debug, PartialEq, Clone)]
pub struct Token<'src> {
    content: tokenizer::TokenContent<'src>,
    location: Location,
}

#[derive(Copy, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Location {
    /// The current line (new line characters are considered part of the prior line)
    pub line: usize,
    /// Column
    pub column: usize
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

impl std::fmt::Debug for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
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
    fn at(self, location: Location) -> ParserError {
        ParserError {
            kind: self,
            locations: vec![location]
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
    locations: Vec<Location>
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
