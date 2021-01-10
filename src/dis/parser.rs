use std::fmt;

use crate::utils;
use crate::utils::Buf;

/// Parser state for parsing compiled HACK programs.
///
/// # impl `From<Buf>`
///
/// A parser object can be created using [Parser::from].
///
/// # impl `Iterator`
///
/// The parse tree of HACK programs is a flat list. A text parser
/// object returns [tokens](Token) when iterated over. Perhaps at a
/// later point a conversion to an abstract syntax tree could reflect
/// the structure of labels and jumps in the program.
///
/// ## Examples
///
/// ```
/// use has::dis::parser::Parser;
/// use has::dis::parser::Token;
///
/// // "(FOO)\n@FOO\nD=D+1;JEQ"
/// let prog = &[0, 0, 0b11100111, 0b11010010][..];
/// let mut parser = Parser::from(prog);
///
/// assert_eq!(parser.next(), Some(Ok(Token::new(0, 0))));
/// assert_eq!(parser.next(), Some(Ok(Token::new(2, 59346))));
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parser<'b> {
  buf: Buf<'b>,
  orig: Buf<'b>,
  index: usize,
}

impl<'b> From<Buf<'b>> for Parser<'b> {
  fn from(buf: Buf<'b>) -> Self {
    Self { buf, orig: buf, index: 0 }
  }
}

impl Parser<'_> {
  /// Calculate the line and column of a [Token].
  ///
  /// Returns a tuple `(line, column)` corresponding to the location
  /// of a [Token] in the original input buffer.
  pub fn loc(&self, tok: &Token) -> (usize, usize) {
    utils::loc(self.orig, tok.index())
  }
}

/// Units returned by iterator over a [Parser] or [TextParser].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token {
  index: usize,
  value: u16,
}

impl Token {
  /// Create a new token.
  ///
  /// # Arguments
  ///
  /// * `index` - The token's index.
  ///
  /// * `value` - The instruction.
  pub fn new(index: usize, value: u16) -> Self {
    Self { index, value }
  }

  /// Returns the index in the buffer the token was created from.
  pub fn index(&self) -> usize {
    self.index
  }

  /// Returns the instruction.
  pub fn value(&self) -> u16 {
    self.value
  }
}

/// Kind of parsing error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrKind {
  /// Expected a bit value to form an instruction.
  ExpectedByte,
}

impl fmt::Display for ErrKind {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      ErrKind::ExpectedByte => write!(f, "expected byte"),
    }
  }
}

/// Error during parsing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Err {
  index: usize,
  kind: ErrKind,
}

impl fmt::Display for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "index {}: {}", self.index, self.kind)
  }
}

impl Err {
  /// Create a new parsing error.
  ///
  /// # Arguments
  ///
  /// * `index` - The index in the buffer at which the error occurred.
  ///
  /// * `kind` - The kind if parsing error.
  fn new(index: usize, kind: ErrKind) -> Self {
    Self { index, kind }
  }

  /// Returns the index in the input buffer at which the error
  /// occurred.
  pub fn index(&self) -> usize {
    self.index
  }

  /// Returns the kind of parsing error.
  pub fn kind(&self) -> ErrKind {
    self.kind
  }
}

impl<'b> Iterator for Parser<'b> {
  type Item = Result<Token, Err>;

  fn next(&mut self) -> Option<Self::Item> {
    let &msb = self.buf.get(0)?;
    let &lsb = if let Some(lsb) = self.buf.get(1) {
      lsb
    } else {
      return Some(Err(Err::new(self.index + 1, ErrKind::ExpectedByte)));
    };

    let token = Token::new(self.index, (u16::from(msb) << 8) | u16::from(lsb));

    self.buf = &self.buf[2..];
    self.index += 2;

    Some(Ok(token))
  }
}
