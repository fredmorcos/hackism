use std::fmt;

use crate::utils;
use crate::utils::Buf;

/// Parser state for parsing compiled text HACK programs.
///
/// # impl `From<Buf>`
///
/// A parser object can be created using [TextParser::from].
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
/// use has::dis::text_parser::TextParser;
/// use has::dis::text_parser::Token;
///
/// // "(FOO)\n@FOO\nD=D+1;JEQ"
/// let prog = "0000000000000000\n1110011111010010".as_bytes();
/// let mut parser = TextParser::from(prog);
///
/// assert_eq!(parser.next(), Some(Ok(Token::new(0, 0))));
/// assert_eq!(parser.next(), Some(Ok(Token::new(17, 59346))));
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextParser<'b> {
  buf: Buf<'b>,
  orig: Buf<'b>,
  index: usize,
}

impl<'b> From<Buf<'b>> for TextParser<'b> {
  fn from(buf: Buf<'b>) -> Self {
    Self { buf, orig: buf, index: 0 }
  }
}

impl TextParser<'_> {
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
  ExpectedBit,
}

impl fmt::Display for ErrKind {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      ErrKind::ExpectedBit => write!(f, "expected bit value"),
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

impl<'b> Iterator for TextParser<'b> {
  type Item = Result<Token, Err>;

  fn next(&mut self) -> Option<Self::Item> {
    'MAIN: loop {
      let &b = self.buf.get(0)?;

      if b.is_ascii_whitespace() {
        let (len, rem) = utils::read_ws(self.buf);
        self.index += len;
        self.buf = rem;
        continue 'MAIN;
      } else {
        let mut inst = 0;

        macro_rules! consume_bit {
          ($index:expr, $on_error:block) => {
            self.buf = if let Some((b, rem)) =
              utils::read_one(self.buf, |b| b == b'0' || b == b'1')
            {
              let b = if b == b'0' { 0 } else { 1 };
              inst |= b << $index;
              rem
            } else $on_error;
          };
          ($index:expr) => {
            consume_bit!($index, {
              return Some(Err(Err::new(self.index + (15 - $index), ErrKind::ExpectedBit)))
            });
          }
        }

        consume_bit!(15, { return None });
        consume_bit!(14);
        consume_bit!(13);
        consume_bit!(12);
        consume_bit!(11);
        consume_bit!(10);
        consume_bit!(9);
        consume_bit!(8);
        consume_bit!(7);
        consume_bit!(6);
        consume_bit!(5);
        consume_bit!(4);
        consume_bit!(3);
        consume_bit!(2);
        consume_bit!(1);
        consume_bit!(0);

        let token = Token::new(self.index, inst);
        self.index += 16;
        return Some(Ok(token));
      }
    }
  }
}
