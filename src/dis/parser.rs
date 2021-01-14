use std::fmt;
use std::marker::PhantomData;

use crate::utils;
use crate::utils::Buf;

pub trait Impl {
  type Item;

  fn next<T: Impl>(parser: &mut Parser<T>) -> Option<Self::Item>;
}

pub struct Binary;

impl Impl for Binary {
  type Item = Result<Token, Err>;

  fn next<T: Impl>(parser: &mut Parser<T>) -> Option<Self::Item> {
    let &msb = parser.buf.get(0)?;
    let &lsb = if let Some(lsb) = parser.buf.get(1) {
      lsb
    } else {
      return Some(Err(Err::new(parser.index + 1, ErrKind::Expected)));
    };

    let token = Token::new(parser.index, (u16::from(msb) << 8) | u16::from(lsb));

    parser.buf = &parser.buf[2..];
    parser.index += 2;

    Some(Ok(token))
  }
}

pub struct Text;

impl Impl for Text {
  type Item = Result<Token, Err>;

  fn next<T: Impl>(parser: &mut Parser<T>) -> Option<Self::Item> {
    'MAIN: loop {
      let &b = parser.buf.get(0)?;

      if b.is_ascii_whitespace() {
        let (len, rem) = utils::read_ws(parser.buf);
        parser.index += len;
        parser.buf = rem;
        continue 'MAIN;
      } else {
        let mut inst = 0;

        macro_rules! consume_bit {
          ($index:expr, $on_error:block) => {
            parser.buf = if let Some((b, rem)) =
              utils::read_one(parser.buf, |b| b == b'0' || b == b'1')
            {
              let b = if b == b'0' { 0 } else { 1 };
              inst |= b << $index;
              rem
            } else $on_error;
          };
          ($index:expr) => {
            consume_bit!($index, {
              return Some(Err(Err::new(parser.index + (15 - $index), ErrKind::Expected)))
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

        let token = Token::new(parser.index, inst);
        parser.index += 16;
        return Some(Ok(token));
      }
    }
  }
}

/// Parser state for parsing compiled HACK programs.
///
/// # impl `From<Buf>`
///
/// A parser object can be created using [Parser::from].
///
/// # impl `Iterator`
///
/// The parse tree of HACK programs is a flat list. A parser returns
/// [tokens](Token) when iterated over. Perhaps at a later point a
/// conversion to an abstract syntax tree could reflect the structure
/// of labels and jumps in the program.
///
/// There are two ways to parse HACK programs: from binary files and
/// from the textual representation of such binary files. Use
/// [Parser<BinaryImpl>] to create a parser for binary HACK files and
/// [Parser<TextImpl>] to create a parser for text HACK files.
///
/// ## Examples
///
/// ```
/// use has::dis::parser::Parser;
/// use has::dis::parser::Binary;
/// use has::dis::parser::Text;
/// use has::dis::parser::Token;
///
/// // Parse the binary representation of "(FOO)\n@FOO\nD=D+1;JEQ"
/// let prog = &[0, 0, 0b11100111, 0b11010010][..];
/// let mut parser: Parser<Binary> = Parser::from(prog);
///
/// assert_eq!(parser.next(), Some(Ok(Token::new(0, 0))));
/// assert_eq!(parser.next(), Some(Ok(Token::new(2, 59346))));
///
/// // Parse the textual representation of "(FOO)\n@FOO\nD=D+1;JEQ"
/// let prog = "0000000000000000\n1110011111010010".as_bytes();
/// let mut parser: Parser<Text> = Parser::from(prog);
///
/// assert_eq!(parser.next(), Some(Ok(Token::new(0, 0))));
/// assert_eq!(parser.next(), Some(Ok(Token::new(17, 59346))));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Parser<'b, T: Impl> {
  buf: Buf<'b>,
  orig: Buf<'b>,
  index: usize,
  phantom: PhantomData<T>,
}

impl<'b, T: Impl> From<Buf<'b>> for Parser<'b, T> {
  fn from(buf: Buf<'b>) -> Self {
    Self { buf, orig: buf, index: 0, phantom: PhantomData }
  }
}

impl<T: Impl> Parser<'_, T> {
  /// Calculate the line and column of a [Token].
  ///
  /// Returns a tuple `(line, column)` corresponding to the location
  /// of a [Token] in the original input buffer.
  pub fn loc(&self, tok: &Token) -> (usize, usize) {
    utils::loc(self.orig, tok.index())
  }
}

/// Units returned by iterator over a [Parser].
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
  /// Expected another byte to form an instruction.
  Expected,
}

impl fmt::Display for ErrKind {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      ErrKind::Expected => write!(f, "expected a byte"),
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

impl<'b, T: Impl<Item = Result<Token, Err>>> Iterator for Parser<'b, T> {
  type Item = Result<Token, Err>;

  fn next(&mut self) -> Option<Self::Item> {
    T::next(self)
  }
}
