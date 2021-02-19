//! Parser for disassembling HACK programs from binary and bintext
//! files.

use crate::parser;
use crate::Buf;
use crate::Index;
use crate::Loc;
use derive_more::Display;
use std::marker::PhantomData;

/// Shorthand for items returned by the (parser)(Parser)
/// (iterator)[Iterator].
pub type Res = Result<Token, Err>;

/// A trait to represent different types of decoders that can be used
/// by the disassembler.
pub trait Impl {
  /// The type of elements returned by the decoder (e.g. Tokens).
  type Item;

  /// Corresponds to the `next` implementation in the (parser)[Parser]
  /// (iterator)[Iterator].
  fn next<T: Impl>(parser: &mut Parser<T>) -> Option<Self::Item>;
}

/// A parser helper for binary HACK programs.
pub struct BinParser;

impl Impl for BinParser {
  type Item = Res;

  fn next<T: Impl>(parser: &mut Parser<T>) -> Option<Self::Item> {
    let &msb = parser.buf.get(0)?;
    let &lsb = if let Some(lsb) = parser.buf.get(1) {
      lsb
    } else {
      return Some(Err(Err::expected(parser.buf, parser.index + 1)));
    };

    let token = Token::new(parser.index, (u16::from(msb) << 8) | u16::from(lsb));

    parser.buf = &parser.buf[2..];
    parser.index += 2;

    Some(Ok(token))
  }
}

/// A parser helper for bintext HACK programs.
pub struct BinTextParser;

impl Impl for BinTextParser {
  type Item = Res;

  fn next<T: Impl>(parser: &mut Parser<T>) -> Option<Self::Item> {
    'MAIN: loop {
      let &b = parser.buf.get(0)?;

      if b.is_ascii_whitespace() {
        let (len, rem) = parser::read_ws(parser.buf);
        parser.index += len;
        parser.buf = rem;
        continue 'MAIN;
      } else {
        let mut inst = 0;

        macro_rules! consume_bit {
          ($index:expr, $on_error:block) => {
            parser.buf = if let Some((b, rem)) =
              parser::read_one(parser.buf, |b| b == b'0' || b == b'1')
            {
              let b = if b == b'0' { 0 } else { 1 };
              inst |= b << $index;
              rem
            } else $on_error;
          };
          ($index:expr) => {
            consume_bit!($index, {
              return Some(Err(Err::expected(parser.buf, parser.index + (15 - $index))))
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
/// use has::hack::dec;
/// use has::hack::dec::Parser;
/// use has::hack::dec::Token;
///
/// // Parse the binary representation of "(FOO)\n@FOO\nD=D+1;JEQ"
/// let prog = &[0, 0, 0b11100111, 0b11010010][..];
/// let mut parser: Parser<dec::BinParser> = Parser::from(prog);
///
/// assert_eq!(parser.next(), Some(Ok(Token::new(0, 0))));
/// assert_eq!(parser.next(), Some(Ok(Token::new(2, 59346))));
///
/// // Parse the textual representation of "(FOO)\n@FOO\nD=D+1;JEQ"
/// let prog = "0000000000000000\n1110011111010010".as_bytes();
/// let mut parser: Parser<dec::BinTextParser> = Parser::from(prog);
///
/// assert_eq!(parser.next(), Some(Ok(Token::new(0, 0))));
/// assert_eq!(parser.next(), Some(Ok(Token::new(17, 59346))));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Parser<'b, T: Impl> {
  /// The current point in the input buffer.
  buf: Buf<'b>,

  /// The original input buffer.
  orig: Buf<'b>,

  /// The current byte into the input buffer.
  index: usize,

  /// Phantom for keeping `Parser` generic over different decoder
  /// implementations.
  phantom: PhantomData<T>,
}

impl<'b, T: Impl> Parser<'b, T> {
  /// The original input buffer attached to this parser.
  pub fn orig(&self) -> Buf<'b> {
    self.orig
  }
}

impl<'b, T: Impl> From<Buf<'b>> for Parser<'b, T> {
  fn from(buf: Buf<'b>) -> Self {
    Self { buf, orig: buf, index: 0, phantom: PhantomData }
  }
}

/// Units returned by iterator over a [Parser].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token {
  /// Index of the token in the original input buffer.
  index: usize,

  /// The encoded bit sequence representing an instruction.
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
#[derive(Display, Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrKind {
  /// Expected another byte to form an instruction.
  #[display(fmt = "Expected another byte")]
  Expected,
}

/// Error during parsing.
#[derive(Display, Debug, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "Disassembly parsing error at {}: {}", loc, kind)]
pub struct Err {
  /// [Location](Loc) of the err in the original input buffer.
  loc: Loc,

  /// The type of error.
  kind: ErrKind,
}

impl Err {
  /// Create a new parsing error.
  ///
  /// # Arguments
  ///
  /// * `buf` - The original input buffer.
  ///
  /// * `index` - The index in the buffer at which the error occurred.
  ///
  /// * `kind` - The kind if parsing error.
  fn new(buf: Buf, index: Index, kind: ErrKind) -> Self {
    Self { loc: Loc::from_index(buf, index), kind }
  }

  /// Returns the [location](Loc) in the input buffer at which the
  /// error occurred.
  pub fn loc(&self) -> Loc {
    self.loc
  }

  /// Returns the kind of parsing error.
  pub fn kind(&self) -> ErrKind {
    self.kind
  }

  /// Creates an error with an `ErrKind::Expected` variant.
  pub fn expected(buf: Buf, index: Index) -> Self {
    Err::new(buf, index, ErrKind::Expected)
  }
}

impl<'b, T: Impl<Item = Result<Token, Err>>> Iterator for Parser<'b, T> {
  type Item = Result<Token, Err>;

  fn next(&mut self) -> Option<Self::Item> {
    T::next(self)
  }
}

#[cfg(test)]
mod tests_bintext {
  use super::Parser;
  use crate::hack::Addr;
  use crate::hack::Comp;
  use crate::hack::Dest;
  use crate::hack::Inst;
  use crate::hack::Jump;
  use crate::hack::Sym;
  use crate::Loc;
  use std::convert::TryFrom;

  macro_rules! parser_text {
    ($f:expr) => {{
      let bytes = include_bytes!(concat!("../../tests/snippets/", $f, ".hack"));
      Parser::from(&bytes[..])
    }};
  }

  macro_rules! next {
    ($parser:expr, $line:expr, $col:expr, $kind:ident, $inst:expr) => {{
      let tok = $parser.next().unwrap().unwrap();
      assert_eq!(Loc::new($line, $col), Loc::from_index($parser.orig(), tok.index()));
      assert_eq!($kind::try_from(tok.value()).unwrap(), $inst);
    }};
  }

  #[test]
  fn empty() {
    let mut p: Parser<super::BinTextParser> = parser_text!("empty");
    assert_eq!(p.next(), None);
  }

  #[test]
  fn spaces() {
    let mut p: Parser<super::BinTextParser> = parser_text!("spaces");
    assert_eq!(p.next(), None);
  }

  #[test]
  fn comments() {
    let mut p: Parser<super::BinTextParser> = parser_text!("comments");
    assert_eq!(p.next(), None);
  }

  #[test]
  fn addr_nums() {
    let mut p: Parser<super::BinTextParser> = parser_text!("addr_nums");
    next!(p, 1, 1, Addr, Addr::Num(8192));
    next!(p, 2, 1, Addr, Addr::Num(123));
    next!(p, 3, 1, Addr, Addr::Num(556));
    assert_eq!(p.next(), None);
  }

  #[test]
  fn address_labels() {
    let mut p: Parser<super::BinTextParser> = parser_text!("addr_labels");
    next!(p, 1, 1, Addr, Addr::Num(16));
    next!(p, 2, 1, Addr, Addr::Num(17));
    next!(p, 3, 1, Addr, Addr::Num(Sym::KBD.into()));
    next!(p, 4, 1, Addr, Addr::Num(18));
    next!(p, 5, 1, Addr, Addr::Num(Sym::LCL.into()));
    next!(p, 6, 1, Addr, Addr::Num(19));
    next!(p, 7, 1, Addr, Addr::Num(Sym::SCREEN.into()));
    next!(p, 8, 1, Addr, Addr::Num(Sym::SP.into()));
    next!(p, 9, 1, Addr, Addr::Num(20));
    next!(p, 10, 1, Addr, Addr::Num(Sym::ARG.into()));
    next!(p, 11, 1, Addr, Addr::Num(21));
    next!(p, 12, 1, Addr, Addr::Num(Sym::THIS.into()));
    next!(p, 13, 1, Addr, Addr::Num(Sym::THAT.into()));
    next!(p, 14, 1, Addr, Addr::Num(22));
    next!(p, 15, 1, Addr, Addr::Num(Sym::R0.into()));
    next!(p, 16, 1, Addr, Addr::Num(Sym::R1.into()));
    next!(p, 17, 1, Addr, Addr::Num(Sym::R11.into()));
    next!(p, 18, 1, Addr, Addr::Num(23));
    next!(p, 19, 1, Addr, Addr::Num(24));
    assert_eq!(p.next(), None);
  }

  #[test]
  fn label() {
    let mut p: Parser<super::BinTextParser> = parser_text!("label");
    next!(p, 1, 1, Addr, Addr::Num(16));
    next!(p, 2, 1, Addr, Addr::Num(1));
    next!(p, 3, 1, Addr, Addr::Num(3));
    next!(p, 4, 1, Addr, Addr::Num(4));
    assert_eq!(p.next(), None);
  }

  macro_rules! inst {
    ($dest:expr, $comp:expr, $jump:expr) => {
      Inst::new($dest, $comp, $jump).unwrap()
    };
  }

  #[test]
  fn instructions() {
    let mut p: Parser<super::BinTextParser> = parser_text!("instructions");

    next!(p, 1, 1, Inst, inst!(Dest::A, Comp::MMinus1, Jump::Null));
    next!(p, 2, 1, Inst, inst!(Dest::AM, Comp::DOrA, Jump::Null));
    next!(p, 3, 1, Inst, inst!(Dest::AMD, Comp::APlus1, Jump::Null));

    next!(p, 4, 1, Inst, inst!(Dest::Null, Comp::MMinus1, Jump::JEQ));
    next!(p, 5, 1, Inst, inst!(Dest::Null, Comp::DOrA, Jump::JNE));
    next!(p, 6, 1, Inst, inst!(Dest::Null, Comp::APlus1, Jump::JMP));

    next!(p, 7, 1, Inst, inst!(Dest::A, Comp::MMinus1, Jump::JEQ));
    next!(p, 8, 1, Inst, inst!(Dest::AM, Comp::DOrA, Jump::JNE));
    next!(p, 9, 1, Inst, inst!(Dest::AMD, Comp::APlus1, Jump::JMP));

    assert_eq!(p.next(), None);
  }
}

#[cfg(test)]
mod tests_bin {
  use super::Parser;
  use crate::hack::Addr;
  use crate::hack::Comp;
  use crate::hack::Dest;
  use crate::hack::Inst;
  use crate::hack::Jump;
  use crate::hack::Sym;
  use crate::Loc;
  use std::convert::TryFrom;

  macro_rules! parser_text {
    ($f:expr) => {{
      let bytes = include_bytes!(concat!("../../tests/snippets/", $f, ".hack_bin"));
      Parser::from(&bytes[..])
    }};
  }

  macro_rules! next {
    ($parser:expr, $line:expr, $col:expr, $kind:ident, $inst:expr) => {{
      let tok = $parser.next().unwrap().unwrap();
      assert_eq!(Loc::new($line, $col), Loc::from_index($parser.orig(), tok.index()));
      assert_eq!($kind::try_from(tok.value()).unwrap(), $inst);
    }};
  }

  #[test]
  fn empty() {
    let mut p: Parser<super::BinParser> = parser_text!("empty");
    assert_eq!(p.next(), None);
  }

  #[test]
  fn spaces() {
    let mut p: Parser<super::BinParser> = parser_text!("spaces");
    assert_eq!(p.next(), None);
  }

  #[test]
  fn comments() {
    let mut p: Parser<super::BinParser> = parser_text!("comments");
    assert_eq!(p.next(), None);
  }

  #[test]
  fn addr_nums() {
    let mut p: Parser<super::BinParser> = parser_text!("addr_nums");
    next!(p, 1, 1, Addr, Addr::Num(8192));
    next!(p, 1, 3, Addr, Addr::Num(123));
    next!(p, 1, 5, Addr, Addr::Num(556));
    assert_eq!(p.next(), None);
  }

  #[test]
  fn address_labels() {
    let mut p: Parser<super::BinParser> = parser_text!("addr_labels");
    next!(p, 1, 1, Addr, Addr::Num(16));
    next!(p, 1, 3, Addr, Addr::Num(17));
    next!(p, 1, 5, Addr, Addr::Num(Sym::KBD.into()));
    next!(p, 1, 7, Addr, Addr::Num(18));
    next!(p, 1, 9, Addr, Addr::Num(Sym::LCL.into()));
    next!(p, 1, 11, Addr, Addr::Num(19));
    next!(p, 1, 13, Addr, Addr::Num(Sym::SCREEN.into()));
    next!(p, 1, 15, Addr, Addr::Num(Sym::SP.into()));
    next!(p, 1, 17, Addr, Addr::Num(20));
    next!(p, 1, 19, Addr, Addr::Num(Sym::ARG.into()));
    next!(p, 1, 21, Addr, Addr::Num(21));
    next!(p, 1, 23, Addr, Addr::Num(Sym::THIS.into()));
    next!(p, 1, 25, Addr, Addr::Num(Sym::THAT.into()));
    next!(p, 1, 27, Addr, Addr::Num(22));
    next!(p, 1, 29, Addr, Addr::Num(Sym::R0.into()));
    next!(p, 1, 31, Addr, Addr::Num(Sym::R1.into()));
    next!(p, 1, 33, Addr, Addr::Num(Sym::R11.into()));
    next!(p, 1, 35, Addr, Addr::Num(23));
    next!(p, 1, 37, Addr, Addr::Num(24));
    assert_eq!(p.next(), None);
  }

  #[test]
  fn label() {
    let mut p: Parser<super::BinParser> = parser_text!("label");
    next!(p, 1, 1, Addr, Addr::Num(16));
    next!(p, 1, 3, Addr, Addr::Num(1));
    next!(p, 1, 5, Addr, Addr::Num(3));
    next!(p, 1, 7, Addr, Addr::Num(4));
    assert_eq!(p.next(), None);
  }

  macro_rules! inst {
    ($dest:expr, $comp:expr, $jump:expr) => {
      Inst::new($dest, $comp, $jump).unwrap()
    };
  }

  #[test]
  fn instructions() {
    let mut p: Parser<super::BinParser> = parser_text!("instructions");

    next!(p, 1, 1, Inst, inst!(Dest::A, Comp::MMinus1, Jump::Null));
    next!(p, 1, 3, Inst, inst!(Dest::AM, Comp::DOrA, Jump::Null));
    next!(p, 1, 5, Inst, inst!(Dest::AMD, Comp::APlus1, Jump::Null));

    next!(p, 1, 7, Inst, inst!(Dest::Null, Comp::MMinus1, Jump::JEQ));
    next!(p, 1, 9, Inst, inst!(Dest::Null, Comp::DOrA, Jump::JNE));
    next!(p, 1, 11, Inst, inst!(Dest::Null, Comp::APlus1, Jump::JMP));

    next!(p, 1, 13, Inst, inst!(Dest::A, Comp::MMinus1, Jump::JEQ));
    next!(p, 1, 15, Inst, inst!(Dest::AM, Comp::DOrA, Jump::JNE));
    next!(p, 1, 17, Inst, inst!(Dest::AMD, Comp::APlus1, Jump::JMP));

    assert_eq!(p.next(), None);
  }
}
