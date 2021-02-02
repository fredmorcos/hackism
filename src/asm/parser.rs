//! Structures to be used for parsing HACK programs.
//!
//! [Parser] is the primary structure in this module that should be
//! used to parse HACK programs.

use crate::com::addr;
use crate::com::addr::Addr;
use crate::com::inst;
use crate::com::inst::Inst;
use crate::com::label;
use crate::com::label::Label;
use crate::utils::buf::Buf;
use crate::utils::loc::Index;
use crate::utils::loc::Loc;
use crate::utils::parser;

use std::convert::TryFrom;

use derive_more::Display;

/// Parser state for parsing HACK programs.
///
/// # impl `From<Buf>`
///
/// A parser object can be created using [Parser::from].
///
/// # impl `Iterator`
///
/// The parse tree of HACK programs is a flat list. A parser object
/// returns [tokens](Token) when iterated over. Perhaps at a later
/// point a conversion to an abstract syntax tree could reflect the
/// structure of labels and jumps in the program.
///
/// ## Examples
///
/// ```
/// use has::asm::parser::Parser;
/// use has::asm::parser::Token;
/// use has::asm::parser::TokenKind;
/// use has::com::inst;
/// use has::com::inst::Inst;
/// use has::com::addr::Addr;
/// use has::com::label::Label;
///
/// use std::convert::TryFrom;
///
/// let prog = "(FOO)\n@FOO\nD=D+A;JMP".as_bytes();
/// let mut parser = Parser::from(prog);
///
/// let buf = "FOO".as_bytes();
/// let label = Label::try_from(buf).unwrap();
/// let label = Token::new(0, TokenKind::Label(label));
/// assert_eq!(parser.next(), Some(Ok(label)));
///
/// let buf = "FOO".as_bytes();
/// let addr = Addr::read_from(buf).unwrap().0;
/// let addr = Token::new(6, TokenKind::Addr(addr));
/// assert_eq!(parser.next(), Some(Ok(addr)));
///
/// let buf = "D=D+A;JMP".as_bytes();
/// let inst = Inst::read_from(buf).unwrap().0;
/// let inst = Token::new(11, TokenKind::Inst(inst));
/// assert_eq!(parser.next(), Some(Ok(inst)));
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parser<'b> {
  /// The current point in the input buffer.
  buf: Buf<'b>,

  /// The original input buffer.
  orig: Buf<'b>,

  /// The current byte index into the input buffer.
  index: usize,
}

impl<'b> Parser<'b> {
  /// The original input buffer attached to this parser.
  pub fn orig(&self) -> Buf<'b> {
    self.orig
  }
}

impl<'b> From<Buf<'b>> for Parser<'b> {
  fn from(buf: Buf<'b>) -> Self {
    Self { buf, orig: buf, index: 0 }
  }
}

/// The kind of a [Token].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind<'b> {
  /// A label as defined by the HACK assembly reference
  /// (e.g. `(FOO)`).
  Label(Label<'b>),
  /// An address as defined by the HACK assembly reference
  /// (e.g. `@FOO`).
  Addr(Addr<'b>),
  /// An instruction as defined by the HACK assembly reference
  /// (e.g. `D=A+1;JMP`).
  Inst(Inst),
}

/// Units returned by iterating over a [Parser].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'b> {
  /// Index of the token in the original input buffer.
  index: Index,

  /// The type of token.
  kind: TokenKind<'b>,
}

impl<'b> Token<'b> {
  /// Create a new token.
  ///
  /// # Arguments
  ///
  /// * `index` - The token's index.
  ///
  /// * `kind` - The token's kind.
  pub fn new(index: Index, kind: TokenKind<'b>) -> Self {
    Self { index, kind }
  }

  /// Returns the token's index in the input buffer.
  pub fn index(&self) -> Index {
    self.index
  }

  /// Returns the kind of token.
  pub fn kind(self) -> TokenKind<'b> {
    self.kind
  }

  /// Create a token with the `TokenKind::Label` variant.
  pub fn label(index: Index, label: Label<'b>) -> Self {
    Token::new(index, TokenKind::Label(label))
  }

  /// Create a token with the `TokenKind::Addr` variant.
  pub fn addr(index: Index, addr: Addr<'b>) -> Self {
    Token::new(index, TokenKind::Addr(addr))
  }

  /// Create a token with the `TokenKind::Inst` variant.
  pub fn inst(index: Index, inst: Inst) -> Self {
    Token::new(index, TokenKind::Inst(inst))
  }
}

/// Kind of parsing error.
#[derive(Display, Debug, Clone, PartialEq, Eq)]
pub enum ErrKind {
  /// Expected a second `/` to form a comment.
  #[display(fmt = "expected a second '/' to form a comment")]
  ExpectedComment,

  /// Invalid label.
  #[display(fmt = "invalid label: {}", _0)]
  InvalidLabel(label::Err),

  /// Missing the closing ')' for a label.
  #[display(fmt = "expected a closing parenthesis ')' for label")]
  MissingLParen,

  /// Invalid address.
  #[display(fmt = "invalid address: {}", _0)]
  InvalidAddr(addr::Err),

  /// Invalid instruction.
  #[display(fmt = "invalid instruction: {}", _0)]
  InvalidInst(inst::Err),
}

/// Error during parsing.
#[derive(Display, Debug, Clone, PartialEq, Eq)]
#[display(fmt = "Parsing error at {}: {}", loc, kind)]
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
  pub fn kind(&self) -> &ErrKind {
    &self.kind
  }

  /// Create an error with the `ErrKind::ExpectedComment` variant.
  pub fn expected_comment(parser: &Parser) -> Self {
    Err::new(parser.orig, parser.index + 1, ErrKind::ExpectedComment)
  }

  /// Create an error with the `ErrKind::InvalidLabel` variant.
  pub fn invalid_label(parser: &Parser, error: label::Err) -> Self {
    Err::new(parser.orig, parser.index, ErrKind::InvalidLabel(error))
  }

  /// Create an error with the `ErrKind::MissingLParen` variant.
  pub fn missing_lparen(parser: &Parser, offset: usize) -> Self {
    Err::new(parser.orig, parser.index + offset, ErrKind::MissingLParen)
  }

  /// Create an error with the `ErrKind::InvalidAddr` variant.
  pub fn invalid_addr(parser: &Parser, error: addr::Err) -> Self {
    Err::new(parser.orig, parser.index, ErrKind::InvalidAddr(error))
  }

  /// Create an error with the `ErrKind::InvalidInst` variant.
  pub fn invalid_inst(parser: &Parser, error: inst::Err) -> Self {
    Err::new(parser.orig, parser.index, ErrKind::InvalidInst(error))
  }
}

impl<'b> Iterator for Parser<'b> {
  type Item = Result<Token<'b>, Err>;

  fn next(&mut self) -> Option<Self::Item> {
    'MAIN: loop {
      let &b = self.buf.get(0)?;

      if b.is_ascii_whitespace() {
        let (len, rem) = parser::read_ws(self.buf);
        self.index += len;
        self.buf = rem;
        continue 'MAIN;
      } else if b == b'/' {
        match self.buf.get(0) {
          Some(b'/') => {}
          Some(_) => return Some(Err(Err::expected_comment(self))),
          None => return Some(Err(Err::expected_comment(self))),
        }

        let (com, rem) = parser::read_until_nl(self.buf);
        self.index += com.len();
        self.buf = rem;
        continue 'MAIN;
      } else if b == b'(' {
        let (txt, rem) = parser::read_while(&self.buf[1..], |b| b != b')');
        let label = match Label::try_from(txt) {
          Ok(label) => label,
          Err(e) => return Some(Err(Err::invalid_label(self, e))),
        };

        self.buf = match parser::read_one(rem, |b| b == b')') {
          Some((_, rem)) => rem,
          None => return Some(Err(Err::missing_lparen(self, txt.len()))),
        };

        let tok = Token::label(self.index, label);
        self.index += txt.len() + 2;
        return Some(Ok(tok));
      } else if b == b'@' {
        match Addr::read_from(&self.buf[1..]) {
          Ok((addr, rem, len)) => {
            let tok = Token::addr(self.index, addr);
            self.buf = rem;
            self.index += len + 1;
            return Some(Ok(tok));
          }
          Err(e) => return Some(Err(Err::invalid_addr(self, e))),
        }
      } else {
        match Inst::read_from(self.buf) {
          Ok((inst, rem, len)) => {
            let tok = Token::inst(self.index, inst);
            self.buf = rem;
            self.index += len;
            return Some(Ok(tok));
          }
          Err(e) => return Some(Err(Err::invalid_inst(self, e))),
        }
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::Parser;
  use super::TokenKind;

  use crate::com::addr::Addr;
  use crate::com::inst::Inst;
  use crate::com::label::Label;
  use crate::com::symbol::Symbol;
  use crate::hack::Comp;
  use crate::hack::Dest;
  use crate::hack::Jump;
  use crate::utils::loc::Loc;

  use std::convert::TryFrom;

  macro_rules! parser {
    ($f:expr) => {
      Parser::from(&include_bytes!(concat!("../../tests/snippets/", $f, ".asm"))[..])
    };
  }

  macro_rules! next {
    ($parser:expr, $line:expr, $col:expr, $kind:path, $inst:expr) => {{
      let tok = $parser.next().unwrap().unwrap();
      assert_eq!(Loc::new($line, $col), Loc::from_index($parser.orig(), tok.index()));
      assert_eq!(tok.kind(), $kind($inst));
    }};
  }

  #[test]
  fn empty() {
    let mut p = parser!("empty");
    assert_eq!(p.next(), None);
  }

  #[test]
  fn spaces() {
    let mut p = parser!("spaces");
    assert_eq!(p.next(), None);
  }

  #[test]
  fn comments() {
    let mut p = parser!("comments");
    assert_eq!(p.next(), None);
  }

  #[test]
  fn addr_nums() {
    let mut p = parser!("addr_nums");
    next!(p, 3, 5, TokenKind::Addr, Addr::Num(8192));
    next!(p, 5, 1, TokenKind::Addr, Addr::Num(123));
    next!(p, 9, 5, TokenKind::Addr, Addr::Num(556));
    assert_eq!(p.next(), None);
  }

  macro_rules! label {
    ($txt:expr) => {
      Label::try_from(&$txt[..]).unwrap()
    };
  }

  #[test]
  fn address_labels() {
    let mut p = parser!("addr_labels");
    next!(p, 3, 5, TokenKind::Addr, Addr::Label(label!(b"FOO")));
    next!(p, 5, 1, TokenKind::Addr, Addr::Label(label!(b"BARBAZ")));
    next!(p, 9, 5, TokenKind::Addr, Addr::Symbol(Symbol::KBD));
    next!(p, 11, 1, TokenKind::Addr, Addr::Label(label!(b"BAZOO")));
    next!(p, 13, 1, TokenKind::Addr, Addr::Symbol(Symbol::LCL));
    next!(p, 13, 6, TokenKind::Addr, Addr::Label(label!(b"LCLCL")));
    next!(p, 14, 1, TokenKind::Addr, Addr::Symbol(Symbol::SCREEN));
    next!(p, 14, 9, TokenKind::Addr, Addr::Symbol(Symbol::SP));
    next!(p, 14, 13, TokenKind::Addr, Addr::Label(label!(b"SPP")));
    next!(p, 15, 1, TokenKind::Addr, Addr::Symbol(Symbol::ARG));
    next!(p, 15, 6, TokenKind::Addr, Addr::Label(label!(b"ARG0")));
    next!(p, 16, 1, TokenKind::Addr, Addr::Symbol(Symbol::THIS));
    next!(p, 16, 7, TokenKind::Addr, Addr::Symbol(Symbol::THAT));
    next!(p, 16, 13, TokenKind::Addr, Addr::Label(label!(b"THOSE")));
    next!(p, 17, 1, TokenKind::Addr, Addr::Symbol(Symbol::R0));
    next!(p, 17, 5, TokenKind::Addr, Addr::Symbol(Symbol::R1));
    next!(p, 17, 9, TokenKind::Addr, Addr::Symbol(Symbol::R11));
    next!(p, 17, 14, TokenKind::Addr, Addr::Label(label!(b"R1_hello")));
    next!(p, 17, 24, TokenKind::Addr, Addr::Label(label!(b"R11_hello")));
    assert_eq!(p.next(), None);
  }

  #[test]
  fn label() {
    let mut p = parser!("label");
    next!(p, 3, 5, TokenKind::Addr, Addr::Label(label!(b"FOO")));
    next!(p, 5, 1, TokenKind::Label, label!(b"LABEL"));
    next!(p, 9, 5, TokenKind::Addr, Addr::Label(label!(b"LABEL")));
    next!(p, 11, 1, TokenKind::Addr, Addr::Label(label!(b"BAR")));
    next!(p, 13, 1, TokenKind::Label, Label::try_from(&b"BAR"[..]).unwrap());
    next!(p, 15, 1, TokenKind::Addr, Addr::Label(label!(b"LAB0")));
    next!(p, 17, 1, TokenKind::Label, label!(b"LAB0"));
    assert_eq!(p.next(), None);
  }

  macro_rules! inst {
    ($dest:expr, $comp:expr, $jump:expr) => {
      Inst::new($dest, $comp, $jump).unwrap()
    };
  }

  #[test]
  fn instructions() {
    let mut p = parser!("instructions");

    next!(p, 1, 1, TokenKind::Inst, inst!(Dest::A, Comp::MMinus1, Jump::Null));
    next!(p, 2, 1, TokenKind::Inst, inst!(Dest::AM, Comp::DOrA, Jump::Null));
    next!(p, 3, 1, TokenKind::Inst, inst!(Dest::AMD, Comp::APlus1, Jump::Null));

    next!(p, 4, 1, TokenKind::Inst, inst!(Dest::Null, Comp::MMinus1, Jump::JEQ));
    next!(p, 5, 1, TokenKind::Inst, inst!(Dest::Null, Comp::DOrA, Jump::JNE));
    next!(p, 6, 1, TokenKind::Inst, inst!(Dest::Null, Comp::APlus1, Jump::JMP));

    next!(p, 7, 1, TokenKind::Inst, inst!(Dest::A, Comp::MMinus1, Jump::JEQ));
    next!(p, 8, 1, TokenKind::Inst, inst!(Dest::AM, Comp::DOrA, Jump::JNE));
    next!(p, 9, 1, TokenKind::Inst, inst!(Dest::AMD, Comp::APlus1, Jump::JMP));

    assert_eq!(p.next(), None);
  }
}
