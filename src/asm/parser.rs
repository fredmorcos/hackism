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
use crate::utils::loc;
use crate::utils::loc::Index;
use crate::utils::loc::Loc;
use crate::utils::parser;

use std::convert::TryFrom;
use std::fmt;

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
  pub fn loc(&self, tok: &Token) -> Loc {
    loc::loc(self.orig, tok.index())
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
}

/// Kind of parsing error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrKind {
  /// Expected a second `/` to form a comment.
  ExpectedComment,
  /// Invalid label.
  InvalidLabel(label::Err),
  /// Missing the closing ')' for a label.
  MissingLParen,
  /// Invalid address.
  InvalidAddr(addr::Err),
  /// Invalid instruction.
  InvalidInst(inst::Err),
}

impl fmt::Display for ErrKind {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      ErrKind::ExpectedComment => write!(f, "expected a second '/' to form a comment"),
      ErrKind::InvalidLabel(e) => write!(f, "invalid label: {}", e),
      ErrKind::MissingLParen => write!(f, "expected a closing parenthesis ')' for label"),
      ErrKind::InvalidAddr(e) => write!(f, "invalid address: {}", e),
      ErrKind::InvalidInst(e) => write!(f, "invalid instruction: {}", e),
    }
  }
}

/// Error during parsing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Err {
  index: usize,
  kind: ErrKind,
}

impl fmt::Display for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{} at {}", self.kind, self.index)
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
  pub fn kind(&self) -> &ErrKind {
    &self.kind
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
          Some(_) => {
            return Some(Err(Err::new(self.index + 1, ErrKind::ExpectedComment)))
          }
          None => return Some(Err(Err::new(self.index + 1, ErrKind::ExpectedComment))),
        }

        let (com, rem) = parser::read_until_nl(self.buf);
        self.index += com.len();
        self.buf = rem;
        continue 'MAIN;
      } else if b == b'(' {
        let index = self.index;
        let (txt, rem) = parser::read_while(&self.buf[1..], |b| b != b')');
        let label = match Label::try_from(txt) {
          Ok(label) => label,
          Err(e) => return Some(Err(Err::new(self.index, ErrKind::InvalidLabel(e)))),
        };
        self.buf = match parser::read_one(rem, |b| b == b')') {
          Some((_, rem)) => rem,
          None => {
            return Some(Err(Err::new(self.index + txt.len(), ErrKind::MissingLParen)));
          }
        };
        self.index += txt.len() + 2;
        return Some(Ok(Token { index, kind: TokenKind::Label(label) }));
      } else if b == b'@' {
        let index = self.index;
        match Addr::read_from(&self.buf[1..]) {
          Ok((addr, rem, len)) => {
            self.buf = rem;
            self.index += len + 1;
            return Some(Ok(Token { index, kind: TokenKind::Addr(addr) }));
          }
          Err(e) => return Some(Err(Err::new(self.index, ErrKind::InvalidAddr(e)))),
        }
      } else {
        let index = self.index;
        match Inst::read_from(self.buf) {
          Ok((inst, rem, len)) => {
            self.buf = rem;
            self.index += len;
            return Some(Ok(Token { index, kind: TokenKind::Inst(inst) }));
          }
          Err(e) => return Some(Err(Err::new(self.index, ErrKind::InvalidInst(e)))),
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
  use crate::com::comp::Comp;
  use crate::com::dest::Dest;
  use crate::com::inst::Inst;
  use crate::com::jump::Jump;
  use crate::com::label::Label;
  use crate::com::symbol::Symbol;
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
      assert_eq!(Loc::new($line, $col), $parser.loc(&tok));
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
