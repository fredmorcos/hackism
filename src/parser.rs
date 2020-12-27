//! Structures to be used for parsing HACK programs.
//!
//! [Parser] is the primary structure in this module that should be
//! used to parse HACK programs.

use crate::inst;
use crate::utils;
use crate::utils::Buf;

use std::convert::TryFrom;

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
/// use has::parser::Parser;
/// use has::parser::Token;
/// use has::parser::TokenKind;
/// use has::inst;
/// use std::convert::TryFrom;
///
/// let prog = "(FOO)\n@FOO\nD=D+A;JMP".as_bytes();
/// let mut parser = Parser::from(prog);
/// assert_eq!(parser.next(), Some(Ok(Token::new(0,
///   TokenKind::Label(inst::Label::try_from("FOO".as_bytes()).unwrap()),
/// ))));
/// assert_eq!(parser.next(), Some(Ok(Token::new(6,
///   TokenKind::Addr(inst::Addr::read_from("FOO".as_bytes()).unwrap().0),
/// ))));
/// assert_eq!(parser.next(), Some(Ok(Token::new(11,
///   TokenKind::Inst(inst::Inst::read_from("D=D+A;JMP".as_bytes()).unwrap().0),
/// ))));
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
    let index = tok.index();
    let mut loc = (1, 1);

    for &b in &self.orig[..index] {
      if b == b'\n' {
        loc.0 += 1;
        loc.1 = 1;
      } else {
        loc.1 += 1;
      }
    }

    loc
  }
}

/// The kind of a [Token].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind<'b> {
  /// A label as defined by the HACK assembly reference: `(FOO)`.
  Label(inst::Label<'b>),
  /// An address as defined by the HACK assembly reference: `@FOO`.
  Addr(inst::Addr<'b>),
  /// An instruction as defined by the HACK assembly reference:
  /// `D=A+1;JMP`.
  Inst(inst::Inst),
}

/// Units returned by iterating over a [Parser].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'b> {
  index: usize,
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
  pub fn new(index: usize, kind: TokenKind<'b>) -> Self {
    Self { index, kind }
  }

  /// Returns the index in the buffer the token was created from.
  pub fn index(&self) -> usize {
    self.index
  }

  /// Returns the kind of token.
  pub fn kind(&self) -> &TokenKind {
    &self.kind
  }
}

/// Kind of parsing error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrKind {
  /// Expected a second `/` to form a comment.
  ExpectedComment,
  /// Parsed a label that was invalid.
  ///
  /// Either the label text was invalid or a closing ')' was missing.
  InvalidLabel,
  /// Invalid address.
  InvalidAddr(inst::AddrErr),
  /// Invalid instruction.
  InvalidInst(inst::InstErr),
}

/// Error during parsing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Err {
  index: usize,
  kind: ErrKind,
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
  type Item = Result<Token<'b>, Err>;

  fn next(&mut self) -> Option<Self::Item> {
    'MAIN: loop {
      let &b = self.buf.get(0)?;

      if b.is_ascii_whitespace() {
        let (ws, rem) = utils::read_while(self.buf, |b| b.is_ascii_whitespace());
        self.index += ws.len();
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

        let (com, rem) = utils::read_while(self.buf, |b| b != b'\n');
        self.index += com.len();
        self.buf = rem;
        continue 'MAIN;
      } else if b == b'(' {
        let index = self.index;
        let (txt, rem) = utils::read_while(&self.buf[1..], |b| b != b')');
        let label = match inst::Label::try_from(txt) {
          Ok(label) => label,
          Err(_) => return Some(Err(Err::new(self.index, ErrKind::InvalidLabel))),
        };
        self.buf = match utils::read_one(rem, |b| b == b')') {
          Some((_, rem)) => rem,
          None => {
            return Some(Err(Err::new(self.index + txt.len(), ErrKind::InvalidLabel)));
          }
        };
        self.index += txt.len() + 2;
        return Some(Ok(Token { index, kind: TokenKind::Label(label) }));
      } else if b == b'@' {
        let index = self.index;
        match inst::Addr::read_from(&self.buf[1..]) {
          Ok((addr, rem, len)) => {
            self.buf = rem;
            self.index += len + 1;
            return Some(Ok(Token { index, kind: TokenKind::Addr(addr) }));
          }
          Err(e) => return Some(Err(Err::new(self.index, ErrKind::InvalidAddr(e)))),
        }
      } else {
        let index = self.index;
        match inst::Inst::read_from(self.buf) {
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
  use crate::inst;
  use crate::inst::Comp;
  use crate::inst::Dest;
  use crate::inst::Inst;
  use crate::inst::Jump;
  use std::convert::TryFrom;

  macro_rules! parser {
    ($f:expr) => {
      Parser::from(&include_bytes!(concat!("../tests/data/", $f))[..])
    };
  }

  macro_rules! next {
    ($parser:expr, $loc:expr, $kind:path, $inst:expr) => {{
      let tok = $parser.next().unwrap().unwrap();
      assert_eq!(tok.kind(), &$kind($inst));
      assert_eq!($parser.loc(&tok), $loc);
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
    next!(p, (3, 5), TokenKind::Addr, inst::Addr::Num(8192));
    next!(p, (5, 1), TokenKind::Addr, inst::Addr::Num(123));
    next!(p, (9, 5), TokenKind::Addr, inst::Addr::Num(556));
    assert_eq!(p.next(), None);
  }

  macro_rules! label {
    ($txt:expr) => {
      inst::Label::try_from(&$txt[..]).unwrap()
    };
  }

  #[test]
  fn address_labels() {
    let mut p = parser!("addr_labels");
    next!(p, (3, 5), TokenKind::Addr, inst::Addr::Label(label!(b"FOO")));
    next!(p, (5, 1), TokenKind::Addr, inst::Addr::Label(label!(b"BARBAZ")));
    next!(p, (9, 5), TokenKind::Addr, inst::Addr::Predef(inst::Predef::KBD));
    next!(p, (11, 1), TokenKind::Addr, inst::Addr::Label(label!(b"BAZOO")));
    next!(p, (13, 1), TokenKind::Addr, inst::Addr::Predef(inst::Predef::LCL));
    next!(p, (13, 6), TokenKind::Addr, inst::Addr::Label(label!(b"LCLCL")));
    next!(p, (14, 1), TokenKind::Addr, inst::Addr::Predef(inst::Predef::SCREEN));
    next!(p, (14, 9), TokenKind::Addr, inst::Addr::Predef(inst::Predef::SP));
    next!(p, (14, 13), TokenKind::Addr, inst::Addr::Label(label!(b"SPP")));
    next!(p, (15, 1), TokenKind::Addr, inst::Addr::Predef(inst::Predef::ARG));
    next!(p, (15, 6), TokenKind::Addr, inst::Addr::Label(label!(b"ARG0")));
    next!(p, (16, 1), TokenKind::Addr, inst::Addr::Predef(inst::Predef::THIS));
    next!(p, (16, 7), TokenKind::Addr, inst::Addr::Predef(inst::Predef::THAT));
    next!(p, (16, 13), TokenKind::Addr, inst::Addr::Label(label!(b"THOSE")));
    next!(p, (17, 1), TokenKind::Addr, inst::Addr::Predef(inst::Predef::R0));
    next!(p, (17, 5), TokenKind::Addr, inst::Addr::Predef(inst::Predef::R1));
    next!(p, (17, 9), TokenKind::Addr, inst::Addr::Predef(inst::Predef::R11));
    next!(p, (17, 14), TokenKind::Addr, inst::Addr::Label(label!(b"R1_hello")));
    next!(p, (17, 24), TokenKind::Addr, inst::Addr::Label(label!(b"R11_hello")));
    assert_eq!(p.next(), None);
  }

  #[test]
  fn label() {
    let mut p = parser!("label");
    next!(p, (3, 5), TokenKind::Addr, inst::Addr::Label(label!(b"FOO")));
    next!(p, (5, 1), TokenKind::Label, label!(b"LABEL"));
    next!(p, (9, 5), TokenKind::Addr, inst::Addr::Label(label!(b"LABEL")));
    next!(p, (11, 1), TokenKind::Addr, inst::Addr::Label(label!(b"BAR")));
    next!(p, (13, 1), TokenKind::Label, inst::Label::try_from(&b"BAR"[..]).unwrap());
    next!(p, (15, 1), TokenKind::Addr, inst::Addr::Label(label!(b"LAB0")));
    next!(p, (17, 1), TokenKind::Label, label!(b"LAB0"));
    assert_eq!(p.next(), None);
  }

  #[test]
  fn instructions() {
    let mut p = parser!("instructions");

    next!(p, (1, 1), TokenKind::Inst, Inst::new(Dest::A, Comp::MMinus1, Jump::Null));
    next!(p, (2, 1), TokenKind::Inst, Inst::new(Dest::AM, Comp::DOrA, Jump::Null));
    next!(p, (3, 1), TokenKind::Inst, Inst::new(Dest::AMD, Comp::APlus1, Jump::Null));

    next!(p, (4, 1), TokenKind::Inst, Inst::new(Dest::Null, Comp::MMinus1, Jump::JEQ));
    next!(p, (5, 1), TokenKind::Inst, Inst::new(Dest::Null, Comp::DOrA, Jump::JNE));
    next!(p, (6, 1), TokenKind::Inst, Inst::new(Dest::Null, Comp::APlus1, Jump::JMP));

    next!(p, (7, 1), TokenKind::Inst, Inst::new(Dest::A, Comp::MMinus1, Jump::JEQ));
    next!(p, (8, 1), TokenKind::Inst, Inst::new(Dest::AM, Comp::DOrA, Jump::JNE));
    next!(p, (9, 1), TokenKind::Inst, Inst::new(Dest::AMD, Comp::APlus1, Jump::JMP));

    assert_eq!(p.next(), None);
  }
}
