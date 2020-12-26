//! Structures to be used for parsing HACK programs.
//!
//! [Parser] is the primary structure in this module that should be
//! used to parse HACK programs.

use crate::inst;
use crate::utils;
use crate::utils::Buf;
use crate::utils::Byte;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Loc {
  line: usize,
  col: usize,
}

impl Default for Loc {
  fn default() -> Self {
    Self { line: 1, col: 0 }
  }
}

impl Loc {
  pub fn new(line: usize, col: usize) -> Self {
    Self { line, col }
  }

  pub fn inc(&mut self, b: Byte) {
    if b == b'\n' {
      self.line += 1;
      self.col = 0;
    } else {
      self.col += 1;
    }
  }
}

impl Parser<'_> {
  pub fn loc(&self, tok: &Token) -> Loc {
    let index = tok.index();
    let mut loc = Loc::default();

    for &i in &self.orig[..index] {
      loc.inc(i);
    }

    loc
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind<'b> {
  Label(inst::Label<'b>),
  Addr(inst::Addr<'b>),
  Inst(inst::Inst),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'b> {
  index: usize,
  kind: TokenKind<'b>,
}

impl<'b> Token<'b> {
  pub fn new(index: usize, kind: TokenKind<'b>) -> Self {
    Self { index, kind }
  }

  pub fn index(&self) -> usize {
    self.index
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrKind {
  ExpectedComment,
  InvalidLabel,
  InvalidAddr(inst::AddrErr),
  InvalidInst(inst::InstErr),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Err {
  index: usize,
  kind: ErrKind,
}

impl Err {
  fn new(index: usize, kind: ErrKind) -> Self {
    Self { index, kind }
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
  use super::Loc;
  use super::Parser;

  macro_rules! parser {
    ($f:expr) => {
      Parser::from(&include_bytes!(concat!("../tests/data/", $f))[..])
    };
  }

  macro_rules! next {
    ($parser:expr, $inst:expr) => {
      assert_eq!($parser.next(), Some(Ok($inst)));
    };
  }

  #[test]
  fn empty() {
    let mut parser = parser!("empty");
    assert_eq!(parser.next(), None);
  }

  #[test]
  fn spaces() {
    let mut parser = parser!("spaces");
    assert_eq!(parser.next(), None);
  }

  #[test]
  fn comments() {
    let mut parser = parser!("comments");
    assert_eq!(parser.next(), None);
  }

  #[test]
  fn addr_nums() {
    let mut parser = parser!("addr_nums");
    next!(parser, Tok(loc!(3, 5), Inst::Addr(Addr::Num(8192))));
    next!(parser, Tok(loc!(5, 1), Inst::Addr(Addr::Num(123))));
    next!(parser, Tok(loc!(9, 5), Inst::Addr(Addr::Num(556))));
    assert_eq!(parser.next(), None);
  }

  macro_rules! label {
    ($label:path, $line:expr, $col:expr, $text:expr) => {
      $label(loc!($line, $col), Text::from_slice($text))
    };
  }

  #[test]
  fn address_labels() {
    let mut parser = parser!("addr_labels");
    next!(parser, label!(Inst::AddrLabel, 3, 5, b"FOO"));
    next!(parser, label!(Inst::AddrLabel, 5, 1, b"BARBAZ"));
    next!(parser, Inst::AddrKBD(loc!(9, 5)));
    next!(parser, label!(Inst::AddrLabel, 11, 1, b"BAZOO"));
    next!(parser, Inst::AddrLCL(loc!(13, 1)));
    next!(parser, label!(Inst::AddrLabel, 13, 6, b"LCLCL"));
    next!(parser, Inst::AddrSCREEN(loc!(14, 1)));
    next!(parser, Inst::AddrSP(loc!(14, 9)));
    next!(parser, label!(Inst::AddrLabel, 14, 13, b"SPP"));
    next!(parser, Inst::AddrARG(loc!(15, 1)));
    next!(parser, label!(Inst::AddrLabel, 15, 6, b"ARG0"));
    next!(parser, Inst::AddrTHIS(loc!(16, 1)));
    next!(parser, Inst::AddrTHAT(loc!(16, 7)));
    next!(parser, label!(Inst::AddrLabel, 16, 13, b"THOSE"));
    next!(parser, Inst::AddrR0(loc!(17, 1)));
    next!(parser, Inst::AddrR1(loc!(17, 5)));
    next!(parser, Inst::AddrR11(loc!(17, 9)));
    next!(parser, label!(Inst::AddrLabel, 17, 14, b"R1_hello"));
    next!(parser, label!(Inst::AddrLabel, 17, 24, b"R11_hello"));
    assert_eq!(parser.next(), None);
  }

  #[test]
  fn label() {
    let mut parser = parser!("label");
    next!(parser, label!(Inst::AddrLabel, 3, 5, b"FOO"));
    next!(parser, label!(Inst::Label, 5, 1, b"LABEL"));
    next!(parser, label!(Inst::AddrLabel, 9, 5, b"LABEL"));
    next!(parser, label!(Inst::AddrLabel, 11, 1, b"BAR"));
    next!(parser, label!(Inst::Label, 13, 1, b"BAR"));
    next!(parser, label!(Inst::AddrLabel, 15, 1, b"LAB0"));
    next!(parser, label!(Inst::Label, 17, 1, b"LAB0"));
    assert_eq!(parser.next(), None);
  }

  #[test]
  fn assignments() {
    let mut parser = parser!("assignments");
    assert_next!(
      parser,
      Token::Assignment(Destination::A, Computation::MMinus1),
      Location::new(1, 1)
    );
    assert_next!(
      parser,
      Token::Assignment(Destination::AM, Computation::DOrA),
      Location::new(2, 1)
    );
    assert_next!(
      parser,
      Token::Assignment(Destination::AMD, Computation::APlus1),
      Location::new(3, 1)
    );
    assert_eq!(parser.next(), None);
  }

  #[test]
  fn branches() {
    let mut parser = parser!("branches");
    assert_next!(parser, tbuf, Token::Comp(Comp::MMinus1));
    assert_eq!(parser.token_pos(), Location::new(1, 1));
    assert_next!(parser, tbuf, Token::Semi);
    assert_eq!(parser.token_pos(), Location::new(1, 4));
    assert_next!(parser, tbuf, Token::Jump(Jump::JEQ));
    assert_eq!(parser.token_pos(), Location::new(1, 5));
    assert_next!(parser, tbuf, Token::Comp(Comp::DOrA));
    assert_eq!(parser.token_pos(), Location::new(2, 1));
    assert_next!(parser, tbuf, Token::Semi);
    assert_eq!(parser.token_pos(), Location::new(2, 4));
    assert_next!(parser, tbuf, Token::Jump(Jump::JNE));
    assert_eq!(parser.token_pos(), Location::new(2, 5));
    assert_next!(parser, tbuf, Token::Comp(Comp::APlus1));
    assert_eq!(parser.token_pos(), Location::new(3, 1));
    assert_next!(parser, tbuf, Token::Semi);
    assert_eq!(parser.token_pos(), Location::new(3, 4));
    assert_next!(parser, tbuf, Token::Jump(Jump::JMP));
    assert_eq!(parser.token_pos(), Location::new(3, 5));
    assert_eq!(parser.next(), None);
  }

  #[test]
  fn instructions() {
    let mut parser = parser!("instructions");
    assert_next!(parser, tbuf, Token::Dest(Dest::A));
    assert_eq!(parser.token_pos(), Location::new(1, 1));
    assert_next!(parser, tbuf, Token::Comp(Comp::MMinus1));
    assert_eq!(parser.token_pos(), Location::new(1, 3));
    assert_next!(parser, tbuf, Token::Semi);
    assert_eq!(parser.token_pos(), Location::new(1, 6));
    assert_next!(parser, tbuf, Token::Jump(Jump::JEQ));
    assert_eq!(parser.token_pos(), Location::new(1, 7));
    assert_next!(parser, tbuf, Token::Dest(Dest::AM));
    assert_eq!(parser.token_pos(), Location::new(2, 1));
    assert_next!(parser, tbuf, Token::Comp(Comp::DOrA));
    assert_eq!(parser.token_pos(), Location::new(2, 4));
    assert_next!(parser, tbuf, Token::Semi);
    assert_eq!(parser.token_pos(), Location::new(2, 7));
    assert_next!(parser, tbuf, Token::Jump(Jump::JNE));
    assert_eq!(parser.token_pos(), Location::new(2, 8));
    assert_next!(parser, tbuf, Token::Dest(Dest::AMD));
    assert_eq!(parser.token_pos(), Location::new(3, 1));
    assert_next!(parser, tbuf, Token::Comp(Comp::APlus1));
    assert_eq!(parser.token_pos(), Location::new(3, 5));
    assert_next!(parser, tbuf, Token::Semi);
    assert_eq!(parser.token_pos(), Location::new(3, 8));
    assert_next!(parser, tbuf, Token::Jump(Jump::JMP));
    assert_eq!(parser.token_pos(), Location::new(3, 9));
    assert_eq!(parser.next(), None);
  }
}
