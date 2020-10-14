#![warn(clippy::all)]

use io::{Bytes, Read};
use std::fmt;
use std::io;

use crate::inst::Inst;
use crate::lex::{self, Lex, Tok};
use crate::pos::Pos;
use crate::st::ST;

pub struct Parse<R: Read> {
  lex: Lex<R>,
  la: Option<Tok>,
  st: ST,
}

impl<R: Read> Parse<R> {
  pub fn new(bytes: Bytes<R>) -> Self {
    Self {
      lex: Lex::new(bytes),
      la: Option::default(),
      st: ST::default(),
    }
  }
}

#[derive(PartialEq, Eq)]
pub enum Err {
  Lex(lex::Err),
  Range(Pos, Vec<u8>, &'static str),
}

impl fmt::Display for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Err::Lex(e) => write!(f, "Lexing error: {}", e),
      Err::Range(pos, addr, msg) => write!(
        f,
        "Value out of range: address {:?} at {}: {}",
        addr, pos, msg
      ),
    }
  }
}

impl fmt::Debug for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    (self as &dyn fmt::Display).fmt(f)
  }
}

impl<R: Read> Iterator for Parse<R> {
  type Item = Result<Inst, Err>;

  fn next(&mut self) -> Option<Self::Item> {
    macro_rules! next {
      ($b:block) => {
        match self.lex.next() {
          Some(Ok(t)) => t,
          Some(Err(e)) => return Some(Err(Err::Lex(e))),
          None => $b,
        };
      };
    }

    let t1 = if let Some(la) = self.la.take() {
      la
    } else {
      next!({ return None })
    };

    match t1 {
      Tok::NumAddr(pos, addr) => Some(Ok(Inst::Addr(pos, addr))),
      Tok::NameAddr(pos, addr) => {
        if let Some(addr) = self.st.get(&addr) {
          Some(Ok(Inst::Addr(pos, addr)))
        } else {
          Some(Err(Err::Range(
            pos,
            addr,
            "label address would be out of range",
          )))
        }
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use std::io::{BufReader, Read};

  use crate::pos::Pos;

  use super::Inst;
  use super::Parse;

  macro_rules! parse {
    ($f:expr) => {
      Parse::new(
        BufReader::new(&include_bytes!(concat!("../tests/data/", $f))[..]).bytes(),
      )
    };
  }

  macro_rules! assert_next {
    ($parse:expr, $e:expr) => {
      assert_eq!($parse.next(), Some(Ok($e)))
    };
  }

  #[test]
  fn empty() {
    let mut parse = parse!("empty");
    assert_eq!(parse.next(), None);
  }

  #[test]
  fn spaces() {
    let mut parse = parse!("spaces");
    assert_eq!(parse.next(), None);
  }

  #[test]
  fn comments() {
    let mut parse = parse!("comments");
    assert_eq!(parse.next(), None);
  }

  #[test]
  fn num_address() {
    let mut parse = parse!("num_address");
    assert_next!(parse, Inst::Addr(Pos::new(3, 5), 8192));
    assert_next!(parse, Inst::Addr(Pos::new(5, 1), 123));
    assert_next!(parse, Inst::Addr(Pos::new(9, 5), 556));
    assert_eq!(parse.next(), None);
  }

  #[test]
  fn name_address() {
    let mut parse = parse!("name_address");
    assert_eq!(parse.next(), Some(Ok(Inst::Addr(Pos::new(3, 5), 16))));
    assert_eq!(parse.next(), Some(Ok(Inst::Addr(Pos::new(5, 1), 17))));
    assert_eq!(parse.next(), Some(Ok(Inst::Addr(Pos::new(9, 5), 2))));
    assert_eq!(parse.next(), None);
  }
}
