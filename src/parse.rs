#![warn(clippy::all)]

use io::{Bytes, Read};
use std::io;

use crate::inst::Inst;
use crate::lex::{self, Lex, Tok};

pub struct Parse<R: Read> {
  lex: Lex<R>,
  la: Option<Tok>,
}

impl<R: Read> Parse<R> {
  pub fn new(bytes: Bytes<R>) -> Self {
    Self {
      lex: Lex::new(bytes),
      la: Option::default(),
    }
  }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Err {
  Lex(lex::Err),
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
      Tok::NumAddr(pos, addr) => Some(Ok(Inst::NumAddr(pos, addr))),
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
    assert_next!(parse, Inst::NumAddr(Pos::new(3, 5), 8192));
    assert_next!(parse, Inst::NumAddr(Pos::new(5, 1), 123));
    assert_next!(parse, Inst::NumAddr(Pos::new(9, 5), 556));
    assert_eq!(parse.next(), None);
  }
}
