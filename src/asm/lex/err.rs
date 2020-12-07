#![warn(clippy::all)]

use crate::utils::loc::Loc;
use crate::utils::loc::SrcLoc;
use std::error::Error;
use std::fmt;

#[derive(Debug)]
pub struct Err {
  pub source: Box<dyn Error>,
  pub sloc: SrcLoc,
  pub loc: Loc,
}

macro_rules! err {
  ($loc:expr, $source:expr) => {
    Err { source: Box::new($source), sloc: srcloc!(), loc: $loc }
  };
}

impl fmt::Display for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "parsing error at {} (in {})", self.loc, self.sloc)
  }
}

impl Error for Err {
  fn source(&self) -> Option<&(dyn Error + 'static)> {
    Some(&*self.source)
  }
}

#[derive(Debug)]
pub struct EOF {
  pub expect: &'static str,
}

macro_rules! eof {
  ($loc:expr, $expect:expr) => {
    err!($loc, EOF { expect: $expect })
  };
}

impl fmt::Display for EOF {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "unexpected end of file, expected {}", self.expect)
  }
}

impl Error for EOF {}

#[derive(Debug)]
pub struct UnexpectedByte {
  pub byte: u8,
  pub expect: &'static str,
}

macro_rules! unexpected_byte {
  ($loc:expr, $byte:expr, $expect:expr) => {
    err!($loc, UnexpectedByte { byte: $byte, expect: $expect })
  };
}

impl fmt::Display for UnexpectedByte {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "unexpected byte `{}`, expected {}", self.byte, self.expect)
  }
}

impl Error for UnexpectedByte {}

#[derive(Debug)]
pub struct UnexpectedTok {
  pub tok: String,
  pub expect: &'static str,
}

macro_rules! unexpected_tok {
  ($loc:expr, $tok:expr, $expect:expr) => {
    err!($loc, UnexpectedByte { tok: $tok, expect: $expect })
  };
}

impl fmt::Display for UnexpectedTok {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "unexpected token `{}`, expected {}", self.tok, self.expect)
  }
}

impl Error for UnexpectedTok {}

#[derive(Debug)]
pub struct AddrRange {
  addr: String,
  max: u16,
  expect: &'static str,
}

macro_rules! addr_range {
  ($loc:expr, $addr:expr, $max:expr, $expect:expr) => {
    err!($loc, AddrRange { addr: $addr, max: $max, expect: $expect })
  };
}

impl fmt::Display for AddrRange {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(
      f,
      "address `{}` out of range of `{}` (15 bits address), expected {}",
      self.addr, self.max, self.expect
    )
  }
}

impl Error for AddrRange {}
