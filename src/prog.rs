use std::collections::HashMap as Map;
use std::convert::TryFrom;
use std::fmt;
use std::io::Bytes;
use std::io::Read;

use crate::gen::Gen;
use crate::parse::Stmt;
use crate::parse::SymInfo;
use crate::parse::{self, Parse};

pub struct Prog {
  st: Map<Vec<u8>, SymInfo>,
  stmts: Vec<Stmt>,
  idx: usize,
  gen: Gen,
}

#[derive(Debug)]
pub enum Err {
  Parse(parse::Err),
}

impl fmt::Display for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Err::Parse(e) => write!(f, "Parsing error: {}", e),
    }
  }
}

impl<R: Read> TryFrom<Bytes<R>> for Prog {
  type Error = Err;

  fn try_from(bytes: Bytes<R>) -> Result<Self, Self::Error> {
    let mut st = Map::new();
    let mut stmts = Vec::new();
    let mut parse = Parse::new(bytes, &mut st);

    for stmt in &mut parse {
      let stmt = stmt.map_err(Err::Parse)?;
      stmts.push(stmt);
    }

    Ok(Self {
      st,
      stmts,
      idx: 0,
      gen: Gen::default(),
    })
  }
}

impl Iterator for Prog {
  type Item = u16;

  fn next(&mut self) -> Option<Self::Item> {
    if let Some(stmt) = self.stmts.get(self.idx) {
      self.idx += 1;
      Some(self.gen.encode(stmt, &mut self.st))
    } else {
      self.idx = 0;
      None
    }
  }
}
