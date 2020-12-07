use std::collections::HashMap as Map;
use std::fmt;

use crate::gen::Gen;
use crate::lex::Txt;
use crate::parse::Stmt;
use crate::parse::SymInfo;
use crate::parse::{self, Parse};

pub struct Prog {
  st: Map<Txt, SymInfo>,
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

impl Prog {
  pub fn try_from(buf: &[u8]) -> Result<Self, Err> {
    let mut st = Map::new();
    let mut stmts = Vec::new();
    let mut parse = Parse::new(buf, &mut st);

    while let Some(stmt) = parse.next() {
      let stmt = stmt.map_err(Err::Parse)?;
      stmts.push(stmt);
    }

    Ok(Self { st, stmts, idx: 0, gen: Gen::default() })
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

impl Prog {
  pub fn text_encode(val: u16) -> [u8; 16] {
    Gen::text_encode(val)
  }

  pub fn num_statements(&self) -> usize {
    self.stmts.len()
  }

  pub fn num_labels(&self) -> usize {
    self.st.len()
  }
}
