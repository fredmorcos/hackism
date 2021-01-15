//! Structures for dealing with HACK assembly programs.
//!
//! [Prog] can be used to represent the (flat) parse tree of a HACK
//! assembly program.

use crate::com::addr::Addr;
use crate::com::inst;
use crate::com::inst::Inst;
use crate::dis::parser;
use crate::dis::parser::Parser;
use crate::utils::Buf;

use std::{convert::TryFrom, fmt};

/// A HACK assembly program.
///
/// Contains the symbol table for declared labels and the list (flat
/// tree) of A- and C- instructions in the program.
///
/// # `impl TryFrom<Buf>`
///
/// A program can be created from an input buffer. This internally
/// [parses](Parser) the input buffer.
pub struct Prog {
  instructions: Vec<parser::Token>,
}

/// Possible errors returned from loading a HACK assembly program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Err {
  /// Parse errors.
  Parser(parser::Err),
}

impl fmt::Display for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Err::Parser(e) => write!(f, "parse error: {}", e),
    }
  }
}

impl Prog {
  fn new_parser(
    parser: &mut dyn Iterator<Item = Result<parser::Token, parser::Err>>,
  ) -> Result<Self, Err> {
    let instructions = parser.collect::<Result<_, _>>().map_err(Err::Parser)?;
    Ok(Self { instructions })
  }

  pub fn new(buf: Buf<'_>) -> Result<Self, Err> {
    let mut parser: Parser<parser::Binary> = Parser::from(buf);
    Prog::new_parser(&mut parser)
  }

  pub fn new_text(buf: Buf<'_>) -> Result<Self, Err> {
    let mut parser: Parser<parser::Text> = Parser::from(buf);
    Prog::new_parser(&mut parser)
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodeErr {
  InvalidInst(inst::DecodeErr, usize),
  InvalidAddr(usize),
}

impl fmt::Display for DecodeErr {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      DecodeErr::InvalidInst(e, index) => {
        write!(f, "Invalid instruction at byte {}: {}", index, e)
      }
      DecodeErr::InvalidAddr(index) => {
        write!(f, "Invalid address instruction at byte {}: value out of range", index)
      }
    }
  }
}

pub struct ProgDecoder<'p> {
  prog: &'p mut Prog,
  index: usize,
}

impl Iterator for ProgDecoder<'_> {
  type Item = Result<String, DecodeErr>;

  fn next(&mut self) -> Option<Self::Item> {
    let token = self.prog.instructions.get(self.index)?;
    let inst = token.value();
    self.index += 1;

    if inst & 0b1000_0000_0000_0000 == 0 {
      // A-instruction
      let inst = inst & 0b0111_1111_1111_1111;
      let decoded = match Addr::try_from(inst) {
        Ok(decoded) => decoded,
        Err(_) => return Some(Err(DecodeErr::InvalidAddr(token.index()))),
      };

      Some(Ok(format!("{}", decoded)))
    } else {
      // C-instruction
      let inst = inst & 0b0001_1111_1111_1111;
      let decoded = match Inst::try_from(inst) {
        Ok(decoded) => decoded,
        Err(e) => return Some(Err(DecodeErr::InvalidInst(e, token.index()))),
      };

      Some(Ok(format!("{}", decoded)))
    }
  }
}

impl Prog {
  pub fn decoder(&mut self) -> ProgDecoder {
    ProgDecoder { index: 0, prog: self }
  }
}
