//! Structures for dealing with HACK assembly programs.
//!
//! [Prog] can be used to represent the (flat) parse tree of a HACK
//! assembly program.

use crate::asm::parser;
use crate::asm::parser::Parser;
use crate::com::addr::Addr;
use crate::com::inst::Inst;
use crate::com::label::Label;
use crate::utils;
use crate::utils::Buf;

use std::collections::HashMap as Map;
use std::convert::TryFrom;
use std::fmt;

use either::Either;

/// A HACK assembly program.
///
/// Contains the symbol table for declared labels and the list (flat
/// tree) of A- and C- instructions in the program.
///
/// # `impl TryFrom<Buf>`
///
/// A program can be created from an input buffer. This internally
/// [parses](Parser) the input buffer.
pub struct Prog<'b> {
  symtable: Map<Label<'b>, u16>,
  instructions: Vec<Either<Addr<'b>, Inst>>,
}

/// Possible errors returned from loading a HACK assembly program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Err {
  /// Parse errors.
  Parser(parser::Err),
  /// A duplicate label was found.
  ///
  /// Contains the index of the duplicate label in the input buffer.
  DuplicateLabel(usize),
}

impl fmt::Display for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Err::Parser(e) => write!(f, "parse error: {}", e),
      Err::DuplicateLabel(index) => write!(f, "Duplicate label at index: {}", index),
    }
  }
}

impl<'b> TryFrom<Buf<'b>> for Prog<'b> {
  type Error = Err;

  fn try_from(buf: Buf<'b>) -> Result<Self, Self::Error> {
    let mut symtable = Map::new();
    let mut instructions = Vec::new();
    let parser = Parser::from(buf);
    let mut index = 0;

    for token in parser {
      let token = token.map_err(Err::Parser)?;
      let token_index = token.index();

      match token.kind() {
        parser::TokenKind::Label(label) => {
          if symtable.insert(label, index).is_some() {
            return Err(Err::DuplicateLabel(token_index));
          }
        }
        parser::TokenKind::Addr(addr) => {
          instructions.push(Either::Left(addr));
          index += 1;
        }
        parser::TokenKind::Inst(inst) => {
          instructions.push(Either::Right(inst));
          index += 1;
        }
      }
    }

    Ok(Self { symtable, instructions })
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EncodeErr {
  TooManySymbols,
}

impl fmt::Display for EncodeErr {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      EncodeErr::TooManySymbols => write!(f, "too many symbols"),
    }
  }
}

pub struct ProgEncoder<'b, 'p> {
  prog: &'p mut Prog<'b>,
  index: usize,
  var_index: usize,
}

impl Iterator for ProgEncoder<'_, '_> {
  type Item = Result<[u8; 2], EncodeErr>;

  fn next(&mut self) -> Option<Self::Item> {
    let inst = self.prog.instructions.get(self.index)?;
    self.index += 1;

    let v = match inst {
      Either::Right(inst) => u16::from(*inst),
      Either::Left(Addr::Num(addr)) => *addr,
      Either::Left(Addr::Symbol(symbol)) => u16::from(*symbol),
      Either::Left(Addr::Label(label)) => {
        if let Some(v) = self.prog.symtable.get(label) {
          *v
        } else {
          if self.var_index > u16::MAX as usize {
            return Some(Err(EncodeErr::TooManySymbols));
          }

          let current_var_index = self.var_index as u16;
          self.var_index += 1;

          self.prog.symtable.insert(label.clone(), current_var_index);
          current_var_index
        }
      }
    };

    Some(Ok([(v >> 8) as u8, v as u8]))
  }
}

pub struct ProgEncoderText<'b, 'p> {
  encoder: ProgEncoder<'b, 'p>,
}

impl Iterator for ProgEncoderText<'_, '_> {
  type Item = Result<[u8; 16], EncodeErr>;

  fn next(&mut self) -> Option<Self::Item> {
    match self.encoder.next()? {
      Ok(v) => Some(Ok(utils::u16_bintext(u16::from(v[0]) << 8 | u16::from(v[1])))),
      Err(e) => Some(Err(e)),
    }
  }
}

impl<'b> Prog<'b> {
  pub fn encoder<'p>(&'p mut self) -> ProgEncoder<'b, 'p> {
    ProgEncoder { prog: self, index: 0, var_index: 16 }
  }

  pub fn text_encoder<'p>(&'p mut self) -> ProgEncoderText<'b, 'p> {
    ProgEncoderText { encoder: ProgEncoder { prog: self, index: 0, var_index: 16 } }
  }
}
