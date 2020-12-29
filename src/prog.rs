//! Structures for dealing with HACK assembly programs.
//!
//! [Prog] can be used to represent the (flat) parse tree of a HACK
//! assembly program.

use std::collections::HashMap as Map;
use std::convert::TryFrom;

use crate::addr::Addr;
use crate::inst::Inst;
use crate::label::Label;
use crate::parser;
use crate::parser::Parser;
use crate::utils;
use crate::utils::Buf;

use either::Either;

/// A HACK assembly program.
///
/// Contains the symbol table for declared labels and the list (flat
/// tree) of A- and C- instructions in the program.
///
/// # `impl TryFrom<Buf>`
///
/// A program can be created from an input buffer. This internally
/// [parses](has::parser::Parser) the input buffer.
pub struct Prog<'b> {
  symtable: Map<Label<'b>, u16>,
  instructions: Vec<Either<Addr<'b>, Inst>>,
}

/// Possible errors returned from loading a HACK assembly program.
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

pub struct EncodeErr<'p, 'b>(&'p Label<'b>);

impl<'b> Prog<'b> {
  pub fn encoder<'p>(
    &'p self,
  ) -> impl Iterator<Item = Result<u16, EncodeErr<'p, 'b>>> + 'p {
    self.instructions.iter().map(move |item| match item {
      Either::Left(Addr::Num(addr)) => Ok(*addr),
      Either::Left(Addr::Symbol(symbol)) => Ok(u16::from(*symbol)),
      Either::Left(Addr::Label(label)) => match self.symtable.get(label) {
        Some(addr) => Ok(*addr),
        None => Err(EncodeErr(label)),
      },
      Either::Right(inst) => Ok(u16::from(*inst)),
    })
  }

  pub fn text_encoder<'p>(
    &'p self,
  ) -> impl Iterator<Item = Result<[u8; 16], EncodeErr<'p, 'b>>> + 'p {
    self.encoder().map(|v| v.map(utils::u16_bintext))
  }
}
