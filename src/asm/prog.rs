//! Structures for dealing with HACK assembly programs.
//!
//! [Prog] can be used to represent the (flat) parse tree of a HACK
//! assembly program.

use crate::asm::parser;
use crate::asm::parser::Parser;
use crate::com::addr::Addr;
use crate::com::inst::Inst;
use crate::com::label::Label;
use crate::utils::buf::Buf;
use crate::utils::conv;
use crate::utils::loc::Loc;

use std::collections::HashMap as Map;
use std::convert::TryFrom;

use derive_more::Display;
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
  /// The symbol table for forward declarations.
  symtable: Map<Label<'b>, u16>,

  /// List of collected instructions.
  instructions: Vec<Either<Addr<'b>, Inst>>,
}

/// Possible errors returned from loading a HACK assembly program.
#[derive(Display, Debug, Clone, PartialEq, Eq)]
#[display(fmt = "Program error: {}")]
pub enum Err {
  /// Parse errors.
  #[display(fmt = "Parser error: {}", _0)]
  Parser(parser::Err),

  /// A duplicate label was found.
  ///
  /// Contains the name and index of the label.
  #[display(fmt = "Duplicate label `{}` at `{}`", _0, _1)]
  DuplicateLabel(String, Loc),
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
            let token_loc = Loc::from_index(buf, token_index);
            return Err(Err::DuplicateLabel(String::from(label.label()), token_loc));
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

/// HACK program encoder that produces binary files.
pub struct BinEncoder<'b, 'p> {
  /// The HACK program.
  prog: &'p mut Prog<'b>,
  /// The index of the current instruction being encoded.
  index: usize,
  /// The index of the most recently user-defined symbol.
  var_index: u16,
}

impl Iterator for BinEncoder<'_, '_> {
  type Item = [u8; 2];

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
          self.prog.symtable.insert(*label, self.var_index);
          let current_var_index = self.var_index;
          self.var_index += 1;
          current_var_index
        }
      }
    };

    Some([(v >> 8) as u8, v as u8])
  }
}

/// HACK program encoder that produces text files.
pub struct TxtEncoder<'b, 'p> {
  /// The binary encoder used to produce textual representations of
  /// instructions from.
  encoder: BinEncoder<'b, 'p>,
}

impl Iterator for TxtEncoder<'_, '_> {
  type Item = [u8; 16];

  fn next(&mut self) -> Option<Self::Item> {
    let val = self.encoder.next()?;
    Some(conv::u16_bintext(u16::from(val[0]) << 8 | u16::from(val[1])))
  }
}

impl<'b> Prog<'b> {
  /// Create an encoder that will produce binary files.
  pub fn encoder<'p>(&'p mut self) -> BinEncoder<'b, 'p> {
    BinEncoder { prog: self, index: 0, var_index: 16 }
  }

  /// Create an encoder that will produce bintext files.
  pub fn text_encoder<'p>(&'p mut self) -> TxtEncoder<'b, 'p> {
    TxtEncoder { encoder: BinEncoder { prog: self, index: 0, var_index: 16 } }
  }
}
