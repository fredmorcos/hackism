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
  DuplicateLabel(u16),
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

      match token.kind() {
        parser::TokenKind::Label(label) => {
          if symtable.insert(label, index).is_some() {
            return Err(Err::DuplicateLabel(index));
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

// impl Prog {
//   pub fn text_encode(val: u16) -> [u8; 16] {
//     Gen::text_encode(val)
//   }

//   pub fn num_statements(&self) -> usize {
//     self.stmts.len()
//   }

//   pub fn num_labels(&self) -> usize {
//     self.st.len()
//   }
// }
