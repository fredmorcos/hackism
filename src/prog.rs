use std::collections::HashMap as Map;
use std::convert::TryFrom;

use crate::inst;
use crate::parser;
use crate::parser::Parser;
use crate::utils::Buf;

use either::Either;

pub struct Prog<'b> {
  symtable: Map<inst::Label<'b>, u16>,
  instructions: Vec<Either<inst::Addr<'b>, inst::Inst>>,
}

pub enum Err {
  Parser(parser::Err),
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
