//! Structures related to HACK programs.
//!
//! [Prog] can be used to represent the (flat) parse tree of a HACK
//! assembly program. The program can be parsed from HACK assembly
//! source code or disassembled from a compiled HACK binary or bintext
//! file.

use crate::hack::dec;
use crate::hack::enc;
use crate::hack::Addr;
use crate::hack::Inst;
use crate::hack::Parser;
use crate::hack::ParserErr;
use crate::hack::TokenKind;
use crate::hack::Var;
use crate::Buf;
use crate::Loc;
use derive_more::Display;
use derive_more::From;
use either::Either;
use std::collections::HashMap as Map;

/// Symbol table.
pub type Symtable<'b> = Map<Var<'b>, u16>;

/// A HACK assembly program.
///
/// Contains the symbol table for declared labels and the list of A-
/// and C- instructions in the program.
pub struct Prog<'b> {
  /// The symbol table for forward declarations.
  symtable: Symtable<'b>,

  /// List of collected instructions.
  insts: Vec<Either<Addr<'b>, Inst>>,
}

/// Possible errors returned from loading a HACK assembly program.
#[derive(Display, Debug, Clone, PartialEq, Eq, From)]
#[display(fmt = "Program error: {}")]
pub enum Err {
  /// Assembly errors.
  #[display(fmt = "Assembly error: {}", _0)]
  Asm(ParserErr),

  /// Disassembly errors.
  #[display(fmt = "Disassembly error: {}", _0)]
  Dis(dec::Err),

  /// A duplicate label was found.
  ///
  /// Contains the name and index of the label.
  #[display(fmt = "Duplicate label `{}` at `{}`", _0, _1)]
  #[from(ignore)]
  DuplicateLabel(String, Loc),

  /// Instruction decoding error.
  #[display(fmt = "Decoding error: {}", _0)]
  Decode(dec::DecodeErr),
}

impl<'b> Prog<'b> {
  /// Create a program from a buffer containing HACK assembly code.
  ///
  /// This parses the input buffer and populates the symbol table.
  ///
  /// # Example
  ///
  /// ```
  /// use has::hack::Prog;
  ///
  /// let buf = "@FOO\nD=A;JMP\n(FOO)".as_bytes();
  /// let prog = Prog::from_source(buf).unwrap();
  /// assert_eq!(prog.symtable().len(), 1);
  /// assert_eq!(prog.insts().len(), 2);
  /// ```
  pub fn from_source(buf: Buf<'b>) -> Result<Self, Err> {
    let mut symtable = Map::new();
    let mut insts = Vec::new();
    let parser = Parser::from(buf);
    let mut index = 0;

    for token in parser {
      let token = token.map_err(Err::Asm)?;
      let token_index = token.index();

      match token.kind() {
        TokenKind::Var(label) => {
          if symtable.insert(label, index).is_some() {
            let token_loc = Loc::from_index(buf, token_index);
            return Err(Err::DuplicateLabel(String::from(label.name()), token_loc));
          }
        }
        TokenKind::Addr(addr) => {
          insts.push(Either::Left(addr));
          index += 1;
        }
        TokenKind::Inst(inst) => {
          insts.push(Either::Right(inst));
          index += 1;
        }
      }
    }

    Ok(Self { symtable, insts })
  }

  pub fn from_bin(buf: Buf<'b>) -> Result<Self, Err> {
    let parser: dec::Parser<dec::BinParser> = dec::Parser::from(buf);
    let insts = parser
      .collect::<Result<Vec<dec::Token>, _>>()?
      .into_iter()
      .map(|t| t.decode(buf))
      .collect::<Result<Vec<_>, _>>()?;
    Ok(Self { symtable: Symtable::new(), insts })
  }

  pub fn from_bintext(buf: Buf<'b>) -> Result<Self, Err> {
    let parser: dec::Parser<dec::BinTextParser> = dec::Parser::from(buf);
    let insts = parser
      .collect::<Result<Vec<dec::Token>, _>>()?
      .into_iter()
      .map(|t| t.decode(buf))
      .collect::<Result<Vec<_>, _>>()?;
    Ok(Self { symtable: Symtable::new(), insts })
  }

  /// Get the list of instructions in a program.
  pub fn insts(&self) -> &[Either<Addr<'b>, Inst>] {
    &self.insts
  }

  /// Get the symbol table in a program.
  pub fn symtable(&self) -> &Symtable<'b> {
    &self.symtable
  }

  /// Get a mutable reference to the symbol table in a program.
  pub fn symtable_mut(&mut self) -> &mut Symtable<'b> {
    &mut self.symtable
  }

  /// Create and return a bintext encoder to encode this program.
  pub fn to_bintext<'p>(&'p mut self) -> enc::BinText<'p, 'b> {
    enc::BinText::from(self)
  }

  /// Create and return a binary encoder to encode this program.
  pub fn to_bin<'p>(&'p mut self) -> enc::Bin<'p, 'b> {
    enc::Bin::from(self)
  }

  pub fn to_source(&self) -> impl Iterator<Item = String> + '_ {
    self.insts.iter().map(|i| format!("{}", i))
  }
}
