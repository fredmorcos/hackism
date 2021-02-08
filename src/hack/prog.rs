//! Structures related to HACK programs.
//!
//! [Prog] can be used to represent the (flat) parse tree of a HACK
//! assembly program. The program can be parsed from HACK assembly
//! source code or disassembled from a compiled HACK binary or bintext
//! file.

use crate::asm;
use crate::conv;
use crate::dis;
use crate::hack::Addr;
use crate::hack::Inst;
use crate::hack::Var;
use crate::Buf;
use crate::Loc;
use derive_more::Display;
use either::Either;
use std::collections::HashMap as Map;

/// A HACK assembly program.
///
/// Contains the symbol table for declared labels and the list (flat
/// tree) of A- and C- instructions in the program.
pub struct Prog<'b> {
  /// The symbol table for forward declarations.
  symtable: Map<Var<'b>, u16>,

  /// List of collected instructions.
  instructions: Vec<Either<Addr<'b>, Inst>>,
}

/// Possible errors returned from loading a HACK assembly program.
#[derive(Display, Debug, Clone, PartialEq, Eq)]
#[display(fmt = "Program error: {}")]
pub enum Err {
  /// Assembly parse errors.
  #[display(fmt = "Assembly parsing error: {}", _0)]
  AsmParser(asm::parser::Err),

  /// Disassembly parse errors.
  #[display(fmt = "Disassembly parsing error: {}", _0)]
  DisParser(dis::parser::Err),

  /// A duplicate label was found.
  ///
  /// Contains the name and index of the label.
  #[display(fmt = "Duplicate label `{}` at `{}`", _0, _1)]
  DuplicateLabel(String, Loc),
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
  /// let prog = Prog::from_hack(buf).unwrap();
  /// assert_eq!(prog.symtable().len(), 1);
  /// assert_eq!(prog.instructions().len(), 2);
  /// ```
  pub fn from_hack(buf: Buf<'b>) -> Result<Self, Err> {
    let mut symtable = Map::new();
    let mut instructions = Vec::new();
    let parser = asm::parser::Parser::from(buf);
    let mut index = 0;

    for token in parser {
      let token = token.map_err(Err::AsmParser)?;
      let token_index = token.index();

      match token.kind() {
        asm::parser::TokenKind::Var(label) => {
          if symtable.insert(label, index).is_some() {
            let token_loc = Loc::from_index(buf, token_index);
            return Err(Err::DuplicateLabel(String::from(label.name()), token_loc));
          }
        }
        asm::parser::TokenKind::Addr(addr) => {
          instructions.push(Either::Left(addr));
          index += 1;
        }
        asm::parser::TokenKind::Inst(inst) => {
          instructions.push(Either::Right(inst));
          index += 1;
        }
      }
    }

    Ok(Self { symtable, instructions })
  }

  /// Get the list of instructions in a program.
  pub fn instructions(&self) -> &[Either<Addr<'b>, Inst>] {
    &self.instructions
  }

  /// Get the symbol table in a program.
  pub fn symtable(&self) -> &Map<Var<'b>, u16> {
    &self.symtable
  }
}

/// HACK program encoder that produces binary files.
pub struct BinEnc<'b, 'p> {
  /// The HACK program.
  prog: &'p mut Prog<'b>,
  /// The index of the current instruction being encoded.
  index: usize,
  /// The index of the most recently user-defined symbol.
  var_index: u16,
}

impl Iterator for BinEnc<'_, '_> {
  type Item = [u8; 2];

  fn next(&mut self) -> Option<Self::Item> {
    let inst = self.prog.instructions.get(self.index)?;
    self.index += 1;

    let v = match inst {
      Either::Right(inst) => u16::from(*inst),
      Either::Left(Addr::Num(addr)) => *addr,
      Either::Left(Addr::Sym(sym)) => u16::from(*sym),
      Either::Left(Addr::Var(var)) => {
        if let Some(&v) = self.prog.symtable.get(var) {
          v
        } else {
          self.prog.symtable.insert(*var, self.var_index);
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
pub struct TxtEnc<'b, 'p> {
  /// The binary encoder used to produce instruction bintext from.
  encoder: BinEnc<'b, 'p>,
}

impl Iterator for TxtEnc<'_, '_> {
  type Item = [u8; 16];

  fn next(&mut self) -> Option<Self::Item> {
    let val = self.encoder.next()?;
    Some(conv::u16_bintext(u16::from(val[0]) << 8 | u16::from(val[1])))
  }
}

impl<'b> Prog<'b> {
  /// Create an encoder that will produce binary files.
  pub fn enc<'p>(&'p mut self) -> BinEnc<'b, 'p> {
    BinEnc { prog: self, index: 0, var_index: 16 }
  }

  /// Create an encoder that will produce bintext files.
  pub fn bintext_enc<'p>(&'p mut self) -> TxtEnc<'b, 'p> {
    TxtEnc { encoder: BinEnc { prog: self, index: 0, var_index: 16 } }
  }
}
