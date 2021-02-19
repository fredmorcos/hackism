//! Structures related to HACK programs.
//!
//! [Prog] can be used to represent the (flat) parse tree of a HACK
//! assembly program. The program can be parsed from HACK assembly
//! source code or disassembled from a compiled HACK binary or bintext
//! file.

use crate::conv;
use crate::hack::dec;
use crate::hack::Addr;
use crate::hack::Cmd;
use crate::hack::CmdErr;
use crate::hack::Label;
use crate::hack::Parser;
use crate::hack::ParserErr;
use crate::hack::TokenKind;
use crate::Buf;
use crate::Loc;
use derive_more::Display;
use derive_more::From;
use std::collections::HashMap as Map;

/// Symbol table.
pub type Symtable<'b> = Map<Label<'b>, u16>;

/// A HACK assembly program.
///
/// Contains the symbol table for declared labels and the list of A-
/// and C- instructions in the program.
pub struct Prog<'b> {
  /// The symbol table for forward declarations.
  symtable: Symtable<'b>,

  /// List of collected instructions.
  insts: Vec<Cmd<'b>>,
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

  /// Label or user-defined variable not found.
  #[display(fmt = "Label or variable `{}` not found", _0)]
  LabelNotFound(String),

  /// Instruction decoding error.
  #[display(fmt = "Decoding error: {}", _0)]
  Decode(CmdErr),
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
        TokenKind::Label(label) => {
          if symtable.insert(label, index).is_some() {
            let token_loc = Loc::from_index(buf, token_index);
            return Err(Err::DuplicateLabel(String::from(label.name()), token_loc));
          }
        }
        TokenKind::Addr(addr) => {
          insts.push(Cmd::Addr(addr));
          index += 1;
        }
        TokenKind::Inst(inst) => {
          insts.push(Cmd::Inst(inst));
          index += 1;
        }
      }
    }

    let mut var_index = 16;

    for inst in &insts {
      if let Cmd::Addr(Addr::Label(label)) = inst {
        symtable.entry(*label).or_insert_with(|| {
          let current_var_index = var_index;
          var_index += 1;
          current_var_index
        });
      }
    }

    Ok(Self { symtable, insts })
  }

  /// Create a program from a buffer containing HACK binary code.
  ///
  /// This parses the input buffer and populates an empty symbol table.
  pub fn from_bin(buf: Buf<'b>) -> Result<Self, Err> {
    let parser: dec::Parser<dec::BinParser> = dec::Parser::from(buf);
    let insts = parser
      .collect::<Result<Vec<dec::Token>, _>>()?
      .into_iter()
      .map(|t| Cmd::new(t.value(), t.index(), buf))
      .collect::<Result<Vec<_>, _>>()?;
    Ok(Self { symtable: Symtable::new(), insts })
  }

  /// Create a program from a buffer containing HACK bintext code.
  ///
  /// This parses the input buffer and populates an empty symbol table.
  pub fn from_bintext(buf: Buf<'b>) -> Result<Self, Err> {
    let parser: dec::Parser<dec::BinTextParser> = dec::Parser::from(buf);
    let insts = parser
      .collect::<Result<Vec<dec::Token>, _>>()?
      .into_iter()
      .map(|t| Cmd::new(t.value(), t.index(), buf))
      .collect::<Result<Vec<_>, _>>()?;
    Ok(Self { symtable: Symtable::new(), insts })
  }

  /// Get the list of instructions in a program.
  pub fn insts(&self) -> &[Cmd<'b>] {
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
  pub fn to_bintext(&self) -> impl Iterator<Item = Result<[u8; 16], Err>> + '_ {
    self.to_bin().map(|res| match res {
      Ok(val) => Ok(conv::u16_bintext(u16::from(val[0]) << 8 | u16::from(val[1]))),
      Err(e) => Err(e),
    })
  }

  /// Create and return a binary encoder to encode this program.
  pub fn to_bin(&self) -> impl Iterator<Item = Result<[u8; 2], Err>> + '_ {
    self.insts.iter().copied().map(move |i| {
      let addr = match i {
        Cmd::Inst(inst) => u16::from(inst),
        Cmd::Addr(Addr::Num(addr)) => addr,
        Cmd::Addr(Addr::Sym(sym)) => u16::from(sym),
        Cmd::Addr(Addr::Label(label)) => {
          if let Some(&addr) = self.symtable.get(&label) {
            addr
          } else {
            return Err(Err::LabelNotFound(String::from(label.name())));
          }
        }
      };

      Ok([(addr >> 8) as u8, addr as u8])
    })
  }

  /// Produce HACK assembly out of the instructions in a program.
  pub fn to_source(&self) -> impl Iterator<Item = String> + '_ {
    self.insts.iter().map(|i| format!("{}", i))
  }
}
