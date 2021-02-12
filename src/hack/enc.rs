//! Structures related to encoding (codegen) HACK programs.

use crate::conv;
use crate::hack::Addr;
use crate::hack::Prog;
use either::Either;

/// HACK program encoder that produces binary files.
pub struct Bin<'b, 'p> {
  /// The HACK program.
  prog: &'p mut Prog<'b>,
  /// The index of the current instruction being encoded.
  index: usize,
  /// The index of the most recently user-defined symbol.
  var_index: u16,
}

impl<'b, 'p> From<&'p mut Prog<'b>> for Bin<'b, 'p> {
  fn from(prog: &'p mut Prog<'b>) -> Self {
    Bin { prog, index: 0, var_index: 16 }
  }
}

impl Iterator for Bin<'_, '_> {
  type Item = [u8; 2];

  fn next(&mut self) -> Option<Self::Item> {
    let &inst = self.prog.insts().get(self.index)?;
    self.index += 1;

    let v = match inst {
      Either::Right(inst) => u16::from(inst),
      Either::Left(Addr::Num(addr)) => addr,
      Either::Left(Addr::Sym(sym)) => u16::from(sym),
      Either::Left(Addr::Var(var)) => {
        if let Some(&v) = self.prog.symtable().get(&var) {
          v
        } else {
          self.prog.symtable_mut().insert(var, self.var_index);
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
pub struct BinText<'b, 'p> {
  /// The binary encoder used to produce instruction bintext from.
  encoder: Bin<'b, 'p>,
}

impl<'b, 'p> From<&'p mut Prog<'b>> for BinText<'b, 'p> {
  fn from(prog: &'p mut Prog<'b>) -> Self {
    BinText { encoder: Bin::from(prog) }
  }
}

impl Iterator for BinText<'_, '_> {
  type Item = [u8; 16];

  fn next(&mut self) -> Option<Self::Item> {
    let val = self.encoder.next()?;
    Some(conv::u16_bintext(u16::from(val[0]) << 8 | u16::from(val[1])))
  }
}
