//! Structures for abstracting over different instructions.

use std::convert::TryFrom;

use crate::hack::Addr;
use crate::hack::AddrErr;
use crate::hack::Inst;
use crate::hack::InstDecodeErr;
use crate::Buf;
use crate::Loc;
use derive_more::Display;
use derive_more::From;

/// A command abstracts over whether an instruction is an
/// A-instruction or C-instruction.
#[derive(Display, Debug, Clone, Copy, PartialEq, Eq, From)]
#[display(fmt = "{}")]
pub enum Cmd<'b> {
  /// A-instruction.
  #[display(fmt = "{}", _0)]
  Addr(Addr<'b>),

  /// C-instruction.
  #[display(fmt = "{}", _0)]
  Inst(Inst),
}

/// Errors when decoding programs from their compiled form.
#[derive(Display, Debug, Clone, PartialEq, Eq)]
#[display(fmt = "Disassembler decoding error: {}")]
pub enum Err {
  /// Invalid instruction.
  #[display(fmt = "Invalid instruction at {}: {}", _0, _1)]
  InvalidInst(Loc, InstDecodeErr),

  /// Invalid address.
  #[display(fmt = "Invalid address instruction {}: {}", _0, _1)]
  InvalidAddr(Loc, AddrErr),
}

impl Err {
  /// Create a `DecodeErr::InvalidInst` variant.
  pub fn invalid_inst(orig: Buf, index: usize, err: InstDecodeErr) -> Self {
    Self::InvalidInst(Loc::from_index(orig, index), err)
  }

  /// Create a `DecodeErr::InvalidAddr` variant.
  pub fn invalid_addr(orig: Buf, index: usize, err: AddrErr) -> Self {
    Self::InvalidAddr(Loc::from_index(orig, index), err)
  }
}

impl<'b> Cmd<'b> {
  /// Create a new command from a binary encoding.
  ///
  /// # Arguments
  ///
  /// * `value` - The binary encoded command.
  ///
  /// * `index` - The index of the command in the input buffer.
  ///
  /// * `orig` - The original (untraversed) input buffer.
  pub fn new(value: u16, index: usize, orig: Buf<'b>) -> Result<Self, Err> {
    if value & 0b1000_0000_0000_0000 == 0 {
      // A-instruction
      let inst = value & 0b0111_1111_1111_1111;
      match Addr::try_from(inst) {
        Ok(decoded) => Ok(Cmd::Addr(decoded)),
        Err(e) => Err(Err::invalid_addr(orig, index, e)),
      }
    } else {
      // C-instruction
      let inst = value & 0b0001_1111_1111_1111;
      match Inst::try_from(inst) {
        Ok(decoded) => Ok(Cmd::Inst(decoded)),
        Err(e) => Err(Err::invalid_inst(orig, index, e)),
      }
    }
  }
}
