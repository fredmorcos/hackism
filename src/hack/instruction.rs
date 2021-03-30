//! A `HACK` instruction.

use super::Computation;
use super::Destination;
use super::EqualToken;
use super::Jump;
use super::SemicolonToken;
use derive_more::Display;

/// An instruction as defined by the HACK assembly reference.
///
/// The binary representation of an instruction is 16 bits wide and
/// consists of a [Destination], a [Computation] and a [Jump].
#[derive(new, Display, Debug, PartialEq, Eq, Clone, Copy)]
pub enum Instruction {
  /// An instruction without a jump section.
  #[display(fmt = "{}={}", destination, computation)]
  Assignment {
    /// Assignment destination.
    destination: Destination,

    /// Assignment computation.
    computation: Computation,
  },

  /// An instruction without a destination section.
  #[display(fmt = "{};{}", computation, jump)]
  Branch {
    /// Branch computation.
    computation: Computation,

    /// Branch jump.
    jump: Jump,
  },

  /// An instruction with all sections used.
  #[display(fmt = "{}={};{}", destination, computation, jump)]
  Instruction {
    /// Instruction destination.
    destination: Destination,

    /// Instruction computation.
    computation: Computation,

    /// Instruction jump.
    jump: Jump,
  },
}

impl Instruction {
  /// Create a new instruction.
  ///
  /// [Option::None] if both the `destination` and the `jump` are
  /// [Option::None].
  pub fn new(
    destination: Option<Destination>,
    computation: Computation,
    jump: Option<Jump>,
  ) -> Option<Self> {
    match (destination, jump) {
      (Some(destination), Some(jump)) => {
        Some(Self::Instruction { d: destination, computation, j: jump })
      }
      (Some(destination), None) => Some(Self::Assignment { destination, computation }),
      (None, Some(jump)) => Some(Self::Branch { computation, jump }),
      (None, None) => None,
    }
  }
}

/// Shorthand for creating specific instructions.
#[macro_export]
macro_rules! instruction {
  ($destination:ident=$computation:ident) => {
    Instruction::Assignment {
      destination: Destination::$destination,
      computation: Computation::$computation,
    }
  };
  ($computation:ident,$jump:ident) => {
    Instruction::Branch { computation: Computation::$computation, jump: Jump::$jump }
  };
  ($destination:ident=$computation:ident, $jump:ident) => {
    Instruction::Instruction {
      destination: Destination::$destination,
      computation: Computation::$computation,
      jump: Jump::$jump,
    }
  };
}

#[cfg(test)]
mod tests {
  use super::Instruction;
  use crate::hack::Computation;
  use crate::hack::Destination;
  use crate::hack::Jump;
  use crate::utilities::tests;

  #[test]
  fn display() {
    assert_format!(instruction!(A = MMinus1), "A=M-1");
    assert_format!(instruction!(AM = DOrA), "AM=D|A");
    assert_format!(instruction!(AMD = APlus1), "AMD=A+1");
    assert_format!(instruction!(MMinus1, JEQ), "M-1;JEQ");
    assert_format!(instruction!(AM = DOrA, JNE), "AM=D|A;JNE");
  }
}
