//! A `HACK` instruction.

use super::Computation;
use super::Destination;
use super::Jump;
use crate::utilities::Span;
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

    /// Span.
    span: Option<Span>,
  },

  /// An instruction without a destination section.
  #[display(fmt = "{};{}", computation, jump)]
  Branch {
    /// Branch computation.
    computation: Computation,

    /// Branch jump.
    jump: Jump,

    /// Span.
    span: Option<Span>,
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

    /// Span.
    span: Option<Span>,
  },
}

impl Instruction {
  /// Create a `HACK` instruction.
  ///
  /// # Arguments
  ///
  /// * `destination` - An optional [`Destination`] component.
  ///
  /// * `computation` - The [`Computation`] component.
  ///
  /// * `jump` - An optional [`Jump`] component.
  ///
  /// # Returns
  ///
  /// [Option::None] if both the `destination` and the `jump` are
  /// [Option::None].
  pub fn new(
    destination: Option<Destination>,
    computation: Computation,
    jump: Option<Jump>,
  ) -> Option<Self> {
    Self::new_with_span(destination, computation, jump, None)
  }

  /// Create a `HACK` instruction.
  ///
  /// # Arguments
  ///
  /// * `destination` - An optional [`Destination`] component.
  ///
  /// * `computation` - The [`Computation`] component.
  ///
  /// * `jump` - An optional [`Jump`] component.
  ///
  /// * `span` - The [`Span`] of the instruction.
  ///
  /// # Returns
  ///
  /// [Option::None] if both the `destination` and the `jump` are
  /// [Option::None].
  pub fn new_with_source(
    destination: Option<Destination>,
    computation: Computation,
    jump: Option<Jump>,
    span: Span,
  ) -> Option<Self> {
    Self::new_with_span(destination, computation, jump, Some(span))
  }

  /// Create a `HACK` instruction.
  ///
  /// # Arguments
  ///
  /// * `destination` - An optional [`Destination`] component.
  ///
  /// * `computation` - The [`Computation`] component.
  ///
  /// * `jump` - An optional [`Jump`] component.
  ///
  /// # Returns
  ///
  /// [Option::None] if both the `destination` and the `jump` are
  /// [Option::None].
  fn new_with_span(
    destination: Option<Destination>,
    computation: Computation,
    jump: Option<Jump>,
    span: Option<Span>,
  ) -> Option<Self> {
    match (destination, jump) {
      (Some(destination), Some(jump)) => {
        Some(Self::Instruction { destination, computation, jump, span })
      }
      (Some(destination), None) => {
        Some(Self::Assignment { destination, computation, span })
      }
      (None, Some(jump)) => Some(Self::Branch { computation, jump, span }),
      (None, None) => None,
    }
  }
}

/// Shorthand for creating specific [`Instruction`] objects.
///
/// See [`Instruction::new`].
///
/// # Variants
///
/// * `($destination = $computation)` - Creates an
/// [`Instruction::Assignment`] object.
///
/// * `($computation, $jump)` - Creates an [`Instruction::Branch`]
/// object.
///
/// * `($destination = $computation, $jump)` - Creates an
/// [`Instruction::Instruction`] object.
#[macro_export]
macro_rules! instruction {
  ($destination:ident = $computation:ident) => {
    Instruction::Assignment {
      destination: Destination::$destination { span: None },
      computation: Computation::$computation { span: None },
      span: None,
    }
  };
  ($computation:ident, $jump:ident) => {
    Instruction::Branch {
      computation: Computation::$computation { span: None },
      jump: Jump::$jump { span: None },
      span: None,
    }
  };
  ($destination:ident=$computation:ident, $jump:ident) => {
    Instruction::Instruction {
      destination: Destination::$destination { span: None },
      computation: Computation::$computation { span: None },
      jump: Jump::$jump { span: None },
      span: None,
    }
  };
}

#[cfg(test)]
mod tests {
  use super::Instruction;
  use crate::assert_format;
  use crate::hack::Computation;
  use crate::hack::Destination;
  use crate::hack::Jump;

  #[test]
  fn display() {
    assert_format!(instruction!(A = MMinus1), "A=M-1");
    assert_format!(instruction!(AM = DOrA), "AM=D|A");
    assert_format!(instruction!(AMD = APlus1), "AMD=A+1");
    assert_format!(instruction!(MMinus1, JEQ), "M-1;JEQ");
    assert_format!(instruction!(AM = DOrA, JNE), "AM=D|A;JNE");
  }

  #[test]
  fn new() {
    macro_rules! assert_instruction {
      ($destination:ident = $computation:ident, $instruction:expr) => {
        assert_eq!(
          Instruction::new(
            Some(Destination::$destination { span: None }),
            Computation::$computation { span: None },
            None
          ),
          Some($instruction)
        )
      };
      ($computation:ident, $jump:ident, $instruction:expr) => {
        assert_eq!(
          Instruction::new(
            None,
            Computation::$computation { span: None },
            Some(Jump::$jump { span: None }),
          ),
          Some($instruction)
        )
      };
      ($destination:ident = $computation:ident, $jump:ident, $instruction:expr) => {
        assert_eq!(
          Instruction::new(
            Some(Destination::$destination { span: None }),
            Computation::$computation { span: None },
            Some(Jump::$jump { span: None }),
          ),
          Some($instruction)
        )
      };
    }

    assert_instruction!(A = MMinus1, instruction!(A = MMinus1));
    assert_instruction!(MMinus1, JEQ, instruction!(MMinus1, JEQ));
    assert_instruction!(AM = DOrA, JNE, instruction!(AM = DOrA, JNE));
    assert_eq!(Instruction::new(None, Computation::new_d_or_a(), None), None);
  }
}
