//! The jump part of `HACK` instructions.

use crate::utilities::Span;
use derive_more::Display;

/// A jump as defined by the HACK assembly reference.
///
/// The binary representation of a jump is 3 bits wide representing
/// the bits `j1`, `j2` and `j3` in an instruction.
///
/// A jump can be parsed from byte buffers using a \[Lexer\].
#[derive(new, Display, Debug, PartialEq, Eq, Clone, Copy)]
pub enum Jump {
  /// Jump on greater than.
  #[display(fmt = "JGT")]
  JGT {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Jump on equal.
  #[display(fmt = "JEQ")]
  JEQ {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Jump on greater than or equal.
  #[display(fmt = "JGE")]
  JGE {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Jump on less than.
  #[display(fmt = "JLT")]
  JLT {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Jump on not equal.
  #[display(fmt = "JNE")]
  JNE {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Jump on less than or equal.
  #[display(fmt = "JLE")]
  JLE {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Unconditional jump.
  #[display(fmt = "JMP")]
  JMP {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },
}

impl Jump {
  /// Create a `HACK` jump from a byte buffer.
  ///
  /// # Arguments
  ///
  /// * `input` - The input byte buffer.
  ///
  /// # Returns
  ///
  /// * `Some(Jump)` when the input matches.
  ///
  /// * `None` when the input does not match.
  pub fn new(input: &[u8]) -> Option<Self> {
    Self::new_with_span(input, None)
  }

  /// Create a `HACK` jump from a byte buffer and a span.
  ///
  /// # Arguments
  ///
  /// * `input` - The input byte buffer.
  ///
  /// * `span` - The span of source covering the input buffer.
  ///
  /// # Returns
  ///
  /// * `Some(Jump)` when the input matches.
  ///
  /// * `None` when the input does not match.
  pub fn new_with_source(input: &[u8], span: Span) -> Option<Self> {
    Self::new_with_span(input, Some(span))
  }

  /// Create a `HACK` jump from a byte buffer.
  ///
  /// # Arguments
  ///
  /// * `input` - The input byte buffer.
  ///
  /// * `span` - The optional span.
  ///
  /// # Returns
  ///
  /// * `Some(Jump)` when the input matches.
  ///
  /// * `None` when the input does not match.
  fn new_with_span(input: &[u8], span: Option<Span>) -> Option<Self> {
    match input {
      b"JGT" => Some(Jump::JGT { span }),
      b"JEQ" => Some(Jump::JEQ { span }),
      b"JGE" => Some(Jump::JGE { span }),
      b"JLT" => Some(Jump::JLT { span }),
      b"JNE" => Some(Jump::JNE { span }),
      b"JLE" => Some(Jump::JLE { span }),
      b"JMP" => Some(Jump::JMP { span }),
      _ => None,
    }
  }
}

#[cfg(test)]
mod tests {
  use super::Jump;
  use crate::assert_format;

  #[test]
  fn display() {
    assert_format!(Jump::new_jgt(), "JGT");
    assert_format!(Jump::new_jeq(), "JEQ");
    assert_format!(Jump::new_jge(), "JGE");
    assert_format!(Jump::new_jlt(), "JLT");
    assert_format!(Jump::new_jne(), "JNE");
    assert_format!(Jump::new_jle(), "JLE");
    assert_format!(Jump::new_jmp(), "JMP");
  }

  #[test]
  fn new() {
    assert_eq!(Jump::new("JGT".as_bytes()), Some(Jump::new_jgt()));
    assert_eq!(Jump::new("JEQ".as_bytes()), Some(Jump::new_jeq()));
    assert_eq!(Jump::new("JGE".as_bytes()), Some(Jump::new_jge()));
    assert_eq!(Jump::new("JLT".as_bytes()), Some(Jump::new_jlt()));
    assert_eq!(Jump::new("JNE".as_bytes()), Some(Jump::new_jne()));
    assert_eq!(Jump::new("JLE".as_bytes()), Some(Jump::new_jle()));
    assert_eq!(Jump::new("JMP".as_bytes()), Some(Jump::new_jmp()));
  }
}
