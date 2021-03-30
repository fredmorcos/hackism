//! The destination part of `HACK` instructions.

use crate::utilities::Span;
use derive_more::Display;

/// A destination as defined by the HACK assembly reference.
///
/// The binary representation of a destination is 3 bits wide
/// representing the bits `d1`, `d2` and `d3` in an instruction.
///
/// A destination can be parsed from byte buffers using a [Lexer].
#[derive(new, Display, Debug, PartialEq, Eq, Clone, Copy)]
pub enum Destination {
  /// Memory register.
  #[display(fmt = "M")]
  M {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Data register.
  #[display(fmt = "D")]
  D {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Memory and Data registers.
  #[display(fmt = "MD")]
  MD {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Address register.
  #[display(fmt = "A")]
  A {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Address and Memory registers.
  #[display(fmt = "AM")]
  AM {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Address and Data registers.
  #[display(fmt = "AD")]
  AD {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Address, Memory and Data registers.
  #[display(fmt = "AMD")]
  AMD {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },
}

impl Destination {
  /// Create a `HACK` destination from a byte buffer.
  ///
  /// # Arguments
  ///
  /// * `input` - The input byte buffer.
  ///
  /// # Returns
  ///
  /// * `Some(Destination)` when the input matches.
  ///
  /// * [Option::None] when the input does not match.
  pub fn new(input: &[u8]) -> Option<Self> {
    Self::new_with_span(input, None)
  }

  /// Create a `HACK` destination from a byte buffer and a span.
  ///
  /// # Arguments
  ///
  /// * `input` - The input byte buffer.
  ///
  /// * `span` - The span of source covering the input buffer.
  ///
  /// # Returns
  ///
  /// * `Some(Destination)` when the input matches.
  ///
  /// * `None` when the input does not match.
  pub fn new_with_source(input: &[u8], span: Span) -> Option<Self> {
    Self::new_with_span(input, Some(span))
  }

  /// Create a `HACK` destination from a byte buffer.
  ///
  /// # Arguments
  ///
  /// * `input` - The input byte buffer.
  ///
  /// * `span` - The optional span.
  ///
  /// # Returns
  ///
  /// * `Some(Destination)` when the input matches.
  ///
  /// * `None` when the input does not match.
  fn new_with_span(input: &[u8], span: Option<Span>) -> Option<Self> {
    match input {
      b"M" => Some(Self::M { span }),
      b"D" => Some(Self::D { span }),
      b"MD" => Some(Self::MD { span }),
      b"A" => Some(Self::A { span }),
      b"AM" => Some(Self::AM { span }),
      b"AD" => Some(Self::AD { span }),
      b"AMD" => Some(Self::AMD { span }),
      _ => None,
    }
  }
}

#[cfg(test)]
mod tests {
  use super::Destination;
  use crate::assert_format;

  #[test]
  fn display() {
    assert_format!(Destination::new_m(), "M");
    assert_format!(Destination::new_d(), "D");
    assert_format!(Destination::new_md(), "MD");
    assert_format!(Destination::new_a(), "A");
    assert_format!(Destination::new_am(), "AM");
    assert_format!(Destination::new_ad(), "AD");
    assert_format!(Destination::new_amd(), "AMD");
  }

  #[test]
  fn new() {
    assert_eq!(Destination::new("M".as_bytes()), Some(Destination::new_m()));
    assert_eq!(Destination::new("D".as_bytes()), Some(Destination::new_d()));
    assert_eq!(Destination::new("MD".as_bytes()), Some(Destination::new_md()));
    assert_eq!(Destination::new("A".as_bytes()), Some(Destination::new_a()));
    assert_eq!(Destination::new("AM".as_bytes()), Some(Destination::new_am()));
    assert_eq!(Destination::new("AD".as_bytes()), Some(Destination::new_ad()));
    assert_eq!(Destination::new("AMD".as_bytes()), Some(Destination::new_amd()));
  }
}
