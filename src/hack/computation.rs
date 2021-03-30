//! The computation part of `HACK` instructions.

use crate::utilities::Span;
use derive_more::Display;

/// A computation as defined by the HACK assembly reference.
///
/// The binary representation is 7 bits wide representing the bits
/// `a`, `c1`, `c2`, `c3`, `c4`, `c5` and `c6` in an instruction.
///
/// A computation can be parsed from byte buffers using a [Lexer].
#[derive(new, Display, Debug, PartialEq, Eq, Clone, Copy)]
pub enum Computation {
  /// Integer literal `0`.
  #[display(fmt = "0")]
  Zero {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Integer literal `1`.
  #[display(fmt = "1")]
  One {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Integer literal `-1` (negative one).
  #[display(fmt = "-1")]
  Negative1 {
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

  /// Address register.
  #[display(fmt = "A")]
  A {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Bitwise inverse of the Data register.
  #[display(fmt = "!D")]
  NotD {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Bitwise inverse of the Address register.
  #[display(fmt = "!A")]
  NotA {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Negated value of the Data register.
  #[display(fmt = "-D")]
  NegativeD {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Negated value of the Address register.
  #[display(fmt = "-A")]
  NegativeA {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Data register value + 1.
  #[display(fmt = "D+1")]
  DPlus1 {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Address register value + 1.
  #[display(fmt = "A+1")]
  APlus1 {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Data register value - 1.
  #[display(fmt = "D-1")]
  DMinus1 {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Address register value - 1.
  #[display(fmt = "A-1")]
  AMinus1 {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Data register value + the Address register value.
  #[display(fmt = "D+A")]
  DPlusA {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Data register value - the Address register value.
  #[display(fmt = "D-A")]
  DMinusA {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Address register value - the Data register value.
  #[display(fmt = "A-D")]
  AMinusD {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Bitwise And of the Data and Address registers.
  #[display(fmt = "D&A")]
  DAndA {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Bitwise Or of the Data and Address registers.
  #[display(fmt = "D|A")]
  DOrA {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Memory register.
  #[display(fmt = "M")]
  M {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Bitwise inverse of the Memory register.
  #[display(fmt = "!M")]
  NotM {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Negated value of the Memory register.
  #[display(fmt = "-M")]
  NegativeM {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Memory register value + 1.
  #[display(fmt = "M+1")]
  MPlus1 {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Memory register value - 1.
  #[display(fmt = "M-1")]
  MMinus1 {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Data register value + the Memory register value.
  #[display(fmt = "D+M")]
  DPlusM {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Data register value - the Memory register value.
  #[display(fmt = "D-M")]
  DMinusM {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Memory register value + the Data register value.
  #[display(fmt = "M-D")]
  MMinusD {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Bitwise And of the Data and Memory registers.
  #[display(fmt = "D&M")]
  DAndM {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },

  /// Bitwise Or of the Data and Memory registers.
  #[display(fmt = "D|M")]
  DOrM {
    /// Source span.
    #[new(default)]
    span: Option<Span>,
  },
}

impl Computation {
  /// Create a `HACK` computation from a byte buffer.
  ///
  /// # Arguments
  ///
  /// * `input` - The input byte buffer.
  ///
  /// # Returns
  ///
  /// * `Some(Computation)` when the input matches.
  ///
  /// * `None` when the input does not match.
  pub fn new(input: &[u8]) -> Option<Self> {
    Self::new_with_span(input, None)
  }

  /// Create a `HACK` computation from a byte buffer and a span.
  ///
  /// # Arguments
  ///
  /// * `input` - The input byte buffer.
  ///
  /// * `span` - The span of source covering the input buffer.
  ///
  /// # Returns
  ///
  /// * `Some(Computation)` when the input matches.
  ///
  /// * `None` when the input does not match.
  pub fn new_with_source(input: &[u8], span: Span) -> Option<Self> {
    Self::new_with_span(input, Some(span))
  }

  /// Create a `HACK` computation from a byte buffer.
  ///
  /// # Arguments
  ///
  /// * `input` - The input byte buffer.
  ///
  /// * `span` - The optional span.
  ///
  /// # Returns
  ///
  /// * `Some(Computation)` when the input matches.
  ///
  /// * `None` when the input does not match.
  fn new_with_span(input: &[u8], span: Option<Span>) -> Option<Self> {
    match input {
      b"0" => Some(Self::Zero { span }),
      b"1" => Some(Self::One { span }),
      b"-1" => Some(Self::Negative1 { span }),
      b"D" => Some(Self::D { span }),
      b"A" => Some(Self::A { span }),
      b"!D" => Some(Self::NotD { span }),
      b"!A" => Some(Self::NotA { span }),
      b"-D" => Some(Self::NegativeD { span }),
      b"-A" => Some(Self::NegativeA { span }),
      b"D+1" => Some(Self::DPlus1 { span }),
      b"A+1" => Some(Self::APlus1 { span }),
      b"D-1" => Some(Self::DMinus1 { span }),
      b"A-1" => Some(Self::AMinus1 { span }),
      b"D+A" => Some(Self::DPlusA { span }),
      b"D-A" => Some(Self::DMinusA { span }),
      b"A-D" => Some(Self::AMinusD { span }),
      b"D&A" => Some(Self::DAndA { span }),
      b"D|A" => Some(Self::DOrA { span }),
      b"M" => Some(Self::M { span }),
      b"!M" => Some(Self::NotM { span }),
      b"-M" => Some(Self::NegativeM { span }),
      b"M+1" => Some(Self::MPlus1 { span }),
      b"M-1" => Some(Self::MMinus1 { span }),
      b"D+M" => Some(Self::DPlusM { span }),
      b"D-M" => Some(Self::DMinusM { span }),
      b"M-D" => Some(Self::MMinusD { span }),
      b"D&M" => Some(Self::DAndM { span }),
      b"D|M" => Some(Self::DOrM { span }),
      _ => None,
    }
  }
}

#[cfg(test)]
mod tests {
  use super::Computation;
  use crate::assert_format;

  #[test]
  fn display() {
    assert_format!(Computation::new_zero(), "0");
    assert_format!(Computation::new_one(), "1");
    assert_format!(Computation::new_negative1(), "-1");
    assert_format!(Computation::new_d(), "D");
    assert_format!(Computation::new_a(), "A");
    assert_format!(Computation::new_not_d(), "!D");
    assert_format!(Computation::new_not_a(), "!A");
    assert_format!(Computation::new_negative_d(), "-D");
    assert_format!(Computation::new_negative_a(), "-A");
    assert_format!(Computation::new_d_plus1(), "D+1");
    assert_format!(Computation::new_a_plus1(), "A+1");
    assert_format!(Computation::new_d_minus1(), "D-1");
    assert_format!(Computation::new_a_minus1(), "A-1");
    assert_format!(Computation::new_d_plus_a(), "D+A");
    assert_format!(Computation::new_d_minus_a(), "D-A");
    assert_format!(Computation::new_a_minus_d(), "A-D");
    assert_format!(Computation::new_d_and_a(), "D&A");
    assert_format!(Computation::new_d_or_a(), "D|A");
    assert_format!(Computation::new_m(), "M");
    assert_format!(Computation::new_not_m(), "!M");
    assert_format!(Computation::new_negative_m(), "-M");
    assert_format!(Computation::new_m_plus1(), "M+1");
    assert_format!(Computation::new_m_minus1(), "M-1");
    assert_format!(Computation::new_d_plus_m(), "D+M");
    assert_format!(Computation::new_d_minus_m(), "D-M");
    assert_format!(Computation::new_m_minus_d(), "M-D");
    assert_format!(Computation::new_d_and_m(), "D&M");
    assert_format!(Computation::new_d_or_m(), "D|M");
  }

  #[test]
  fn new() {
    assert_eq!(Computation::new("0".as_bytes()), Some(Computation::new_zero()));
    assert_eq!(Computation::new("1".as_bytes()), Some(Computation::new_one()));
    assert_eq!(Computation::new("-1".as_bytes()), Some(Computation::new_negative1()));
    assert_eq!(Computation::new("D".as_bytes()), Some(Computation::new_d()));
    assert_eq!(Computation::new("A".as_bytes()), Some(Computation::new_a()));
    assert_eq!(Computation::new("!D".as_bytes()), Some(Computation::new_not_d()));
    assert_eq!(Computation::new("!A".as_bytes()), Some(Computation::new_not_a()));
    assert_eq!(Computation::new("-D".as_bytes()), Some(Computation::new_negative_d()));
    assert_eq!(Computation::new("-A".as_bytes()), Some(Computation::new_negative_a()));
    assert_eq!(Computation::new("D+1".as_bytes()), Some(Computation::new_d_plus1()));
    assert_eq!(Computation::new("A+1".as_bytes()), Some(Computation::new_a_plus1()));
    assert_eq!(Computation::new("D-1".as_bytes()), Some(Computation::new_d_minus1()));
    assert_eq!(Computation::new("A-1".as_bytes()), Some(Computation::new_a_minus1()));
    assert_eq!(Computation::new("D+A".as_bytes()), Some(Computation::new_d_plus_a()));
    assert_eq!(Computation::new("D-A".as_bytes()), Some(Computation::new_d_minus_a()));
    assert_eq!(Computation::new("A-D".as_bytes()), Some(Computation::new_a_minus_d()));
    assert_eq!(Computation::new("D&A".as_bytes()), Some(Computation::new_d_and_a()));
    assert_eq!(Computation::new("D|A".as_bytes()), Some(Computation::new_d_or_a()));
    assert_eq!(Computation::new("M".as_bytes()), Some(Computation::new_m()));
    assert_eq!(Computation::new("!M".as_bytes()), Some(Computation::new_not_m()));
    assert_eq!(Computation::new("-M".as_bytes()), Some(Computation::new_negative_m()));
    assert_eq!(Computation::new("M+1".as_bytes()), Some(Computation::new_m_plus1()));
    assert_eq!(Computation::new("M-1".as_bytes()), Some(Computation::new_m_minus1()));
    assert_eq!(Computation::new("D+M".as_bytes()), Some(Computation::new_d_plus_m()));
    assert_eq!(Computation::new("D-M".as_bytes()), Some(Computation::new_d_minus_m()));
    assert_eq!(Computation::new("M-D".as_bytes()), Some(Computation::new_m_minus_d()));
    assert_eq!(Computation::new("D&M".as_bytes()), Some(Computation::new_d_and_m()));
    assert_eq!(Computation::new("D|M".as_bytes()), Some(Computation::new_d_or_m()));
  }
}
