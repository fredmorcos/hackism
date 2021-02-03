//! Instruction computation for the HACK assembly language.

use crate::parser;
use crate::Buf;
use crate::Byte;
use derive_more::Display;
use std::convert::TryFrom;

/// A computation as defined by the HACK assembly reference.
///
/// The binary representation is 7 bits wide representing the bits
/// `a`, `c1`, `c2`, `c3`, `c4`, `c5` and `c6` in an
/// [instruction](crate::hack::Inst).
///
/// A computation can be parsed from (byte buffers)(Buf) using
/// [Comp::read_from].
///
/// # Examples
///
/// ```
/// use has::hack::Comp;
/// use std::convert::TryFrom;
///
/// let comp = Comp::DOrM;
/// assert_eq!(u16::from(comp), 0b1010101);
/// assert_eq!(Comp::try_from(0b1010101), Ok(comp));
/// assert_eq!(format!("{}", comp), "D|M");
/// ```
#[derive(Display, Debug, PartialEq, Eq, Clone, Copy)]
pub enum Comp {
  /// Integer literal 0.
  #[display(fmt = "0")]
  Zero,

  /// Integer literal 1.
  #[display(fmt = "1")]
  One,

  /// Integer literal -1 (negative one).
  #[display(fmt = "-1")]
  Neg1,

  /// Data register.
  #[display(fmt = "D")]
  D,

  /// Address register.
  #[display(fmt = "A")]
  A,

  /// Bitwise inverse of the Data register.
  #[display(fmt = "!D")]
  NotD,

  /// Bitwise inverse of the Address register.
  #[display(fmt = "!A")]
  NotA,

  /// Negated value of the Data register.
  #[display(fmt = "-D")]
  NegD,

  /// Negated value of the Address register.
  #[display(fmt = "-A")]
  NegA,

  /// Data register value + 1.
  #[display(fmt = "D+1")]
  DPlus1,

  /// Address register value + 1.
  #[display(fmt = "A+1")]
  APlus1,

  /// Data register value - 1.
  #[display(fmt = "D-1")]
  DMinus1,

  /// Address register value - 1.
  #[display(fmt = "A-1")]
  AMinus1,

  /// Data register value + the Address register value.
  #[display(fmt = "D+A")]
  DPlusA,

  /// Data register value - the Address register value.
  #[display(fmt = "D-A")]
  DMinusA,

  /// Address register value - the Data register value.
  #[display(fmt = "A-D")]
  AMinusD,

  /// Bitwise And of the Data and Address registers.
  #[display(fmt = "D&A")]
  DAndA,

  /// Bitwise Or of the Data and Address registers.
  #[display(fmt = "D|A")]
  DOrA,

  /// Memory register.
  #[display(fmt = "M")]
  M,

  /// Bitwise inverse of the Memory register.
  #[display(fmt = "!M")]
  NotM,

  /// Negated value of the Memory register.
  #[display(fmt = "-M")]
  NegM,

  /// Memory register value + 1.
  #[display(fmt = "M+1")]
  MPlus1,

  /// Memory register value - 1.
  #[display(fmt = "M-1")]
  MMinus1,

  /// Data register value + the Memory register value.
  #[display(fmt = "D+M")]
  DPlusM,

  /// Data register value - the Memory register value.
  #[display(fmt = "D-M")]
  DMinusM,

  /// Memory register value + the Data register value.
  #[display(fmt = "M-D")]
  MMinusD,

  /// Bitwise And of the Data and Memory registers.
  #[display(fmt = "D&M")]
  DAndM,

  /// Bitwise Or of the Data and Memory registers.
  #[display(fmt = "D|M")]
  DOrM,
}

/// Serialize a [Comp] object to [u16].
///
/// # Examples
///
/// ```
/// use has::hack::Comp;
///
/// assert_eq!(u16::from(Comp::Zero),    0b0101010);
/// assert_eq!(u16::from(Comp::One),     0b0111111);
/// assert_eq!(u16::from(Comp::Neg1),    0b0111010);
/// assert_eq!(u16::from(Comp::D),       0b0001100);
/// assert_eq!(u16::from(Comp::A),       0b0110000);
/// assert_eq!(u16::from(Comp::NotD),    0b0001101);
/// assert_eq!(u16::from(Comp::NotA),    0b0110001);
/// assert_eq!(u16::from(Comp::NegD),    0b0001111);
/// assert_eq!(u16::from(Comp::NegA),    0b0110011);
/// assert_eq!(u16::from(Comp::DPlus1),  0b0011111);
/// assert_eq!(u16::from(Comp::APlus1),  0b0110111);
/// assert_eq!(u16::from(Comp::DMinus1), 0b0001110);
/// assert_eq!(u16::from(Comp::AMinus1), 0b0110010);
/// assert_eq!(u16::from(Comp::DPlusA),  0b0000010);
/// assert_eq!(u16::from(Comp::DMinusA), 0b0010011);
/// assert_eq!(u16::from(Comp::AMinusD), 0b0000111);
/// assert_eq!(u16::from(Comp::DAndA),   0b0000000);
/// assert_eq!(u16::from(Comp::DOrA),    0b0010101);
/// assert_eq!(u16::from(Comp::M),       0b1110000);
/// assert_eq!(u16::from(Comp::NotM),    0b1110001);
/// assert_eq!(u16::from(Comp::NegM),    0b1110011);
/// assert_eq!(u16::from(Comp::MPlus1),  0b1110111);
/// assert_eq!(u16::from(Comp::MMinus1), 0b1110010);
/// assert_eq!(u16::from(Comp::DPlusM),  0b1000010);
/// assert_eq!(u16::from(Comp::DMinusM), 0b1010011);
/// assert_eq!(u16::from(Comp::MMinusD), 0b1000111);
/// assert_eq!(u16::from(Comp::DAndM),   0b1000000);
/// assert_eq!(u16::from(Comp::DOrM),    0b1010101);
impl From<Comp> for u16 {
  fn from(comp: Comp) -> Self {
    match comp {
      Comp::Zero => 0b0101010,
      Comp::One => 0b0111111,
      Comp::Neg1 => 0b0111010,
      Comp::D => 0b0001100,
      Comp::A => 0b0110000,
      Comp::NotD => 0b0001101,
      Comp::NotA => 0b0110001,
      Comp::NegD => 0b0001111,
      Comp::NegA => 0b0110011,
      Comp::DPlus1 => 0b0011111,
      Comp::APlus1 => 0b0110111,
      Comp::DMinus1 => 0b0001110,
      Comp::AMinus1 => 0b0110010,
      Comp::DPlusA => 0b0000010,
      Comp::DMinusA => 0b0010011,
      Comp::AMinusD => 0b0000111,
      Comp::DAndA => 0b0000000,
      Comp::DOrA => 0b0010101,
      Comp::M => 0b1110000,
      Comp::NotM => 0b1110001,
      Comp::NegM => 0b1110011,
      Comp::MPlus1 => 0b1110111,
      Comp::MMinus1 => 0b1110010,
      Comp::DPlusM => 0b1000010,
      Comp::DMinusM => 0b1010011,
      Comp::MMinusD => 0b1000111,
      Comp::DAndM => 0b1000000,
      Comp::DOrM => 0b1010101,
    }
  }
}

/// Deserialize a [Comp] object from [u16].
///
/// A value outside of the 7-bit range produces an `Err(())`.
///
/// # Examples
///
/// ```
/// use has::hack::Comp;
/// use std::convert::TryFrom;
///
/// assert_eq!(Comp::try_from(0b0101010), Ok(Comp::Zero));
/// assert_eq!(Comp::try_from(0b0111111), Ok(Comp::One));
/// assert_eq!(Comp::try_from(0b0111010), Ok(Comp::Neg1));
/// assert_eq!(Comp::try_from(0b0001100), Ok(Comp::D));
/// assert_eq!(Comp::try_from(0b0110000), Ok(Comp::A));
/// assert_eq!(Comp::try_from(0b0001101), Ok(Comp::NotD));
/// assert_eq!(Comp::try_from(0b0110001), Ok(Comp::NotA));
/// assert_eq!(Comp::try_from(0b0001111), Ok(Comp::NegD));
/// assert_eq!(Comp::try_from(0b0110011), Ok(Comp::NegA));
/// assert_eq!(Comp::try_from(0b0011111), Ok(Comp::DPlus1));
/// assert_eq!(Comp::try_from(0b0110111), Ok(Comp::APlus1));
/// assert_eq!(Comp::try_from(0b0001110), Ok(Comp::DMinus1));
/// assert_eq!(Comp::try_from(0b0110010), Ok(Comp::AMinus1));
/// assert_eq!(Comp::try_from(0b0000010), Ok(Comp::DPlusA));
/// assert_eq!(Comp::try_from(0b0010011), Ok(Comp::DMinusA));
/// assert_eq!(Comp::try_from(0b0000111), Ok(Comp::AMinusD));
/// assert_eq!(Comp::try_from(0b0000000), Ok(Comp::DAndA));
/// assert_eq!(Comp::try_from(0b0010101), Ok(Comp::DOrA));
/// assert_eq!(Comp::try_from(0b1110000), Ok(Comp::M));
/// assert_eq!(Comp::try_from(0b1110001), Ok(Comp::NotM));
/// assert_eq!(Comp::try_from(0b1110011), Ok(Comp::NegM));
/// assert_eq!(Comp::try_from(0b1110111), Ok(Comp::MPlus1));
/// assert_eq!(Comp::try_from(0b1110010), Ok(Comp::MMinus1));
/// assert_eq!(Comp::try_from(0b1000010), Ok(Comp::DPlusM));
/// assert_eq!(Comp::try_from(0b1010011), Ok(Comp::DMinusM));
/// assert_eq!(Comp::try_from(0b1000111), Ok(Comp::MMinusD));
/// assert_eq!(Comp::try_from(0b1000000), Ok(Comp::DAndM));
/// assert_eq!(Comp::try_from(0b1010101), Ok(Comp::DOrM));
impl TryFrom<u16> for Comp {
  type Error = ();

  fn try_from(v: u16) -> Result<Self, Self::Error> {
    match v {
      0b0101010 => Ok(Comp::Zero),
      0b0111111 => Ok(Comp::One),
      0b0111010 => Ok(Comp::Neg1),
      0b0001100 => Ok(Comp::D),
      0b0110000 => Ok(Comp::A),
      0b0001101 => Ok(Comp::NotD),
      0b0110001 => Ok(Comp::NotA),
      0b0001111 => Ok(Comp::NegD),
      0b0110011 => Ok(Comp::NegA),
      0b0011111 => Ok(Comp::DPlus1),
      0b0110111 => Ok(Comp::APlus1),
      0b0001110 => Ok(Comp::DMinus1),
      0b0110010 => Ok(Comp::AMinus1),
      0b0000010 => Ok(Comp::DPlusA),
      0b0010011 => Ok(Comp::DMinusA),
      0b0000111 => Ok(Comp::AMinusD),
      0b0000000 => Ok(Comp::DAndA),
      0b0010101 => Ok(Comp::DOrA),
      0b1110000 => Ok(Comp::M),
      0b1110001 => Ok(Comp::NotM),
      0b1110011 => Ok(Comp::NegM),
      0b1110111 => Ok(Comp::MPlus1),
      0b1110010 => Ok(Comp::MMinus1),
      0b1000010 => Ok(Comp::DPlusM),
      0b1010011 => Ok(Comp::DMinusM),
      0b1000111 => Ok(Comp::MMinusD),
      0b1000000 => Ok(Comp::DAndM),
      0b1010101 => Ok(Comp::DOrM),
      _ => Err(()),
    }
  }
}

/// Parse a [Comp] object from a (byte buffer)(Buf).
///
/// An unrecognized input produces an `Err(())`.
///
/// # Examples
///
/// ```
/// use has::hack::Comp;
/// use std::convert::TryFrom;
///
/// assert_eq!(Comp::try_from("0".as_bytes()),   Ok(Comp::Zero));
/// assert_eq!(Comp::try_from("1".as_bytes()),   Ok(Comp::One));
/// assert_eq!(Comp::try_from("-1".as_bytes()),  Ok(Comp::Neg1));
/// assert_eq!(Comp::try_from("D".as_bytes()),   Ok(Comp::D));
/// assert_eq!(Comp::try_from("A".as_bytes()),   Ok(Comp::A));
/// assert_eq!(Comp::try_from("!D".as_bytes()),  Ok(Comp::NotD));
/// assert_eq!(Comp::try_from("!A".as_bytes()),  Ok(Comp::NotA));
/// assert_eq!(Comp::try_from("-D".as_bytes()),  Ok(Comp::NegD));
/// assert_eq!(Comp::try_from("-A".as_bytes()),  Ok(Comp::NegA));
/// assert_eq!(Comp::try_from("D+1".as_bytes()), Ok(Comp::DPlus1));
/// assert_eq!(Comp::try_from("A+1".as_bytes()), Ok(Comp::APlus1));
/// assert_eq!(Comp::try_from("D-1".as_bytes()), Ok(Comp::DMinus1));
/// assert_eq!(Comp::try_from("A-1".as_bytes()), Ok(Comp::AMinus1));
/// assert_eq!(Comp::try_from("D+A".as_bytes()), Ok(Comp::DPlusA));
/// assert_eq!(Comp::try_from("D-A".as_bytes()), Ok(Comp::DMinusA));
/// assert_eq!(Comp::try_from("A-D".as_bytes()), Ok(Comp::AMinusD));
/// assert_eq!(Comp::try_from("D&A".as_bytes()), Ok(Comp::DAndA));
/// assert_eq!(Comp::try_from("D|A".as_bytes()), Ok(Comp::DOrA));
/// assert_eq!(Comp::try_from("M".as_bytes()),   Ok(Comp::M));
/// assert_eq!(Comp::try_from("!M".as_bytes()),  Ok(Comp::NotM));
/// assert_eq!(Comp::try_from("-M".as_bytes()),  Ok(Comp::NegM));
/// assert_eq!(Comp::try_from("M+1".as_bytes()), Ok(Comp::MPlus1));
/// assert_eq!(Comp::try_from("M-1".as_bytes()), Ok(Comp::MMinus1));
/// assert_eq!(Comp::try_from("D+M".as_bytes()), Ok(Comp::DPlusM));
/// assert_eq!(Comp::try_from("D-M".as_bytes()), Ok(Comp::DMinusM));
/// assert_eq!(Comp::try_from("M-D".as_bytes()), Ok(Comp::MMinusD));
/// assert_eq!(Comp::try_from("D&M".as_bytes()), Ok(Comp::DAndM));
/// assert_eq!(Comp::try_from("D|M".as_bytes()), Ok(Comp::DOrM));
/// ```
impl TryFrom<Buf<'_>> for Comp {
  type Error = ();

  fn try_from(buf: Buf) -> Result<Self, Self::Error> {
    match buf {
      b"0" => Ok(Comp::Zero),
      b"1" => Ok(Comp::One),
      b"-1" => Ok(Comp::Neg1),
      b"D" => Ok(Comp::D),
      b"A" => Ok(Comp::A),
      b"!D" => Ok(Comp::NotD),
      b"!A" => Ok(Comp::NotA),
      b"-D" => Ok(Comp::NegD),
      b"-A" => Ok(Comp::NegA),
      b"D+1" => Ok(Comp::DPlus1),
      b"A+1" => Ok(Comp::APlus1),
      b"D-1" => Ok(Comp::DMinus1),
      b"A-1" => Ok(Comp::AMinus1),
      b"D+A" => Ok(Comp::DPlusA),
      b"D-A" => Ok(Comp::DMinusA),
      b"A-D" => Ok(Comp::AMinusD),
      b"D&A" => Ok(Comp::DAndA),
      b"D|A" => Ok(Comp::DOrA),
      b"M" => Ok(Comp::M),
      b"!M" => Ok(Comp::NotM),
      b"-M" => Ok(Comp::NegM),
      b"M+1" => Ok(Comp::MPlus1),
      b"M-1" => Ok(Comp::MMinus1),
      b"D+M" => Ok(Comp::DPlusM),
      b"D-M" => Ok(Comp::DMinusM),
      b"M-D" => Ok(Comp::MMinusD),
      b"D&M" => Ok(Comp::DAndM),
      b"D|M" => Ok(Comp::DOrM),
      _ => Err(()),
    }
  }
}

#[cfg(test)]
mod tests {
  #[test]
  fn display() {
    use crate::hack::Comp;

    assert_eq!(format!("{}", Comp::Zero), "0");
    assert_eq!(format!("{}", Comp::One), "1");
    assert_eq!(format!("{}", Comp::Neg1), "-1");
    assert_eq!(format!("{}", Comp::D), "D");
    assert_eq!(format!("{}", Comp::A), "A");
    assert_eq!(format!("{}", Comp::NotD), "!D");
    assert_eq!(format!("{}", Comp::NotA), "!A");
    assert_eq!(format!("{}", Comp::NegD), "-D");
    assert_eq!(format!("{}", Comp::NegA), "-A");
    assert_eq!(format!("{}", Comp::DPlus1), "D+1");
    assert_eq!(format!("{}", Comp::APlus1), "A+1");
    assert_eq!(format!("{}", Comp::DMinus1), "D-1");
    assert_eq!(format!("{}", Comp::AMinus1), "A-1");
    assert_eq!(format!("{}", Comp::DPlusA), "D+A");
    assert_eq!(format!("{}", Comp::DMinusA), "D-A");
    assert_eq!(format!("{}", Comp::AMinusD), "A-D");
    assert_eq!(format!("{}", Comp::DAndA), "D&A");
    assert_eq!(format!("{}", Comp::DOrA), "D|A");
    assert_eq!(format!("{}", Comp::M), "M");
    assert_eq!(format!("{}", Comp::NotM), "!M");
    assert_eq!(format!("{}", Comp::NegM), "-M");
    assert_eq!(format!("{}", Comp::MPlus1), "M+1");
    assert_eq!(format!("{}", Comp::MMinus1), "M-1");
    assert_eq!(format!("{}", Comp::DPlusM), "D+M");
    assert_eq!(format!("{}", Comp::DMinusM), "D-M");
    assert_eq!(format!("{}", Comp::MMinusD), "M-D");
    assert_eq!(format!("{}", Comp::DAndM), "D&M");
    assert_eq!(format!("{}", Comp::DOrM), "D|M");
  }
}

/// Errors when parsing a computation.
#[derive(Display, Debug, Clone, PartialEq, Eq)]
#[display(fmt = "Computation error: {}")]
pub enum Err {
  /// Unknown computation.
  #[display(fmt = "Unknown computation `{}`", _0)]
  Unknown(String),

  /// Converting byte buffers to UTF-8 strings.
  #[display(fmt = "computation `{:?}` is invalid: {}", _0, _1)]
  Convert(Vec<Byte>, std::string::FromUtf8Error),
}

impl Err {
  /// Constructs an `Err::Unknown` variant.
  ///
  /// Note that if `buf` is not valid UTF-8 then an [Err::Convert]
  /// will be return instead.
  pub fn unknown(buf: Buf) -> Self {
    match String::from_utf8(Vec::from(buf)) {
      Ok(txt) => Err::Unknown(txt),
      Err(e) => Err::Convert(Vec::from(buf), e),
    }
  }
}

impl Comp {
  /// Read a computation object from a buffer.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::hack::Comp;
  /// use has::hack::CompErr;
  ///
  /// let comp = Comp::read_from("".as_bytes());
  /// assert_eq!(comp, Err(CompErr::Unknown(String::from(""))));
  ///
  /// let comp = Comp::read_from("Foo".as_bytes());
  /// assert_eq!(comp, Err(CompErr::Unknown(String::from(""))));
  ///
  /// let expected = (Comp::Zero, "".as_bytes(), 1);
  /// assert_eq!(Comp::read_from("0".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::One, "".as_bytes(), 1);
  /// assert_eq!(Comp::read_from("1".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::Neg1, "".as_bytes(), 2);
  /// assert_eq!(Comp::read_from("-1".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::D, "".as_bytes(), 1);
  /// assert_eq!(Comp::read_from("D".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::A, "".as_bytes(), 1);
  /// assert_eq!(Comp::read_from("A".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::NotD, "".as_bytes(), 2);
  /// assert_eq!(Comp::read_from("!D".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::NotA, "".as_bytes(), 2);
  /// assert_eq!(Comp::read_from("!A".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::NegD, "".as_bytes(), 2);
  /// assert_eq!(Comp::read_from("-D".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::NegA, "".as_bytes(), 2);
  /// assert_eq!(Comp::read_from("-A".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DPlus1, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D+1".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::APlus1, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("A+1".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DMinus1, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D-1".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::AMinus1, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("A-1".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DPlusA, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D+A".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DMinusA, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D-A".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::AMinusD, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("A-D".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DAndA, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D&A".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DOrA, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D|A".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::M, "".as_bytes(), 1);
  /// assert_eq!(Comp::read_from("M".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::NotM, "".as_bytes(), 2);
  /// assert_eq!(Comp::read_from("!M".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::NegM, "".as_bytes(), 2);
  /// assert_eq!(Comp::read_from("-M".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::MPlus1, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("M+1".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::MMinus1, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("M-1".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DPlusM, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D+M".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DMinusM, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D-M".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::MMinusD, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("M-D".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DAndM, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D&M".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DOrM, "".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D|M".as_bytes()), Ok(expected));
  ///
  ///
  /// let expected = (Comp::Zero, ";".as_bytes(), 1);
  /// assert_eq!(Comp::read_from("0;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::One, ";".as_bytes(), 1);
  /// assert_eq!(Comp::read_from("1;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::Neg1, ";".as_bytes(), 2);
  /// assert_eq!(Comp::read_from("-1;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::D, ";".as_bytes(), 1);
  /// assert_eq!(Comp::read_from("D;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::A, ";".as_bytes(), 1);
  /// assert_eq!(Comp::read_from("A;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::NotD, ";".as_bytes(), 2);
  /// assert_eq!(Comp::read_from("!D;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::NotA, ";".as_bytes(), 2);
  /// assert_eq!(Comp::read_from("!A;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::NegD, ";".as_bytes(), 2);
  /// assert_eq!(Comp::read_from("-D;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::NegA, ";".as_bytes(), 2);
  /// assert_eq!(Comp::read_from("-A;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DPlus1, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D+1;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::APlus1, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("A+1;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DMinus1, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D-1;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::AMinus1, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("A-1;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DPlusA, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D+A;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DMinusA, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D-A;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::AMinusD, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("A-D;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DAndA, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D&A;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DOrA, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D|A;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::M, ";".as_bytes(), 1);
  /// assert_eq!(Comp::read_from("M;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::NotM, ";".as_bytes(), 2);
  /// assert_eq!(Comp::read_from("!M;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::NegM, ";".as_bytes(), 2);
  /// assert_eq!(Comp::read_from("-M;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::MPlus1, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("M+1;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::MMinus1, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("M-1;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DPlusM, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D+M;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DMinusM, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D-M;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::MMinusD, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("M-D;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DAndM, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D&M;".as_bytes()), Ok(expected));
  ///
  /// let expected = (Comp::DOrM, ";".as_bytes(), 3);
  /// assert_eq!(Comp::read_from("D|M;".as_bytes()), Ok(expected));
  /// ```
  pub fn read_from(buf: Buf) -> Result<(Self, Buf, usize), Err> {
    let p = |b| b"01AMD+-!&|".contains(&b);
    let (b, rem) = parser::read_while(buf, p);

    match Self::try_from(b) {
      Ok(res) => Ok((res, rem, b.len())),
      Err(_) => Err(Err::unknown(b)),
    }
  }
}
