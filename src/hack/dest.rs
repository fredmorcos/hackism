//! Instruction destination for the HACK assembly language.

use crate::parser;
use crate::Buf;
use crate::Byte;
use derive_more::Display;
use std::convert::TryFrom;

/// A destination as defined by the HACK assembly reference.
///
/// The binary representation of a destination is 3 bits wide
/// representing the bits `d1`, `d2` and `d3` in an
/// [instruction](crate::hack::Inst).
///
/// A destination can be parsed from (byte buffers)[Buf] using
/// [Dest::read_from].
///
/// # Examples
///
/// ```
/// use has::hack::Dest;
/// use std::convert::TryFrom;
///
/// let dest = Dest::AMD;
/// assert_eq!(u16::from(dest), 0b111);
/// assert_eq!(Dest::try_from(0b111), Ok(dest));
/// assert_eq!(format!("{}", dest), "AMD");
/// ```
#[derive(Display, Debug, PartialEq, Eq, Clone, Copy)]
pub enum Dest {
  /// No destination.
  #[display(fmt = "")]
  Null,

  /// Memory register.
  #[display(fmt = "M")]
  M,

  /// Data register.
  #[display(fmt = "D")]
  D,

  /// Memory and Data registers.
  #[display(fmt = "MD")]
  MD,

  /// Address register.
  #[display(fmt = "A")]
  A,

  /// Address and Memory registers.
  #[display(fmt = "AM")]
  AM,

  /// Address and Data registers.
  #[display(fmt = "AD")]
  AD,

  /// Address, Memory and Data registers.
  #[display(fmt = "AMD")]
  AMD,
}

/// Serialize a [Dest] object to [u16].
///
/// # Examples
///
/// ```
/// use has::hack::Dest;
///
/// assert_eq!(u16::from(Dest::Null), 0b000);
/// assert_eq!(u16::from(Dest::M),    0b001);
/// assert_eq!(u16::from(Dest::D),    0b010);
/// assert_eq!(u16::from(Dest::MD),   0b011);
/// assert_eq!(u16::from(Dest::A),    0b100);
/// assert_eq!(u16::from(Dest::AM),   0b101);
/// assert_eq!(u16::from(Dest::AD),   0b110);
/// assert_eq!(u16::from(Dest::AMD),  0b111);
/// ```
impl From<Dest> for u16 {
  fn from(dest: Dest) -> Self {
    match dest {
      Dest::Null => 0b000,
      Dest::M => 0b001,
      Dest::D => 0b010,
      Dest::MD => 0b011,
      Dest::A => 0b100,
      Dest::AM => 0b101,
      Dest::AD => 0b110,
      Dest::AMD => 0b111,
    }
  }
}

/// Deserialize a [Dest] object from [u16].
///
/// A value outside of the 3-bit range produces an `Err(())`.
///
/// # Examples
///
/// ```
/// use has::hack::Dest;
/// use std::convert::TryFrom;
///
/// assert_eq!(Dest::try_from(0b000), Ok(Dest::Null));
/// assert_eq!(Dest::try_from(0b001), Ok(Dest::M));
/// assert_eq!(Dest::try_from(0b010), Ok(Dest::D));
/// assert_eq!(Dest::try_from(0b011), Ok(Dest::MD));
/// assert_eq!(Dest::try_from(0b100), Ok(Dest::A));
/// assert_eq!(Dest::try_from(0b101), Ok(Dest::AM));
/// assert_eq!(Dest::try_from(0b110), Ok(Dest::AD));
/// assert_eq!(Dest::try_from(0b111), Ok(Dest::AMD));
/// ```
impl TryFrom<u16> for Dest {
  type Error = ();

  fn try_from(v: u16) -> Result<Self, Self::Error> {
    match v {
      0b000 => Ok(Dest::Null),
      0b001 => Ok(Dest::M),
      0b010 => Ok(Dest::D),
      0b011 => Ok(Dest::MD),
      0b100 => Ok(Dest::A),
      0b101 => Ok(Dest::AM),
      0b110 => Ok(Dest::AD),
      0b111 => Ok(Dest::AMD),
      _ => Err(()),
    }
  }
}

/// Parse a [Dest] object from a (byte buffer)(Buf).
///
/// An unrecognized input produces an `Err(())`. Note that
/// [Dest::Null] is inconstructible this way.
///
/// # Examples
///
/// ```
/// use has::hack::Dest;
/// use std::convert::TryFrom;
///
/// assert_eq!(Dest::try_from("M".as_bytes()), Ok(Dest::M));
/// assert_eq!(Dest::try_from("D".as_bytes()), Ok(Dest::D));
/// assert_eq!(Dest::try_from("MD".as_bytes()), Ok(Dest::MD));
/// assert_eq!(Dest::try_from("A".as_bytes()), Ok(Dest::A));
/// assert_eq!(Dest::try_from("AM".as_bytes()), Ok(Dest::AM));
/// assert_eq!(Dest::try_from("AD".as_bytes()), Ok(Dest::AD));
/// assert_eq!(Dest::try_from("AMD".as_bytes()), Ok(Dest::AMD));
/// ```
impl TryFrom<Buf<'_>> for Dest {
  type Error = ();

  fn try_from(buf: Buf) -> Result<Self, Self::Error> {
    match buf {
      b"M" => Ok(Dest::M),
      b"D" => Ok(Dest::D),
      b"MD" => Ok(Dest::MD),
      b"A" => Ok(Dest::A),
      b"AM" => Ok(Dest::AM),
      b"AD" => Ok(Dest::AD),
      b"AMD" => Ok(Dest::AMD),
      _ => Err(()),
    }
  }
}

#[cfg(test)]
mod tests {
  #[test]
  fn display() {
    use crate::hack::Dest;

    assert_eq!(format!("{}", Dest::Null), "");
    assert_eq!(format!("{}", Dest::M), "M");
    assert_eq!(format!("{}", Dest::D), "D");
    assert_eq!(format!("{}", Dest::MD), "MD");
    assert_eq!(format!("{}", Dest::A), "A");
    assert_eq!(format!("{}", Dest::AM), "AM");
    assert_eq!(format!("{}", Dest::AD), "AD");
    assert_eq!(format!("{}", Dest::AMD), "AMD");
  }
}

/// Errors when parsing a destination.
#[derive(Display, Debug, Clone, PartialEq, Eq)]
pub enum Err {
  /// Unknown destination.
  #[display(fmt = "unknown destination `{}`", _0)]
  Unknown(String),

  /// Converting byte buffers to UTF-8 strings.
  #[display(fmt = "destination `{:?}` is invalid: {}", _0, _1)]
  Convert(Vec<Byte>, std::string::FromUtf8Error),
}

impl Err {
  /// Constructs an [Err::Unknown] variant.
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

impl Dest {
  /// Read a destination object from a buffer.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::hack::Dest;
  /// use has::hack::DestErr;
  ///
  /// let dest = Dest::read_from("".as_bytes());
  /// assert_eq!(dest, Err(DestErr::Unknown(String::from(""))));
  ///
  /// let dest = Dest::read_from("Foo".as_bytes());
  /// assert_eq!(dest, Err(DestErr::Unknown(String::from(""))));
  ///
  /// let expected = (Dest::M, "".as_bytes(), 1);
  /// assert_eq!(Dest::read_from("M".as_bytes()), Ok(expected));
  ///
  /// let expected = (Dest::D, "".as_bytes(), 1);
  /// assert_eq!(Dest::read_from("D".as_bytes()), Ok(expected));
  ///
  /// let expected = (Dest::MD, "".as_bytes(), 2);
  /// assert_eq!(Dest::read_from("MD".as_bytes()), Ok(expected));
  ///
  /// let expected = (Dest::A, "".as_bytes(), 1);
  /// assert_eq!(Dest::read_from("A".as_bytes()), Ok(expected));
  ///
  /// let expected = (Dest::AM, "".as_bytes(), 2);
  /// assert_eq!(Dest::read_from("AM".as_bytes()), Ok(expected));
  ///
  /// let expected = (Dest::AD, "".as_bytes(), 2);
  /// assert_eq!(Dest::read_from("AD".as_bytes()), Ok(expected));
  ///
  /// let expected = (Dest::AMD, "".as_bytes(), 3);
  /// assert_eq!(Dest::read_from("AMD".as_bytes()), Ok(expected));
  ///
  ///
  /// let expected = (Dest::M, "=".as_bytes(), 1);
  /// assert_eq!(Dest::read_from("M=".as_bytes()), Ok(expected));
  ///
  /// let expected = (Dest::D, "=".as_bytes(), 1);
  /// assert_eq!(Dest::read_from("D=".as_bytes()), Ok(expected));
  ///
  /// let expected = (Dest::MD, "=".as_bytes(), 2);
  /// assert_eq!(Dest::read_from("MD=".as_bytes()), Ok(expected));
  ///
  /// let expected = (Dest::A, "=".as_bytes(), 1);
  /// assert_eq!(Dest::read_from("A=".as_bytes()), Ok(expected));
  ///
  /// let expected = (Dest::AM, "=".as_bytes(), 2);
  /// assert_eq!(Dest::read_from("AM=".as_bytes()), Ok(expected));
  ///
  /// let expected = (Dest::AD, "=".as_bytes(), 2);
  /// assert_eq!(Dest::read_from("AD=".as_bytes()), Ok(expected));
  ///
  /// let expected = (Dest::AMD, "=".as_bytes(), 3);
  /// assert_eq!(Dest::read_from("AMD=".as_bytes()), Ok(expected));
  /// ```
  pub fn read_from(buf: Buf) -> Result<(Self, Buf, usize), Err> {
    let p = |b| b"AMD".contains(&b);
    let (b, rem) = parser::read_while(buf, p);

    match Self::try_from(b) {
      Ok(res) => Ok((res, rem, b.len())),
      Err(_) => Err(Err::unknown(b)),
    }
  }

  /// Whether the [destination](Dest) object is null.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::hack::Dest;
  ///
  /// assert!(Dest::Null.is_null());
  /// assert!(!Dest::D.is_null());
  /// ```
  pub fn is_null(&self) -> bool {
    matches!(self, Dest::Null)
  }
}
