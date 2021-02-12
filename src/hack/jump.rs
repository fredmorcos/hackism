//! Instruction jump for the HACK assembly language.

use crate::parser;
use crate::Buf;
use crate::Byte;
use derive_more::Display;
use std::convert::TryFrom;

/// A jump as defined by the HACK assembly reference.
///
/// The binary representation of a jump is 3 bits wide representing
/// the bits `j1`, `j2` and `j3` in an
/// [instruction](crate::hack::Inst).
///
/// A jump can be parsed from (byte buffers)(Buf) using
/// [Jump::read_from].
///
/// # Examples
///
/// ```
/// use has::hack::Jump;
/// use std::convert::TryFrom;
///
/// let jump = Jump::JMP;
/// assert_eq!(u16::from(jump), 0b111);
/// assert_eq!(Jump::try_from(0b111), Ok(jump));
/// assert_eq!(format!("{}", jump), "JMP");
/// ```
#[derive(Display, Debug, PartialEq, Eq, Clone, Copy)]
pub enum Jump {
  /// No jump.
  #[display(fmt = "")]
  Null,

  /// Jump on greater than.
  #[display(fmt = "JGT")]
  JGT,

  /// Jump on equal.
  #[display(fmt = "JEQ")]
  JEQ,

  /// Jump on greater than or equal.
  #[display(fmt = "JGE")]
  JGE,

  /// Jump on less than.
  #[display(fmt = "JLT")]
  JLT,

  /// Jump on not equal.
  #[display(fmt = "JNE")]
  JNE,

  /// Jump on less than or equal.
  #[display(fmt = "JLE")]
  JLE,

  /// Unconditional jump.
  #[display(fmt = "JMP")]
  JMP,
}

/// Serialize a [Jump] object to [u16].
///
/// # Examples
///
/// ```
/// use has::hack::Jump;
///
/// assert_eq!(u16::from(Jump::Null), 0b000);
/// assert_eq!(u16::from(Jump::JGT),  0b001);
/// assert_eq!(u16::from(Jump::JEQ),  0b010);
/// assert_eq!(u16::from(Jump::JGE),  0b011);
/// assert_eq!(u16::from(Jump::JLT),  0b100);
/// assert_eq!(u16::from(Jump::JNE),  0b101);
/// assert_eq!(u16::from(Jump::JLE),  0b110);
/// assert_eq!(u16::from(Jump::JMP),  0b111);
/// ```
impl From<Jump> for u16 {
  fn from(jump: Jump) -> Self {
    match jump {
      Jump::Null => 0b000,
      Jump::JGT => 0b001,
      Jump::JEQ => 0b010,
      Jump::JGE => 0b011,
      Jump::JLT => 0b100,
      Jump::JNE => 0b101,
      Jump::JLE => 0b110,
      Jump::JMP => 0b111,
    }
  }
}

/// Deserialize a [Jump] object from [u16].
///
/// A value outside of the 3-bit range produces an `Err(())`.
///
/// # Examples
///
/// ```
/// use has::hack::Jump;
/// use std::convert::TryFrom;
///
/// assert_eq!(Jump::try_from(0b000), Ok(Jump::Null));
/// assert_eq!(Jump::try_from(0b001), Ok(Jump::JGT));
/// assert_eq!(Jump::try_from(0b010), Ok(Jump::JEQ));
/// assert_eq!(Jump::try_from(0b011), Ok(Jump::JGE));
/// assert_eq!(Jump::try_from(0b100), Ok(Jump::JLT));
/// assert_eq!(Jump::try_from(0b101), Ok(Jump::JNE));
/// assert_eq!(Jump::try_from(0b110), Ok(Jump::JLE));
/// assert_eq!(Jump::try_from(0b111), Ok(Jump::JMP));
/// ```
impl TryFrom<u16> for Jump {
  type Error = ();

  fn try_from(v: u16) -> Result<Self, Self::Error> {
    match v {
      0b000 => Ok(Jump::Null),
      0b001 => Ok(Jump::JGT),
      0b010 => Ok(Jump::JEQ),
      0b011 => Ok(Jump::JGE),
      0b100 => Ok(Jump::JLT),
      0b101 => Ok(Jump::JNE),
      0b110 => Ok(Jump::JLE),
      0b111 => Ok(Jump::JMP),
      _ => Err(()),
    }
  }
}

/// Parse a [Jump] object from a (byte buffer)(Buf).
///
/// An unrecognized input produces an `Err(())`. Note that
/// [Jump::Null] is inconstructible this way.
///
/// # Examples
///
/// ```
/// use has::hack::Jump;
/// use std::convert::TryFrom;
///
/// assert_eq!(Jump::try_from("JGT".as_bytes()), Ok(Jump::JGT));
/// assert_eq!(Jump::try_from("JEQ".as_bytes()), Ok(Jump::JEQ));
/// assert_eq!(Jump::try_from("JGE".as_bytes()), Ok(Jump::JGE));
/// assert_eq!(Jump::try_from("JLT".as_bytes()), Ok(Jump::JLT));
/// assert_eq!(Jump::try_from("JNE".as_bytes()), Ok(Jump::JNE));
/// assert_eq!(Jump::try_from("JLE".as_bytes()), Ok(Jump::JLE));
/// assert_eq!(Jump::try_from("JMP".as_bytes()), Ok(Jump::JMP));
/// ```
impl TryFrom<Buf<'_>> for Jump {
  type Error = ();

  fn try_from(buf: Buf) -> Result<Self, Self::Error> {
    match buf {
      b"JGT" => Ok(Jump::JGT),
      b"JEQ" => Ok(Jump::JEQ),
      b"JGE" => Ok(Jump::JGE),
      b"JLT" => Ok(Jump::JLT),
      b"JNE" => Ok(Jump::JNE),
      b"JLE" => Ok(Jump::JLE),
      b"JMP" => Ok(Jump::JMP),
      _ => Err(()),
    }
  }
}

#[cfg(test)]
mod tests {
  #[test]
  fn display() {
    use crate::hack::Jump;

    assert_eq!(format!("{}", Jump::Null), "");
    assert_eq!(format!("{}", Jump::JGT), "JGT");
    assert_eq!(format!("{}", Jump::JEQ), "JEQ");
    assert_eq!(format!("{}", Jump::JGE), "JGE");
    assert_eq!(format!("{}", Jump::JLT), "JLT");
    assert_eq!(format!("{}", Jump::JNE), "JNE");
    assert_eq!(format!("{}", Jump::JLE), "JLE");
    assert_eq!(format!("{}", Jump::JMP), "JMP");
  }
}

/// Errors when parsing a jump.
#[derive(Display, Debug, Clone, PartialEq, Eq)]
#[display(fmt = "Jump error: {}")]
pub enum Err {
  /// Unknown jump.
  #[display(fmt = "unknown jump `{}`", _0)]
  Unknown(String),

  /// Converting byte buffers to UTF-8 strings.
  #[display(fmt = "jump `{:?}` is invalid: {}", _0, _1)]
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

impl Jump {
  /// Read a jump object from a buffer.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::hack::Jump;
  /// use has::hack::JumpErr;
  ///
  /// let jump = Jump::read_from("".as_bytes());
  /// assert_eq!(jump, Err(JumpErr::Unknown(String::from(""))));
  ///
  /// let jump = Jump::read_from("Foo".as_bytes());
  /// assert_eq!(jump, Err(JumpErr::Unknown(String::from(""))));
  ///
  /// let expected = (Jump::JGT, "".as_bytes(), 3);
  /// assert_eq!(Jump::read_from("JGT".as_bytes()), Ok(expected));
  ///
  /// let expected = (Jump::JEQ, "".as_bytes(), 3);
  /// assert_eq!(Jump::read_from("JEQ".as_bytes()), Ok(expected));
  ///
  /// let expected = (Jump::JGE, "".as_bytes(), 3);
  /// assert_eq!(Jump::read_from("JGE".as_bytes()), Ok(expected));
  ///
  /// let expected = (Jump::JLT, "".as_bytes(), 3);
  /// assert_eq!(Jump::read_from("JLT".as_bytes()), Ok(expected));
  ///
  /// let expected = (Jump::JNE, "".as_bytes(), 3);
  /// assert_eq!(Jump::read_from("JNE".as_bytes()), Ok(expected));
  ///
  /// let expected = (Jump::JLE, "".as_bytes(), 3);
  /// assert_eq!(Jump::read_from("JLE".as_bytes()), Ok(expected));
  ///
  /// let expected = (Jump::JMP, "".as_bytes(), 3);
  /// assert_eq!(Jump::read_from("JMP".as_bytes()), Ok(expected));
  ///
  ///
  /// let expected = (Jump::JGT, " //".as_bytes(), 3);
  /// assert_eq!(Jump::read_from("JGT //".as_bytes()), Ok(expected));
  ///
  /// let expected = (Jump::JEQ, " //".as_bytes(), 3);
  /// assert_eq!(Jump::read_from("JEQ //".as_bytes()), Ok(expected));
  ///
  /// let expected = (Jump::JGE, " //".as_bytes(), 3);
  /// assert_eq!(Jump::read_from("JGE //".as_bytes()), Ok(expected));
  ///
  /// let expected = (Jump::JLT, " //".as_bytes(), 3);
  /// assert_eq!(Jump::read_from("JLT //".as_bytes()), Ok(expected));
  ///
  /// let expected = (Jump::JNE, " //".as_bytes(), 3);
  /// assert_eq!(Jump::read_from("JNE //".as_bytes()), Ok(expected));
  ///
  /// let expected = (Jump::JLE, " //".as_bytes(), 3);
  /// assert_eq!(Jump::read_from("JLE //".as_bytes()), Ok(expected));
  ///
  /// let expected = (Jump::JMP, " //".as_bytes(), 3);
  /// assert_eq!(Jump::read_from("JMP //".as_bytes()), Ok(expected));
  /// ```
  pub fn read_from(buf: Buf) -> Result<(Self, Buf, usize), Err> {
    let p = |b| b"JGTELNMPQ".contains(&b);
    let (b, rem) = parser::read_while(buf, p);

    match Self::try_from(b) {
      Ok(res) => Ok((res, rem, b.len())),
      Err(_) => Err(Err::unknown(b)),
    }
  }

  /// Whether the [jump](Jump) object is null.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::hack::Jump;
  ///
  /// assert!(Jump::Null.is_null());
  /// assert!(!Jump::JGT.is_null());
  /// ```
  pub fn is_null(&self) -> bool {
    matches!(self, Jump::Null)
  }
}
