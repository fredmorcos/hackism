//! HACK jumps.

use std::convert::TryFrom;

use crate::utils::buf::Buf;
use crate::utils::buf::Byte;
use crate::utils::parser;

use derive_more::Display;

/// A jump as defined by the HACK assembly reference.
///
/// Can be parsed using [Jump::read_from].
///
/// # impl `Into<u16>`
///
/// The binary representation is 3 bits wide representing the bits
/// `j1`, `j2` and `j3` in an [instruction](crate::com::inst::Inst).
///
/// ## Examples
///
/// ```
/// use has::com::jump::Jump;
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
///
/// # impl `Display`
///
/// ```
/// use has::com::jump::Jump;
///
/// assert_eq!(format!("{}", Jump::Null), "");
/// assert_eq!(format!("{}", Jump::JGT),  "JGT");
/// assert_eq!(format!("{}", Jump::JEQ),  "JEQ");
/// assert_eq!(format!("{}", Jump::JGE),  "JGE");
/// assert_eq!(format!("{}", Jump::JLT),  "JLT");
/// assert_eq!(format!("{}", Jump::JNE),  "JNE");
/// assert_eq!(format!("{}", Jump::JLE),  "JLE");
/// assert_eq!(format!("{}", Jump::JMP),  "JMP");
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
  /// use has::com::jump;
  /// use has::com::jump::Jump;
  ///
  /// let jump = Jump::read_from("".as_bytes());
  /// assert_eq!(jump, Err(jump::Err::Unknown(String::from(""))));
  ///
  /// let jump = Jump::read_from("Foo".as_bytes());
  /// assert_eq!(jump, Err(jump::Err::Unknown(String::from(""))));
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
  /// use has::com::jump::Jump;
  ///
  /// assert!(Jump::Null.is_null());
  /// assert!(!Jump::JGT.is_null());
  /// ```
  pub fn is_null(&self) -> bool {
    match self {
      Jump::Null => true,
      Jump::JGT
      | Jump::JEQ
      | Jump::JGE
      | Jump::JLT
      | Jump::JNE
      | Jump::JLE
      | Jump::JMP => false,
    }
  }
}
