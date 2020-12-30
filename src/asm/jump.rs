use std::convert::TryFrom;
use std::fmt;

use crate::utils;
use crate::utils::Buf;

/// A jump as defined by the HACK assembly reference.
///
/// Can be parsed using [Jump::read_from].
///
/// # impl `Into<u16>`
///
/// The binary representation is 3 bits wide representing the bits
/// `j1`, `j2` and `j3` in an [instruction](crate::asm::inst::Inst).
///
/// ## Examples
///
/// ```
/// use has::asm::jump::Jump;
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
/// use has::asm::jump::Jump;
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
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Jump {
  /// No jump.
  Null,
  /// Jump on greater than.
  JGT,
  /// Jump on equal.
  JEQ,
  /// Jump on greater than or equal.
  JGE,
  /// Jump on less than.
  JLT,
  /// Jump on not equal.
  JNE,
  /// Jump on less than or equal.
  JLE,
  /// Unconditional jump.
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

impl fmt::Display for Jump {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Jump::Null => write!(f, ""),
      Jump::JGT => write!(f, "JGT"),
      Jump::JEQ => write!(f, "JEQ"),
      Jump::JGE => write!(f, "JGE"),
      Jump::JLT => write!(f, "JLT"),
      Jump::JNE => write!(f, "JNE"),
      Jump::JLE => write!(f, "JLE"),
      Jump::JMP => write!(f, "JMP"),
    }
  }
}

impl Jump {
  /// Read a jump object from a buffer.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::asm::jump::Jump;
  ///
  /// assert_eq!(Jump::read_from("".as_bytes()), Err(()));
  /// assert_eq!(Jump::read_from("Foo".as_bytes()), Err(()));
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
  pub fn read_from(buf: Buf) -> Result<(Self, Buf, usize), ()> {
    let p = |b| b"JGTELNMPQ".contains(&b);
    let (b, rem) = utils::read_while(buf, p);
    let res = Self::try_from(b).map_err(|_| ())?;
    Ok((res, rem, b.len()))
  }

  /// Whether the [jump](Jump) object is null.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::asm::jump::Jump;
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
