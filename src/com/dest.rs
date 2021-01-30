use std::convert::TryFrom;

use crate::utils::buf::Buf;
use crate::utils::buf::Byte;
use crate::utils::parser;

use derive_more::Display;

/// A destination as defined by the HACK assembly reference.
///
/// Can be parsed using [Dest::read_from].
///
/// # impl `Into<u16>`
///
/// The binary representation is 3 bits wide representing the bits
/// `d1`, `d2` and `d3` in an [instruction](crate::com::inst::Inst).
///
/// ## Examples
///
/// ```
/// use has::com::dest::Dest;
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
///
/// # impl `Display`
///
/// ```
/// use has::com::dest::Dest;
///
/// assert_eq!(format!("{}", Dest::Null), "");
/// assert_eq!(format!("{}", Dest::M),    "M");
/// assert_eq!(format!("{}", Dest::D),    "D");
/// assert_eq!(format!("{}", Dest::MD),   "MD");
/// assert_eq!(format!("{}", Dest::A),    "A");
/// assert_eq!(format!("{}", Dest::AM),   "AM");
/// assert_eq!(format!("{}", Dest::AD),   "AD");
/// assert_eq!(format!("{}", Dest::AMD),  "AMD");
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
  /// Constructs an `Err::Unknown` variant.
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
  /// use has::com::dest;
  /// use has::com::dest::Dest;
  ///
  /// let dest = Dest::read_from("".as_bytes());
  /// assert_eq!(dest, Err(dest::Err::Unknown(String::from(""))));
  ///
  /// let dest = Dest::read_from("Foo".as_bytes());
  /// assert_eq!(dest, Err(dest::Err::Unknown(String::from(""))));
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

  /// Whether the destination object is null.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::com::dest::Dest;
  ///
  /// assert!(Dest::Null.is_null());
  /// assert!(!Dest::D.is_null());
  /// ```
  pub fn is_null(&self) -> bool {
    match self {
      Dest::Null => true,
      Dest::M | Dest::D | Dest::MD | Dest::A | Dest::AM | Dest::AD | Dest::AMD => false,
    }
  }
}
