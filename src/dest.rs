use std::convert::TryFrom;
use std::fmt;

use crate::utils;
use crate::utils::Buf;

/// A destination as defined by the HACK assembly reference.
///
/// Can be parsed using [Dest::read_from].
///
/// # impl `Into<u16>`
///
/// The binary representation is 3 bits wide representing the bits
/// `d1`, `d2` and `d3` in an [instruction](Inst).
///
/// ## Examples
///
/// ```
/// use has::dest::Dest;
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
/// use has::dest::Dest;
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
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Dest {
  /// No destination.
  Null,
  /// Memory register.
  M,
  /// Data register.
  D,
  /// Memory and Data registers.
  MD,
  /// Address register.
  A,
  /// Address and Memory registers.
  AM,
  /// Address and Data registers.
  AD,
  /// Address, Memory and Data registers.
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

impl fmt::Display for Dest {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Dest::Null => write!(f, ""),
      Dest::M => write!(f, "M"),
      Dest::D => write!(f, "D"),
      Dest::MD => write!(f, "MD"),
      Dest::A => write!(f, "A"),
      Dest::AM => write!(f, "AM"),
      Dest::AD => write!(f, "AD"),
      Dest::AMD => write!(f, "AMD"),
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

impl Dest {
  /// Read a destination object from a buffer.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::dest::Dest;
  ///
  /// assert_eq!(Dest::read_from("".as_bytes()), Err(()));
  /// assert_eq!(Dest::read_from("Foo".as_bytes()), Err(()));
  ///
  /// assert_eq!(Dest::read_from("M".as_bytes()),   Ok((Dest::M,   "".as_bytes(), 1)));
  /// assert_eq!(Dest::read_from("D".as_bytes()),   Ok((Dest::D,   "".as_bytes(), 1)));
  /// assert_eq!(Dest::read_from("MD".as_bytes()),  Ok((Dest::MD,  "".as_bytes(), 2)));
  /// assert_eq!(Dest::read_from("A".as_bytes()),   Ok((Dest::A,   "".as_bytes(), 1)));
  /// assert_eq!(Dest::read_from("AM".as_bytes()),  Ok((Dest::AM,  "".as_bytes(), 2)));
  /// assert_eq!(Dest::read_from("AD".as_bytes()),  Ok((Dest::AD,  "".as_bytes(), 2)));
  /// assert_eq!(Dest::read_from("AMD".as_bytes()), Ok((Dest::AMD, "".as_bytes(), 3)));
  ///
  /// assert_eq!(Dest::read_from("M=".as_bytes()),   Ok((Dest::M,   "=".as_bytes(), 1)));
  /// assert_eq!(Dest::read_from("D=".as_bytes()),   Ok((Dest::D,   "=".as_bytes(), 1)));
  /// assert_eq!(Dest::read_from("MD=".as_bytes()),  Ok((Dest::MD,  "=".as_bytes(), 2)));
  /// assert_eq!(Dest::read_from("A=".as_bytes()),   Ok((Dest::A,   "=".as_bytes(), 1)));
  /// assert_eq!(Dest::read_from("AM=".as_bytes()),  Ok((Dest::AM,  "=".as_bytes(), 2)));
  /// assert_eq!(Dest::read_from("AD=".as_bytes()),  Ok((Dest::AD,  "=".as_bytes(), 2)));
  /// assert_eq!(Dest::read_from("AMD=".as_bytes()), Ok((Dest::AMD, "=".as_bytes(), 3)));
  /// ```
  pub fn read_from(buf: Buf) -> Result<(Self, Buf, usize), ()> {
    let p = |b| b"AMD".contains(&b);
    let (b, rem) = utils::read_while(buf, p);
    let res = Self::try_from(b).map_err(|_| ())?;
    Ok((res, rem, b.len()))
  }

  /// Whether the destination object is null.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::dest::Dest;
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