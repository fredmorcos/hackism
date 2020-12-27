use std::convert::TryFrom;
use std::fmt;

use crate::utils;
use crate::utils::Buf;

/// A computation as defined by the HACK assembly reference.
///
/// Can be created using [Comp::read_from].
///
/// # impl `Into<u16>`
///
/// The binary representation is 7 bits wide representing the bits
/// `a`, `c1`, `c2`, `c3`, `c4`, `c5` and `c6` in an
/// [instruction](Inst).
///
/// ## Examples
///
/// ```
/// use has::comp::Comp;
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
/// ```
///
/// # impl `Display`
///
/// ```
/// use has::comp::Comp;
///
/// assert_eq!(format!("{}", Comp::Zero),    "0");
/// assert_eq!(format!("{}", Comp::One),     "1");
/// assert_eq!(format!("{}", Comp::Neg1),    "-1");
/// assert_eq!(format!("{}", Comp::D),       "D");
/// assert_eq!(format!("{}", Comp::A),       "A");
/// assert_eq!(format!("{}", Comp::NotD),    "!D");
/// assert_eq!(format!("{}", Comp::NotA),    "!A");
/// assert_eq!(format!("{}", Comp::NegD),    "-D");
/// assert_eq!(format!("{}", Comp::NegA),    "-A");
/// assert_eq!(format!("{}", Comp::DPlus1),  "D+1");
/// assert_eq!(format!("{}", Comp::APlus1),  "A+1");
/// assert_eq!(format!("{}", Comp::DMinus1), "D-1");
/// assert_eq!(format!("{}", Comp::AMinus1), "A-1");
/// assert_eq!(format!("{}", Comp::DPlusA),  "D+A");
/// assert_eq!(format!("{}", Comp::DMinusA), "D-A");
/// assert_eq!(format!("{}", Comp::AMinusD), "A-D");
/// assert_eq!(format!("{}", Comp::DAndA),   "D&A");
/// assert_eq!(format!("{}", Comp::DOrA),    "D|A");
/// assert_eq!(format!("{}", Comp::M),       "M");
/// assert_eq!(format!("{}", Comp::NotM),    "!M");
/// assert_eq!(format!("{}", Comp::NegM),    "-M");
/// assert_eq!(format!("{}", Comp::MPlus1),  "M+1");
/// assert_eq!(format!("{}", Comp::MMinus1), "M-1");
/// assert_eq!(format!("{}", Comp::DPlusM),  "D+M");
/// assert_eq!(format!("{}", Comp::DMinusM), "D-M");
/// assert_eq!(format!("{}", Comp::MMinusD), "M-D");
/// assert_eq!(format!("{}", Comp::DAndM),   "D&M");
/// assert_eq!(format!("{}", Comp::DOrM),    "D|M");
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Comp {
  /// Integer literal 0.
  Zero,
  /// Integer literal 1.
  One,
  /// Integer literal -1 (negative one).
  Neg1,
  /// Data register.
  D,
  /// Address register.
  A,
  /// Bitwise inverse of the Data register.
  NotD,
  /// Bitwise inverse of the Address register.
  NotA,
  /// Negated value of the Data register.
  NegD,
  /// Negated value of the Address register.
  NegA,
  /// Data register value + 1.
  DPlus1,
  /// Address register value + 1.
  APlus1,
  /// Data register value - 1.
  DMinus1,
  /// Address register value - 1.
  AMinus1,
  /// Data register value + the Address register value.
  DPlusA,
  /// Data register value - the Address register value.
  DMinusA,
  /// Address register value - the Data register value.
  AMinusD,
  /// Bitwise And of the Data and Address registers.
  DAndA,
  /// Bitwise Or of the Data and Address registers.
  DOrA,
  /// Memory register.
  M,
  /// Bitwise inverse of the Memory register.
  NotM,
  /// Negated value of the Memory register.
  NegM,
  /// Memory register value + 1.
  MPlus1,
  /// Memory register value - 1.
  MMinus1,
  /// Data register value + the Memory register value.
  DPlusM,
  /// Data register value - the Memory register value.
  DMinusM,
  /// Memory register value + the Data register value.
  MMinusD,
  /// Bitwise And of the Data and Memory registers.
  DAndM,
  /// Bitwise Or of the Data and Memory registers.
  DOrM,
}

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

impl fmt::Display for Comp {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Comp::Zero => write!(f, "0"),
      Comp::One => write!(f, "1"),
      Comp::Neg1 => write!(f, "-1"),
      Comp::D => write!(f, "D"),
      Comp::A => write!(f, "A"),
      Comp::NotD => write!(f, "!D"),
      Comp::NotA => write!(f, "!A"),
      Comp::NegD => write!(f, "-D"),
      Comp::NegA => write!(f, "-A"),
      Comp::DPlus1 => write!(f, "D+1"),
      Comp::APlus1 => write!(f, "A+1"),
      Comp::DMinus1 => write!(f, "D-1"),
      Comp::AMinus1 => write!(f, "A-1"),
      Comp::DPlusA => write!(f, "D+A"),
      Comp::DMinusA => write!(f, "D-A"),
      Comp::AMinusD => write!(f, "A-D"),
      Comp::DAndA => write!(f, "D&A"),
      Comp::DOrA => write!(f, "D|A"),
      Comp::M => write!(f, "M"),
      Comp::NotM => write!(f, "!M"),
      Comp::NegM => write!(f, "-M"),
      Comp::MPlus1 => write!(f, "M+1"),
      Comp::MMinus1 => write!(f, "M-1"),
      Comp::DPlusM => write!(f, "D+M"),
      Comp::DMinusM => write!(f, "D-M"),
      Comp::MMinusD => write!(f, "M-D"),
      Comp::DAndM => write!(f, "D&M"),
      Comp::DOrM => write!(f, "D|M"),
    }
  }
}

impl Comp {
  /// Read a computation object from a buffer.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::comp::Comp;
  ///
  /// assert_eq!(Comp::read_from("".as_bytes()), Err(()));
  /// assert_eq!(Comp::read_from("Foo".as_bytes()), Err(()));
  ///
  /// assert_eq!(Comp::read_from("0".as_bytes()),   Ok((Comp::Zero,    "".as_bytes(), 1)));
  /// assert_eq!(Comp::read_from("1".as_bytes()),   Ok((Comp::One,     "".as_bytes(), 1)));
  /// assert_eq!(Comp::read_from("-1".as_bytes()),  Ok((Comp::Neg1,    "".as_bytes(), 2)));
  /// assert_eq!(Comp::read_from("D".as_bytes()),   Ok((Comp::D,       "".as_bytes(), 1)));
  /// assert_eq!(Comp::read_from("A".as_bytes()),   Ok((Comp::A,       "".as_bytes(), 1)));
  /// assert_eq!(Comp::read_from("!D".as_bytes()),  Ok((Comp::NotD,    "".as_bytes(), 2)));
  /// assert_eq!(Comp::read_from("!A".as_bytes()),  Ok((Comp::NotA,    "".as_bytes(), 2)));
  /// assert_eq!(Comp::read_from("-D".as_bytes()),  Ok((Comp::NegD,    "".as_bytes(), 2)));
  /// assert_eq!(Comp::read_from("-A".as_bytes()),  Ok((Comp::NegA,    "".as_bytes(), 2)));
  /// assert_eq!(Comp::read_from("D+1".as_bytes()), Ok((Comp::DPlus1,  "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("A+1".as_bytes()), Ok((Comp::APlus1,  "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D-1".as_bytes()), Ok((Comp::DMinus1, "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("A-1".as_bytes()), Ok((Comp::AMinus1, "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D+A".as_bytes()), Ok((Comp::DPlusA,  "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D-A".as_bytes()), Ok((Comp::DMinusA, "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("A-D".as_bytes()), Ok((Comp::AMinusD, "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D&A".as_bytes()), Ok((Comp::DAndA,   "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D|A".as_bytes()), Ok((Comp::DOrA,    "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("M".as_bytes()),   Ok((Comp::M,       "".as_bytes(), 1)));
  /// assert_eq!(Comp::read_from("!M".as_bytes()),  Ok((Comp::NotM,    "".as_bytes(), 2)));
  /// assert_eq!(Comp::read_from("-M".as_bytes()),  Ok((Comp::NegM,    "".as_bytes(), 2)));
  /// assert_eq!(Comp::read_from("M+1".as_bytes()), Ok((Comp::MPlus1,  "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("M-1".as_bytes()), Ok((Comp::MMinus1, "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D+M".as_bytes()), Ok((Comp::DPlusM,  "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D-M".as_bytes()), Ok((Comp::DMinusM, "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("M-D".as_bytes()), Ok((Comp::MMinusD, "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D&M".as_bytes()), Ok((Comp::DAndM,   "".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D|M".as_bytes()), Ok((Comp::DOrM,    "".as_bytes(), 3)));
  ///
  /// assert_eq!(Comp::read_from("0;".as_bytes()),   Ok((Comp::Zero,    ";".as_bytes(), 1)));
  /// assert_eq!(Comp::read_from("1;".as_bytes()),   Ok((Comp::One,     ";".as_bytes(), 1)));
  /// assert_eq!(Comp::read_from("-1;".as_bytes()),  Ok((Comp::Neg1,    ";".as_bytes(), 2)));
  /// assert_eq!(Comp::read_from("D;".as_bytes()),   Ok((Comp::D,       ";".as_bytes(), 1)));
  /// assert_eq!(Comp::read_from("A;".as_bytes()),   Ok((Comp::A,       ";".as_bytes(), 1)));
  /// assert_eq!(Comp::read_from("!D;".as_bytes()),  Ok((Comp::NotD,    ";".as_bytes(), 2)));
  /// assert_eq!(Comp::read_from("!A;".as_bytes()),  Ok((Comp::NotA,    ";".as_bytes(), 2)));
  /// assert_eq!(Comp::read_from("-D;".as_bytes()),  Ok((Comp::NegD,    ";".as_bytes(), 2)));
  /// assert_eq!(Comp::read_from("-A;".as_bytes()),  Ok((Comp::NegA,    ";".as_bytes(), 2)));
  /// assert_eq!(Comp::read_from("D+1;".as_bytes()), Ok((Comp::DPlus1,  ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("A+1;".as_bytes()), Ok((Comp::APlus1,  ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D-1;".as_bytes()), Ok((Comp::DMinus1, ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("A-1;".as_bytes()), Ok((Comp::AMinus1, ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D+A;".as_bytes()), Ok((Comp::DPlusA,  ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D-A;".as_bytes()), Ok((Comp::DMinusA, ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("A-D;".as_bytes()), Ok((Comp::AMinusD, ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D&A;".as_bytes()), Ok((Comp::DAndA,   ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D|A;".as_bytes()), Ok((Comp::DOrA,    ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("M;".as_bytes()),   Ok((Comp::M,       ";".as_bytes(), 1)));
  /// assert_eq!(Comp::read_from("!M;".as_bytes()),  Ok((Comp::NotM,    ";".as_bytes(), 2)));
  /// assert_eq!(Comp::read_from("-M;".as_bytes()),  Ok((Comp::NegM,    ";".as_bytes(), 2)));
  /// assert_eq!(Comp::read_from("M+1;".as_bytes()), Ok((Comp::MPlus1,  ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("M-1;".as_bytes()), Ok((Comp::MMinus1, ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D+M;".as_bytes()), Ok((Comp::DPlusM,  ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D-M;".as_bytes()), Ok((Comp::DMinusM, ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("M-D;".as_bytes()), Ok((Comp::MMinusD, ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D&M;".as_bytes()), Ok((Comp::DAndM,   ";".as_bytes(), 3)));
  /// assert_eq!(Comp::read_from("D|M;".as_bytes()), Ok((Comp::DOrM,    ";".as_bytes(), 3)));
  /// ```
  pub fn read_from(buf: Buf) -> Result<(Self, Buf, usize), ()> {
    let p = |b| b"01AMD+-!&|".contains(&b);
    let (b, rem) = utils::read_while(buf, p);
    let res = Self::try_from(b).map_err(|_| ())?;
    Ok((res, rem, b.len()))
  }
}
