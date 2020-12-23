//! Structures related to HACK instructions.
//!
//! An [instruction](Inst) can represent different types of commands
//! in the HACK assembly language.

use std::fmt;
use std::{convert::TryFrom, str::FromStr};

use crate::utils;

/// A destination as defined by the HACK assembly reference.
///
/// A destination object can be parsed using [Dest::read_from].
///
/// # impl `Into<u16>`
///
/// The binary representation is 3 bits wide representing the bits
/// `d1`, `d2` and `d3` in an [instruction](Inst).
///
/// ## Examples
///
/// ```
/// use has::inst::Dest;
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
/// use has::inst::Dest;
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

impl FromStr for Dest {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match s {
      "M" => Ok(Dest::M),
      "D" => Ok(Dest::D),
      "MD" => Ok(Dest::MD),
      "A" => Ok(Dest::A),
      "AM" => Ok(Dest::AM),
      "AD" => Ok(Dest::AD),
      "AMD" => Ok(Dest::AMD),
      _ => Err(()),
    }
  }
}

impl Dest {
  /// Read a destination object from a string.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::inst::Dest;
  ///
  /// assert_eq!(Dest::read_from(""), Err(()));
  /// assert_eq!(Dest::read_from("Foo"), Err(()));
  ///
  /// assert_eq!(Dest::read_from("M"),   Ok((Dest::M,   "", 1)));
  /// assert_eq!(Dest::read_from("D"),   Ok((Dest::D,   "", 1)));
  /// assert_eq!(Dest::read_from("MD"),  Ok((Dest::MD,  "", 2)));
  /// assert_eq!(Dest::read_from("A"),   Ok((Dest::A,   "", 1)));
  /// assert_eq!(Dest::read_from("AM"),  Ok((Dest::AM,  "", 2)));
  /// assert_eq!(Dest::read_from("AD"),  Ok((Dest::AD,  "", 2)));
  /// assert_eq!(Dest::read_from("AMD"), Ok((Dest::AMD, "", 3)));
  ///
  /// assert_eq!(Dest::read_from("M="),   Ok((Dest::M,   "=", 1)));
  /// assert_eq!(Dest::read_from("D="),   Ok((Dest::D,   "=", 1)));
  /// assert_eq!(Dest::read_from("MD="),  Ok((Dest::MD,  "=", 2)));
  /// assert_eq!(Dest::read_from("A="),   Ok((Dest::A,   "=", 1)));
  /// assert_eq!(Dest::read_from("AM="),  Ok((Dest::AM,  "=", 2)));
  /// assert_eq!(Dest::read_from("AD="),  Ok((Dest::AD,  "=", 2)));
  /// assert_eq!(Dest::read_from("AMD="), Ok((Dest::AMD, "=", 3)));
  /// ```
  pub fn read_from(buf: &str) -> Result<(Self, &str, usize), ()> {
    let p = |c| c == 'A' || c == 'M' || c == 'D';

    let (s, rem) = utils::read_while(buf, p);
    let res = Self::from_str(s).map_err(|_| ())?;
    Ok((res, rem, s.len()))
  }

  /// Whether the destination object is null.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::inst::Dest;
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

/// A computation as defined by the HACK assembly reference.
///
/// A computation object can be created using [Comp::read_from].
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
/// use has::inst::Comp;
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
/// use has::inst::Comp;
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

impl FromStr for Comp {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match s {
      "0" => Ok(Comp::Zero),
      "1" => Ok(Comp::One),
      "-1" => Ok(Comp::Neg1),
      "D" => Ok(Comp::D),
      "A" => Ok(Comp::A),
      "!D" => Ok(Comp::NotD),
      "!A" => Ok(Comp::NotA),
      "-D" => Ok(Comp::NegD),
      "-A" => Ok(Comp::NegA),
      "D+1" => Ok(Comp::DPlus1),
      "A+1" => Ok(Comp::APlus1),
      "D-1" => Ok(Comp::DMinus1),
      "A-1" => Ok(Comp::AMinus1),
      "D+A" => Ok(Comp::DPlusA),
      "D-A" => Ok(Comp::DMinusA),
      "A-D" => Ok(Comp::AMinusD),
      "D&A" => Ok(Comp::DAndA),
      "D|A" => Ok(Comp::DOrA),
      "M" => Ok(Comp::M),
      "!M" => Ok(Comp::NotM),
      "-M" => Ok(Comp::NegM),
      "M+1" => Ok(Comp::MPlus1),
      "M-1" => Ok(Comp::MMinus1),
      "D+M" => Ok(Comp::DPlusM),
      "D-M" => Ok(Comp::DMinusM),
      "M-D" => Ok(Comp::MMinusD),
      "D&M" => Ok(Comp::DAndM),
      "D|M" => Ok(Comp::DOrM),
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
  /// Read a computation object from a string.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::inst::Comp;
  ///
  /// assert_eq!(Comp::read_from(""), Err(()));
  /// assert_eq!(Comp::read_from("Foo"), Err(()));
  ///
  /// assert_eq!(Comp::read_from("0"),   Ok((Comp::Zero,    "", 1)));
  /// assert_eq!(Comp::read_from("1"),   Ok((Comp::One,     "", 1)));
  /// assert_eq!(Comp::read_from("-1"),  Ok((Comp::Neg1,    "", 2)));
  /// assert_eq!(Comp::read_from("D"),   Ok((Comp::D,       "", 1)));
  /// assert_eq!(Comp::read_from("A"),   Ok((Comp::A,       "", 1)));
  /// assert_eq!(Comp::read_from("!D"),  Ok((Comp::NotD,    "", 2)));
  /// assert_eq!(Comp::read_from("!A"),  Ok((Comp::NotA,    "", 2)));
  /// assert_eq!(Comp::read_from("-D"),  Ok((Comp::NegD,    "", 2)));
  /// assert_eq!(Comp::read_from("-A"),  Ok((Comp::NegA,    "", 2)));
  /// assert_eq!(Comp::read_from("D+1"), Ok((Comp::DPlus1,  "", 3)));
  /// assert_eq!(Comp::read_from("A+1"), Ok((Comp::APlus1,  "", 3)));
  /// assert_eq!(Comp::read_from("D-1"), Ok((Comp::DMinus1, "", 3)));
  /// assert_eq!(Comp::read_from("A-1"), Ok((Comp::AMinus1, "", 3)));
  /// assert_eq!(Comp::read_from("D+A"), Ok((Comp::DPlusA,  "", 3)));
  /// assert_eq!(Comp::read_from("D-A"), Ok((Comp::DMinusA, "", 3)));
  /// assert_eq!(Comp::read_from("A-D"), Ok((Comp::AMinusD, "", 3)));
  /// assert_eq!(Comp::read_from("D&A"), Ok((Comp::DAndA,   "", 3)));
  /// assert_eq!(Comp::read_from("D|A"), Ok((Comp::DOrA,    "", 3)));
  /// assert_eq!(Comp::read_from("M"),   Ok((Comp::M,       "", 1)));
  /// assert_eq!(Comp::read_from("!M"),  Ok((Comp::NotM,    "", 2)));
  /// assert_eq!(Comp::read_from("-M"),  Ok((Comp::NegM,    "", 2)));
  /// assert_eq!(Comp::read_from("M+1"), Ok((Comp::MPlus1,  "", 3)));
  /// assert_eq!(Comp::read_from("M-1"), Ok((Comp::MMinus1, "", 3)));
  /// assert_eq!(Comp::read_from("D+M"), Ok((Comp::DPlusM,  "", 3)));
  /// assert_eq!(Comp::read_from("D-M"), Ok((Comp::DMinusM, "", 3)));
  /// assert_eq!(Comp::read_from("M-D"), Ok((Comp::MMinusD, "", 3)));
  /// assert_eq!(Comp::read_from("D&M"), Ok((Comp::DAndM,   "", 3)));
  /// assert_eq!(Comp::read_from("D|M"), Ok((Comp::DOrM,    "", 3)));
  ///
  /// assert_eq!(Comp::read_from("0;"),   Ok((Comp::Zero,    ";", 1)));
  /// assert_eq!(Comp::read_from("1;"),   Ok((Comp::One,     ";", 1)));
  /// assert_eq!(Comp::read_from("-1;"),  Ok((Comp::Neg1,    ";", 2)));
  /// assert_eq!(Comp::read_from("D;"),   Ok((Comp::D,       ";", 1)));
  /// assert_eq!(Comp::read_from("A;"),   Ok((Comp::A,       ";", 1)));
  /// assert_eq!(Comp::read_from("!D;"),  Ok((Comp::NotD,    ";", 2)));
  /// assert_eq!(Comp::read_from("!A;"),  Ok((Comp::NotA,    ";", 2)));
  /// assert_eq!(Comp::read_from("-D;"),  Ok((Comp::NegD,    ";", 2)));
  /// assert_eq!(Comp::read_from("-A;"),  Ok((Comp::NegA,    ";", 2)));
  /// assert_eq!(Comp::read_from("D+1;"), Ok((Comp::DPlus1,  ";", 3)));
  /// assert_eq!(Comp::read_from("A+1;"), Ok((Comp::APlus1,  ";", 3)));
  /// assert_eq!(Comp::read_from("D-1;"), Ok((Comp::DMinus1, ";", 3)));
  /// assert_eq!(Comp::read_from("A-1;"), Ok((Comp::AMinus1, ";", 3)));
  /// assert_eq!(Comp::read_from("D+A;"), Ok((Comp::DPlusA,  ";", 3)));
  /// assert_eq!(Comp::read_from("D-A;"), Ok((Comp::DMinusA, ";", 3)));
  /// assert_eq!(Comp::read_from("A-D;"), Ok((Comp::AMinusD, ";", 3)));
  /// assert_eq!(Comp::read_from("D&A;"), Ok((Comp::DAndA,   ";", 3)));
  /// assert_eq!(Comp::read_from("D|A;"), Ok((Comp::DOrA,    ";", 3)));
  /// assert_eq!(Comp::read_from("M;"),   Ok((Comp::M,       ";", 1)));
  /// assert_eq!(Comp::read_from("!M;"),  Ok((Comp::NotM,    ";", 2)));
  /// assert_eq!(Comp::read_from("-M;"),  Ok((Comp::NegM,    ";", 2)));
  /// assert_eq!(Comp::read_from("M+1;"), Ok((Comp::MPlus1,  ";", 3)));
  /// assert_eq!(Comp::read_from("M-1;"), Ok((Comp::MMinus1, ";", 3)));
  /// assert_eq!(Comp::read_from("D+M;"), Ok((Comp::DPlusM,  ";", 3)));
  /// assert_eq!(Comp::read_from("D-M;"), Ok((Comp::DMinusM, ";", 3)));
  /// assert_eq!(Comp::read_from("M-D;"), Ok((Comp::MMinusD, ";", 3)));
  /// assert_eq!(Comp::read_from("D&M;"), Ok((Comp::DAndM,   ";", 3)));
  /// assert_eq!(Comp::read_from("D|M;"), Ok((Comp::DOrM,    ";", 3)));
  /// ```
  pub fn read_from(buf: &str) -> Result<(Self, &str, usize), ()> {
    let p = |c| {
      c == '0'
        || c == '1'
        || c == 'A'
        || c == 'M'
        || c == 'D'
        || c == '+'
        || c == '-'
        || c == '!'
        || c == '&'
        || c == '|'
    };

    let (s, rem) = utils::read_while(buf, p);
    let res = Self::from_str(s).map_err(|_| ())?;
    Ok((res, rem, s.len()))
  }
}

/// A jump as defined by the HACK assembly reference.
///
/// A jump object can be parsed using [Jump::read_from].
///
/// # impl `Into<u16>`
///
/// The binary representation is 3 bits wide representing the bits
/// `j1`, `j2` and `j3` in an [instruction](Inst).
///
/// ## Examples
///
/// ```
/// use has::inst::Jump;
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
/// use has::inst::Jump;
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

impl FromStr for Jump {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match s {
      "JGT" => Ok(Jump::JGT),
      "JEQ" => Ok(Jump::JEQ),
      "JGE" => Ok(Jump::JGE),
      "JLT" => Ok(Jump::JLT),
      "JNE" => Ok(Jump::JNE),
      "JLE" => Ok(Jump::JLE),
      "JMP" => Ok(Jump::JMP),
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
  /// Read a jump object from a string.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::inst::Jump;
  ///
  /// assert_eq!(Jump::read_from(""), Err(()));
  /// assert_eq!(Jump::read_from("Foo"), Err(()));
  ///
  /// assert_eq!(Jump::read_from("JGT"), Ok((Jump::JGT, "", 3)));
  /// assert_eq!(Jump::read_from("JEQ"), Ok((Jump::JEQ, "", 3)));
  /// assert_eq!(Jump::read_from("JGE"), Ok((Jump::JGE, "", 3)));
  /// assert_eq!(Jump::read_from("JLT"), Ok((Jump::JLT, "", 3)));
  /// assert_eq!(Jump::read_from("JNE"), Ok((Jump::JNE, "", 3)));
  /// assert_eq!(Jump::read_from("JLE"), Ok((Jump::JLE, "", 3)));
  /// assert_eq!(Jump::read_from("JMP"), Ok((Jump::JMP, "", 3)));
  ///
  /// assert_eq!(Jump::read_from("JGT //"), Ok((Jump::JGT, " //", 3)));
  /// assert_eq!(Jump::read_from("JEQ //"), Ok((Jump::JEQ, " //", 3)));
  /// assert_eq!(Jump::read_from("JGE //"), Ok((Jump::JGE, " //", 3)));
  /// assert_eq!(Jump::read_from("JLT //"), Ok((Jump::JLT, " //", 3)));
  /// assert_eq!(Jump::read_from("JNE //"), Ok((Jump::JNE, " //", 3)));
  /// assert_eq!(Jump::read_from("JLE //"), Ok((Jump::JLE, " //", 3)));
  /// assert_eq!(Jump::read_from("JMP //"), Ok((Jump::JMP, " //", 3)));
  /// ```
  pub fn read_from(buf: &str) -> Result<(Self, &str, usize), ()> {
    let p = |c| {
      c == 'J'
        || c == 'G'
        || c == 'T'
        || c == 'E'
        || c == 'L'
        || c == 'N'
        || c == 'M'
        || c == 'P'
        || c == 'Q'
    };

    let (s, rem) = utils::read_while(buf, p);
    let res = Self::from_str(s).map_err(|_| ())?;
    Ok((res, rem, s.len()))
  }

  /// Whether the [jump](Jump) object is null.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::inst::Jump;
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

// /// An instruction.
// ///
// /// An instruction consists of a [destination](Dest), a
// /// [computation](Comp) and a [jump](Jump).
// ///
// /// # impl `Display` examples
// ///
// /// ```
// /// use has::inst::Inst;
// /// use has::inst::Dest;
// /// use has::inst::Comp;
// /// use has::inst::Jump;
// ///
// /// let mut buf = "MD=D+A;JGT".as_bytes();
// /// assert_eq!(Inst::from_buf(&mut buf), Ok(Inst::new(Dest::MD, Comp::DPlusA, Jump::JGT)));
// /// ```
// #[derive(Debug, Clone, Copy, PartialEq, Eq)]
// pub struct Inst {
//   dest: Dest,
//   comp: Comp,
//   jump: Jump,
// }

// impl fmt::Display for Inst {
//   fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//     if !self.dest.is_null() {
//       write!(f, "{}=", self.dest)?;
//     }

//     write!(f, "{}", self.comp)?;

//     if !self.jump.is_null() {
//       write!(f, ";{}", self.jump)?;
//     }

//     Ok(())
//   }
// }

// #[derive(Debug, Clone, Copy, PartialEq, Eq)]
// pub enum InstErr {
//   NoDestNoJump,
//   Dest,
//   Comp,
//   Jump,
// }

// impl Inst {
//   pub fn new(dest: Dest, comp: Comp, jump: Jump) -> Self {
//     Self { dest, comp, jump }
//   }

//   pub fn from_buf(buf: &mut &[u8]) -> Result<Self, InstErr> {
//     let dest = Inst::dest_from_buf(buf)?;
//     let dest_null = dest.is_null();

//     if !dest_null {
//       if buf.is_empty() || unsafe { *buf.get_unchecked(0) } != b'=' {
//         return Err(InstErr::Dest);
//       }

//       *buf = &buf[1..];
//     }

//     let comp = Inst::comp_from_buf(buf)?;

//     let jump = if !buf.is_empty() && unsafe { *buf.get_unchecked(0) } == b';' {
//       *buf = &buf[1..];
//       Inst::jump_from_buf(buf)?
//     } else {
//       Jump::Null
//     };

//     if dest_null && jump.is_null() {
//       return Err(InstErr::NoDestNoJump);
//     }

//     Ok(Self { dest, comp, jump })
//   }

//   fn dest_from_buf(buf: &mut &[u8]) -> Result<Dest, InstErr> {
//     for (i, &b) in buf.iter().enumerate() {
//       if b == b'=' {
//         let dest = Dest::try_from(&buf[..i]).map_err(|_| InstErr::Dest)?;
//         *buf = &buf[i..];
//         return Ok(dest);
//       } else if b == b';' {
//         return Ok(Dest::Null);
//       } else if b != b'A' && b != b'M' && b != b'D' {
//         break;
//       }
//     }

//     Err(InstErr::Dest)
//   }

//   fn comp_from_buf(buf: &mut &[u8]) -> Result<Comp, InstErr> {
//     let len = buf.len();

//     for (i, &b) in buf.iter().enumerate() {
//       if b == b';' || b.is_ascii_whitespace() || i == len {
//         let comp = Comp::try_from(&buf[..i]).map_err(|_| InstErr::Comp)?;
//         *buf = &buf[i..];
//         return Ok(comp);
//       } else if b != b'0'
//         && b != b'1'
//         && b != b'A'
//         && b != b'M'
//         && b != b'D'
//         && b != b'+'
//         && b != b'-'
//         && b != b'!'
//         && b != b'&'
//         && b != b'|'
//       {
//         break;
//       }
//     }

//     Err(InstErr::Comp)
//   }

//   fn jump_from_buf(buf: &mut &[u8]) -> Result<Jump, InstErr> {
//     let len = buf.len();

//     for (i, &b) in buf.iter().enumerate() {
//       if b.is_ascii_whitespace() || i == len {
//         let jump = Jump::try_from(&buf[..i]).map_err(|_| InstErr::Jump)?;
//         *buf = &buf[i..];
//         return Ok(jump);
//       } else if b != b'J'
//         && b != b'G'
//         && b != b'T'
//         && b != b'E'
//         && b != b'Q'
//         && b != b'L'
//         && b != b'N'
//         && b != b'M'
//         && b != b'P'
//       {
//         dbg!(b);
//         break;
//       }
//     }

//     dbg!(buf);
//     Err(InstErr::Jump)
//   }
// }

/// An encoding for predefined symbols as defined by the HACK assembly
/// reference.
///
/// # impl `Into<u16>`
///
/// The binary representation is 15 bits wide as defined by
/// A-instructions in the HACK assembly language.
///
/// ## Examples
///
/// ```
/// use has::inst::Predef;
///
/// assert_eq!(u16::from(Predef::SP),     0x0000);
/// assert_eq!(u16::from(Predef::LCL),    0x0001);
/// assert_eq!(u16::from(Predef::ARG),    0x0002);
/// assert_eq!(u16::from(Predef::THIS),   0x0003);
/// assert_eq!(u16::from(Predef::THAT),   0x0004);
/// assert_eq!(u16::from(Predef::R0),     0x0000);
/// assert_eq!(u16::from(Predef::R1),     0x0001);
/// assert_eq!(u16::from(Predef::R2),     0x0002);
/// assert_eq!(u16::from(Predef::R3),     0x0003);
/// assert_eq!(u16::from(Predef::R4),     0x0004);
/// assert_eq!(u16::from(Predef::R5),     0x0005);
/// assert_eq!(u16::from(Predef::R6),     0x0006);
/// assert_eq!(u16::from(Predef::R7),     0x0007);
/// assert_eq!(u16::from(Predef::R8),     0x0008);
/// assert_eq!(u16::from(Predef::R9),     0x0009);
/// assert_eq!(u16::from(Predef::R10),    0x000A);
/// assert_eq!(u16::from(Predef::R11),    0x000B);
/// assert_eq!(u16::from(Predef::R12),    0x000C);
/// assert_eq!(u16::from(Predef::R13),    0x000D);
/// assert_eq!(u16::from(Predef::R14),    0x000E);
/// assert_eq!(u16::from(Predef::R15),    0x000F);
/// assert_eq!(u16::from(Predef::SCREEN), 0x4000);
/// assert_eq!(u16::from(Predef::KBD),    0x6000);
/// ```
///
/// # impl `TryFrom<&[u8]>` (`type Error = ()`)
///
/// A [Predef] object can be created from a slice of bytes. A
/// `Result::Err(())` is returned if the input sequence is not
/// recognized.
///
/// ## Examples
///
/// ```
/// use has::inst::Predef;
/// use std::convert::TryFrom;
///
/// assert_eq!(Predef::try_from(&b""[..]),    Err(()));
/// assert_eq!(Predef::try_from(&b"Foo"[..]), Err(()));
///
/// assert_eq!(Predef::try_from(&b"SP"[..]),     Ok(Predef::SP));
/// assert_eq!(Predef::try_from(&b"LCL"[..]),    Ok(Predef::LCL));
/// assert_eq!(Predef::try_from(&b"ARG"[..]),    Ok(Predef::ARG));
/// assert_eq!(Predef::try_from(&b"THIS"[..]),   Ok(Predef::THIS));
/// assert_eq!(Predef::try_from(&b"THAT"[..]),   Ok(Predef::THAT));
/// assert_eq!(Predef::try_from(&b"R0"[..]),     Ok(Predef::R0));
/// assert_eq!(Predef::try_from(&b"R1"[..]),     Ok(Predef::R1));
/// assert_eq!(Predef::try_from(&b"R2"[..]),     Ok(Predef::R2));
/// assert_eq!(Predef::try_from(&b"R3"[..]),     Ok(Predef::R3));
/// assert_eq!(Predef::try_from(&b"R4"[..]),     Ok(Predef::R4));
/// assert_eq!(Predef::try_from(&b"R5"[..]),     Ok(Predef::R5));
/// assert_eq!(Predef::try_from(&b"R6"[..]),     Ok(Predef::R6));
/// assert_eq!(Predef::try_from(&b"R7"[..]),     Ok(Predef::R7));
/// assert_eq!(Predef::try_from(&b"R8"[..]),     Ok(Predef::R8));
/// assert_eq!(Predef::try_from(&b"R9"[..]),     Ok(Predef::R9));
/// assert_eq!(Predef::try_from(&b"R10"[..]),    Ok(Predef::R10));
/// assert_eq!(Predef::try_from(&b"R11"[..]),    Ok(Predef::R11));
/// assert_eq!(Predef::try_from(&b"R12"[..]),    Ok(Predef::R12));
/// assert_eq!(Predef::try_from(&b"R13"[..]),    Ok(Predef::R13));
/// assert_eq!(Predef::try_from(&b"R14"[..]),    Ok(Predef::R14));
/// assert_eq!(Predef::try_from(&b"R15"[..]),    Ok(Predef::R15));
/// assert_eq!(Predef::try_from(&b"SCREEN"[..]), Ok(Predef::SCREEN));
/// assert_eq!(Predef::try_from(&b"KBD"[..]),    Ok(Predef::KBD));
/// ```
///
/// # impl `Display`
///
/// ```
/// use has::inst::Predef;
///
/// assert_eq!(format!("{}", Predef::SP),     "SP");
/// assert_eq!(format!("{}", Predef::LCL),    "LCL");
/// assert_eq!(format!("{}", Predef::ARG),    "ARG");
/// assert_eq!(format!("{}", Predef::THIS),   "THIS");
/// assert_eq!(format!("{}", Predef::THAT),   "THAT");
/// assert_eq!(format!("{}", Predef::R0),     "R0");
/// assert_eq!(format!("{}", Predef::R1),     "R1");
/// assert_eq!(format!("{}", Predef::R2),     "R2");
/// assert_eq!(format!("{}", Predef::R3),     "R3");
/// assert_eq!(format!("{}", Predef::R4),     "R4");
/// assert_eq!(format!("{}", Predef::R5),     "R5");
/// assert_eq!(format!("{}", Predef::R6),     "R6");
/// assert_eq!(format!("{}", Predef::R7),     "R7");
/// assert_eq!(format!("{}", Predef::R8),     "R8");
/// assert_eq!(format!("{}", Predef::R9),     "R9");
/// assert_eq!(format!("{}", Predef::R10),    "R10");
/// assert_eq!(format!("{}", Predef::R11),    "R11");
/// assert_eq!(format!("{}", Predef::R12),    "R12");
/// assert_eq!(format!("{}", Predef::R13),    "R13");
/// assert_eq!(format!("{}", Predef::R14),    "R14");
/// assert_eq!(format!("{}", Predef::R15),    "R15");
/// assert_eq!(format!("{}", Predef::SCREEN), "SCREEN");
/// assert_eq!(format!("{}", Predef::KBD),    "KBD");
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Predef {
  /// Stack Pointer.
  SP,
  /// LCL.
  LCL,
  /// Argument.
  ARG,
  /// This reference.
  THIS,
  /// That reference.
  THAT,
  /// Register 0.
  R0,
  /// Register 1.
  R1,
  /// Register 2.
  R2,
  /// Register 3.
  R3,
  /// Register 4.
  R4,
  /// Register 5.
  R5,
  /// Register 6.
  R6,
  /// Register 7.
  R7,
  /// Register 8.
  R8,
  /// Register 9.
  R9,
  /// Register 10.
  R10,
  /// Register 11.
  R11,
  /// Register 12.
  R12,
  /// Register 13.
  R13,
  /// Register 14.
  R14,
  /// Register 15.
  R15,
  /// Screen buffer.
  SCREEN,
  /// Keyboard input.
  KBD,
}

impl From<Predef> for u16 {
  fn from(predef: Predef) -> Self {
    match predef {
      Predef::SP => 0x0000,
      Predef::LCL => 0x0001,
      Predef::ARG => 0x0002,
      Predef::THIS => 0x0003,
      Predef::THAT => 0x0004,
      Predef::R0 => 0x0000,
      Predef::R1 => 0x0001,
      Predef::R2 => 0x0002,
      Predef::R3 => 0x0003,
      Predef::R4 => 0x0004,
      Predef::R5 => 0x0005,
      Predef::R6 => 0x0006,
      Predef::R7 => 0x0007,
      Predef::R8 => 0x0008,
      Predef::R9 => 0x0009,
      Predef::R10 => 0x000A,
      Predef::R11 => 0x000B,
      Predef::R12 => 0x000C,
      Predef::R13 => 0x000D,
      Predef::R14 => 0x000E,
      Predef::R15 => 0x000F,
      Predef::SCREEN => 0x4000,
      Predef::KBD => 0x6000,
    }
  }
}

impl TryFrom<&[u8]> for Predef {
  type Error = ();

  fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
    match bytes {
      b"SP" => Ok(Predef::SP),
      b"LCL" => Ok(Predef::LCL),
      b"ARG" => Ok(Predef::ARG),
      b"THIS" => Ok(Predef::THIS),
      b"THAT" => Ok(Predef::THAT),
      b"R0" => Ok(Predef::R0),
      b"R1" => Ok(Predef::R1),
      b"R2" => Ok(Predef::R2),
      b"R3" => Ok(Predef::R3),
      b"R4" => Ok(Predef::R4),
      b"R5" => Ok(Predef::R5),
      b"R6" => Ok(Predef::R6),
      b"R7" => Ok(Predef::R7),
      b"R8" => Ok(Predef::R8),
      b"R9" => Ok(Predef::R9),
      b"R10" => Ok(Predef::R10),
      b"R11" => Ok(Predef::R11),
      b"R12" => Ok(Predef::R12),
      b"R13" => Ok(Predef::R13),
      b"R14" => Ok(Predef::R14),
      b"R15" => Ok(Predef::R15),
      b"SCREEN" => Ok(Predef::SCREEN),
      b"KBD" => Ok(Predef::KBD),
      _ => Err(()),
    }
  }
}

impl fmt::Display for Predef {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Predef::SP => write!(f, "SP"),
      Predef::LCL => write!(f, "LCL"),
      Predef::ARG => write!(f, "ARG"),
      Predef::THIS => write!(f, "THIS"),
      Predef::THAT => write!(f, "THAT"),
      Predef::R0 => write!(f, "R0"),
      Predef::R1 => write!(f, "R1"),
      Predef::R2 => write!(f, "R2"),
      Predef::R3 => write!(f, "R3"),
      Predef::R4 => write!(f, "R4"),
      Predef::R5 => write!(f, "R5"),
      Predef::R6 => write!(f, "R6"),
      Predef::R7 => write!(f, "R7"),
      Predef::R8 => write!(f, "R8"),
      Predef::R9 => write!(f, "R9"),
      Predef::R10 => write!(f, "R10"),
      Predef::R11 => write!(f, "R11"),
      Predef::R12 => write!(f, "R12"),
      Predef::R13 => write!(f, "R13"),
      Predef::R14 => write!(f, "R14"),
      Predef::R15 => write!(f, "R15"),
      Predef::SCREEN => write!(f, "SCREEN"),
      Predef::KBD => write!(f, "KBD"),
    }
  }
}

/// An encoding for user-defined symbols as defined by the HACK
/// assembly reference.
///
/// # impl `TryFrom<&[u8]>` (`type Error = ()`)
///
/// A [Label] object can be created from a slice of bytes. A
/// `Result::Err(())` is returned if the input sequence is invalid.
///
/// ## Examples
///
/// ```
/// use has::inst::Label;
/// use std::convert::TryFrom;
///
/// assert_eq!(Label::try_from(&b"@foobar"[..]), Err(()));
/// assert_eq!(Label::try_from(&b"foobar@"[..]), Err(()));
/// assert_eq!(Label::try_from(&b"1foobar"[..]), Err(()));
///
/// assert_eq!(Label::try_from(&b"foobar1"[..]).unwrap().label(), &b"foobar1"[..]);
/// ```
///
/// # impl `Display`
///
/// ```
/// use has::inst::Label;
/// use std::convert::TryFrom;
///
/// assert_eq!(format!("{}", Label::try_from(&b"foobar"[..]).unwrap()), "foobar");
/// ```
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Label<'b>(&'b [u8]);

impl Label<'_> {
  /// Whether a byte is a symbol that can be used in a [Label].
  ///
  /// Returns true if `byte` is either `_`, `.`, `$` or `:`.
  fn is_label_symbol(byte: u8) -> bool {
    byte == b'_' || byte == b'.' || byte == b'$' || byte == b':'
  }

  /// Whether a byte can be at the start of a [Label].
  ///
  /// Returns true if `byte` [is ASCII
  /// alphabetic](is_ascii_alphabetic) or [is a label
  /// symbol](is_label_symbol).
  pub(crate) fn is_label_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || Label::is_label_symbol(byte)
  }

  /// Whether a byte can be part of a [Label].
  ///
  /// Returns true if `byte` [is ASCII
  /// alphabetic](is_ascii_alphanumeric) or [is a label
  /// symbol](is_label_symbol).
  pub(crate) fn is_label_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || Label::is_label_symbol(byte)
  }

  /// Returns the label byte slice of a [Label].
  ///
  /// # Examples
  ///
  /// ```
  /// use has::inst::Label;
  /// use std::convert::TryFrom;
  ///
  /// assert_eq!(Label::try_from(&b"foobar1"[..]).unwrap().label(), &b"foobar1"[..]);
  pub fn label(&self) -> &[u8] {
    self.0
  }
}

#[cfg(test)]
mod label_tests {
  use super::Label;

  #[test]
  fn test_is_label_symbol() {
    assert!(Label::is_label_symbol(b'_'));
    assert!(Label::is_label_symbol(b'.'));
    assert!(Label::is_label_symbol(b'$'));
    assert!(Label::is_label_symbol(b':'));

    assert!(!Label::is_label_symbol(b'@'));
    assert!(!Label::is_label_symbol(b'^'));
    assert!(!Label::is_label_symbol(b'&'));
    assert!(!Label::is_label_symbol(b'*'));
    assert!(!Label::is_label_symbol(b'('));
    assert!(!Label::is_label_symbol(b')'));
    assert!(!Label::is_label_symbol(b'%'));
    assert!(!Label::is_label_symbol(b'#'));
    assert!(!Label::is_label_symbol(b'!'));
  }
}

impl<'b> TryFrom<&'b [u8]> for Label<'b> {
  type Error = ();

  fn try_from(bytes: &'b [u8]) -> Result<Self, Self::Error> {
    let c0 = if let Some(&c0) = bytes.get(0) {
      c0
    } else {
      return Err(());
    };

    if !Label::is_label_start(c0) {
      return Err(());
    }

    for &c in &bytes[1..] {
      if !Label::is_label_byte(c) {
        return Err(());
      }
    }

    Ok(Self(bytes))
  }
}

impl fmt::Display for Label<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", unsafe { std::str::from_utf8_unchecked(self.0) })
  }
}

/// An encoding for addressing instructions (A-instructions) as
/// defined by the HACK assembly reference.
///
/// The binary representation is 16 bits wide as defined by the HACK
/// assembly language. The most significant bit is always `0` to
/// signify an A-instruction and the effective addressing width is the
/// remaining 15 bits.
///
/// # impl `TryFrom<u16>` (`type Error = ()`)
///
/// Creates an [Addr::Num] object from a [u16].
///
/// If the value is outside the range of unsigned 15-bits (> 32767),
/// `Err(())` is returned.
///
/// ## Examples
///
/// ```
/// use has::inst::Addr;
/// use std::convert::TryFrom;
///
/// assert_eq!(Addr::try_from(25), Ok(Addr::Num(25)));
/// assert_eq!(Addr::try_from(32768), Err(()));
/// ```
///
/// # impl `From<Label>`
///
/// Creates an [Addr::Label] object from a [Label].
///
/// ## Examples
///
/// ```
/// use has::inst::Addr;
/// use has::inst::Label;
/// use std::convert::TryFrom;
///
/// assert_eq!(Addr::from(Label::try_from(&b"foobar1"[..]).unwrap()),
///            Addr::Label(Label::try_from(&b"foobar1"[..]).unwrap()));
/// ```
///
/// # impl `From<Predef>`
///
/// Creates an [Addr::Predef] object from a [Predef].
///
/// ## Examples
///
/// ```
/// use has::inst::Addr;
/// use has::inst::Predef;
///
/// assert_eq!(Addr::from(Predef::LCL), Addr::Predef(Predef::LCL));
/// ```
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Addr<'b> {
  Num(u16),
  Label(Label<'b>),
  Predef(Predef),
}

impl TryFrom<u16> for Addr<'_> {
  type Error = ();

  fn try_from(addr: u16) -> Result<Self, Self::Error> {
    // 32767 (15 bits of address value)
    if addr <= 32767 {
      return Ok(Self::Num(addr));
    }

    Err(())
  }
}

impl<'b> From<Label<'b>> for Addr<'b> {
  fn from(label: Label<'b>) -> Self {
    Addr::Label(label)
  }
}

impl From<Predef> for Addr<'_> {
  fn from(predef: Predef) -> Self {
    Addr::Predef(predef)
  }
}

impl fmt::Display for Addr<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Addr::Num(addr) => write!(f, "@{}", addr),
      Addr::Label(label) => write!(f, "@{}", label),
      Addr::Predef(predef) => write!(f, "@{}", predef),
    }
  }
}

// impl TryFrom<Text> for Addr {
//   type Error = AddrErr;

//   fn try_from(v: Text) -> Result<Self, Self::Error> {
//     if v.is_empty() {
//       return Err(AddrErr::Empty);
//     }

//     let c0 = unsafe { v.get_unchecked(0) };

//     if !c0.is_ascii_digit() {
//       if let Ok(predef) = Predef::try_from(&v) {
//         return Ok(Self::Predef(predef));
//       }

//       return match Label::try_from(v) {
//         Ok(label) => Ok(Self::Label(label)),
//         Err(e) => Err(AddrErr::Other(Box::new(e))),
//       };
//     }

//     for c in &v[1..] {
//       if !c.is_ascii_digit() {
//         return Err(AddrErr::NotDigit { byte: *c });
//       }
//     }

//     if let Some(addr) = u16::from_radix_10_checked(&v).0 {
//       // 32767 (15 bits of address value)
//       if addr <= 32767 {
//         return Ok(Self::Num(addr));
//       }
//     }

//     Err(AddrErr::Range { addr: v, max: 32767 })
//   }
// }

// #[derive(Debug, PartialEq, Eq)]
// pub enum Inst<'b> {
//   Addr(Addr<'b>),
//   Stmt(Dest, Comp, Jump),
// }

//  Label(Label<'b>),
