// use atoi::FromRadix10Checked;
use std::convert::TryFrom;
// use std::error::Error;
use std::fmt;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Dest {
  M,
  D,
  MD,
  A,
  AM,
  AD,
  AMD,
}

impl<'b> TryFrom<&'b [u8]> for Dest {
  type Error = ();

  fn try_from(buf: &'b [u8]) -> Result<Self, Self::Error> {
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

impl fmt::Display for Dest {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Comp {
  Zero,
  One,
  Neg1,
  D,
  A,
  NotD,
  NotA,
  NegD,
  NegA,
  DPlus1,
  APlus1,
  DMinus1,
  AMinus1,
  DPlusA,
  DMinusA,
  AMinusD,
  DAndA,
  DOrA,
  M,
  NotM,
  NegM,
  MPlus1,
  MMinus1,
  DPlusM,
  DMinusM,
  MMinusD,
  DAndM,
  DOrM,
}

impl<'b> TryFrom<&'b [u8]> for Comp {
  type Error = ();

  fn try_from(buf: &'b [u8]) -> Result<Self, Self::Error> {
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Jump {
  JGT,
  JEQ,
  JGE,
  JLT,
  JNE,
  JLE,
  JMP,
}

impl<'b> TryFrom<&'b [u8]> for Jump {
  type Error = ();

  fn try_from(buf: &'b [u8]) -> Result<Self, Self::Error> {
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Predef {
  SP,
  LCL,
  ARG,
  THIS,
  THAT,
  R0,
  R1,
  R2,
  R3,
  R4,
  R5,
  R6,
  R7,
  R8,
  R9,
  R10,
  R11,
  R12,
  R13,
  R14,
  R15,
  SCREEN,
  KBD,
}

impl<'b> TryFrom<&'b [u8]> for Predef {
  type Error = ();

  fn try_from(buf: &'b [u8]) -> Result<Self, Self::Error> {
    match buf {
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Label<'b>(&'b [u8]);

impl Label<'_> {
  fn is_label_symbol(byte: u8) -> bool {
    byte == b'_' || byte == b'.' || byte == b'$' || byte == b':'
  }

  pub(crate) fn is_label_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || Label::is_label_symbol(byte)
  }

  pub(crate) fn is_label_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || Label::is_label_symbol(byte)
  }
}

impl<'b> TryFrom<&'b [u8]> for Label<'b> {
  type Error = ();

  fn try_from(buf: &'b [u8]) -> Result<Self, Self::Error> {
    let c0 = if let Some(&c0) = buf.get(0) {
      c0
    } else {
      return Err(());
    };

    if !Label::is_label_start(c0) {
      return Err(());
    }

    for &c in &buf[1..] {
      if !Label::is_label_byte(c) {
        return Err(());
      }
    }

    Ok(Self(buf))
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Addr<'b> {
  Num(u16),
  Label(Label<'b>),
  Predef(Predef),
}

impl<'b> TryFrom<u16> for Addr<'b> {
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
  fn from(label: Predef) -> Self {
    Addr::Predef(label)
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

#[derive(Debug, PartialEq, Eq)]
pub enum Inst<'b> {
  Addr(Addr<'b>),
  Label(Label<'b>),
  Assign(Dest, Comp),
  Branch(Comp, Jump),
  Stmt(Dest, Comp, Jump),
}
