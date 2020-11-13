use atoi::FromRadix10Checked;
use std::fmt;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Destination {
  M,
  D,
  MD,
  A,
  AM,
  AD,
  AMD,
}

impl fmt::Display for Destination {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Destination::M => write!(f, "M"),
      Destination::D => write!(f, "D"),
      Destination::MD => write!(f, "MD"),
      Destination::A => write!(f, "A"),
      Destination::AM => write!(f, "AM"),
      Destination::AD => write!(f, "AD"),
      Destination::AMD => write!(f, "AMD"),
    }
  }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Computation {
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

impl fmt::Display for Computation {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Computation::Zero => write!(f, "0"),
      Computation::One => write!(f, "1"),
      Computation::Neg1 => write!(f, "-1"),
      Computation::D => write!(f, "D"),
      Computation::A => write!(f, "A"),
      Computation::NotD => write!(f, "!D"),
      Computation::NotA => write!(f, "!A"),
      Computation::NegD => write!(f, "-D"),
      Computation::NegA => write!(f, "-A"),
      Computation::DPlus1 => write!(f, "D+1"),
      Computation::APlus1 => write!(f, "A+1"),
      Computation::DMinus1 => write!(f, "D-1"),
      Computation::AMinus1 => write!(f, "A-1"),
      Computation::DPlusA => write!(f, "D+A"),
      Computation::DMinusA => write!(f, "D-A"),
      Computation::AMinusD => write!(f, "A-D"),
      Computation::DAndA => write!(f, "D&A"),
      Computation::DOrA => write!(f, "D|A"),
      Computation::M => write!(f, "M"),
      Computation::NotM => write!(f, "!M"),
      Computation::NegM => write!(f, "-M"),
      Computation::MPlus1 => write!(f, "M+1"),
      Computation::MMinus1 => write!(f, "M-1"),
      Computation::DPlusM => write!(f, "D+M"),
      Computation::DMinusM => write!(f, "D-M"),
      Computation::MMinusD => write!(f, "M-D"),
      Computation::DAndM => write!(f, "D&M"),
      Computation::DOrM => write!(f, "D|M"),
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

#[derive(Debug, PartialEq, Eq)]
pub enum Token<'b> {
  AddressNumerical(u16),
  AddressLabel(&'b [u8]),
  AddressSP,
  AddressLCL,
  AddressARG,
  AddressTHIS,
  AddressTHAT,
  AddressR0,
  AddressR1,
  AddressR2,
  AddressR3,
  AddressR4,
  AddressR5,
  AddressR6,
  AddressR7,
  AddressR8,
  AddressR9,
  AddressR10,
  AddressR11,
  AddressR12,
  AddressR13,
  AddressR14,
  AddressR15,
  AddressSCREEN,
  AddressKBD,
  Label(&'b [u8]),
  SemiColon,
  Assignment(Destination, Computation),
  Branch(Computation, Jump),
  Instruction(Destination, Computation, Jump),
}

impl Token<'_> {
  pub(crate) fn new_numerical_address(address: &[u8]) -> Option<u16> {
    if let Some(addr) = u16::from_radix_10_checked(address).0 {
      // 32767 (15 bits of address value)
      if addr <= 32767 {
        return Some(addr);
      }
    }

    None
  }
}
