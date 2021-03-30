//! Predefined addresses for the `HACK` assembly language.

use derive_more::Display;
use std::convert::TryFrom;

/// Predefined addresses as defined by the `HACK` assembly reference.
///
/// The binary representation is 15 bits wide and can fit in an
/// address instruction (A-instruction).
#[derive(Display, Debug, PartialEq, Eq, Clone, Copy)]
pub enum PredefinedAddress {
  /// Stack Pointer.
  #[display(fmt = "SP")]
  SP,

  /// LCL.
  #[display(fmt = "LCL")]
  LCL,

  /// Argument.
  #[display(fmt = "ARG")]
  ARG,

  /// This reference.
  #[display(fmt = "THIS")]
  THIS,

  /// That reference.
  #[display(fmt = "THAT")]
  THAT,

  /// Register 0.
  #[display(fmt = "R0")]
  R0,

  /// Register 1.
  #[display(fmt = "R1")]
  R1,

  /// Register 2.
  #[display(fmt = "R2")]
  R2,

  /// Register 3.
  #[display(fmt = "R3")]
  R3,

  /// Register 4.
  #[display(fmt = "R4")]
  R4,

  /// Register 5.
  #[display(fmt = "R5")]
  R5,

  /// Register 6.
  #[display(fmt = "R6")]
  R6,

  /// Register 7.
  #[display(fmt = "R7")]
  R7,

  /// Register 8.
  #[display(fmt = "R8")]
  R8,

  /// Register 9.
  #[display(fmt = "R9")]
  R9,

  /// Register 10.
  #[display(fmt = "R10")]
  R10,

  /// Register 11.
  #[display(fmt = "R11")]
  R11,

  /// Register 12.
  #[display(fmt = "R12")]
  R12,

  /// Register 13.
  #[display(fmt = "R13")]
  R13,

  /// Register 14.
  #[display(fmt = "R14")]
  R14,

  /// Register 15.
  #[display(fmt = "R15")]
  R15,

  /// Screen buffer.
  #[display(fmt = "SCREEN")]
  SCREEN,

  /// Keyboard input.
  #[display(fmt = "KBD")]
  KBD,
}

/// Parse a predefined address from a byte buffer.
///
/// An unrecognized input produces an `Err(())`.
impl TryFrom<&'_ [u8]> for PredefinedAddress {
  type Error = ();

  fn try_from(buf: &[u8]) -> Result<Self, Self::Error> {
    match buf {
      b"SP" => Ok(PredefinedAddress::SP),
      b"LCL" => Ok(PredefinedAddress::LCL),
      b"ARG" => Ok(PredefinedAddress::ARG),
      b"THIS" => Ok(PredefinedAddress::THIS),
      b"THAT" => Ok(PredefinedAddress::THAT),
      b"R0" => Ok(PredefinedAddress::R0),
      b"R1" => Ok(PredefinedAddress::R1),
      b"R2" => Ok(PredefinedAddress::R2),
      b"R3" => Ok(PredefinedAddress::R3),
      b"R4" => Ok(PredefinedAddress::R4),
      b"R5" => Ok(PredefinedAddress::R5),
      b"R6" => Ok(PredefinedAddress::R6),
      b"R7" => Ok(PredefinedAddress::R7),
      b"R8" => Ok(PredefinedAddress::R8),
      b"R9" => Ok(PredefinedAddress::R9),
      b"R10" => Ok(PredefinedAddress::R10),
      b"R11" => Ok(PredefinedAddress::R11),
      b"R12" => Ok(PredefinedAddress::R12),
      b"R13" => Ok(PredefinedAddress::R13),
      b"R14" => Ok(PredefinedAddress::R14),
      b"R15" => Ok(PredefinedAddress::R15),
      b"SCREEN" => Ok(PredefinedAddress::SCREEN),
      b"KBD" => Ok(PredefinedAddress::KBD),
      _ => Err(()),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::PredefinedAddress;

  #[test]
  fn display() {
    assert_eq!(format!("{}", PredefinedAddress::SP), "SP");
    assert_eq!(format!("{}", PredefinedAddress::LCL), "LCL");
    assert_eq!(format!("{}", PredefinedAddress::ARG), "ARG");
    assert_eq!(format!("{}", PredefinedAddress::THIS), "THIS");
    assert_eq!(format!("{}", PredefinedAddress::THAT), "THAT");
    assert_eq!(format!("{}", PredefinedAddress::R0), "R0");
    assert_eq!(format!("{}", PredefinedAddress::R1), "R1");
    assert_eq!(format!("{}", PredefinedAddress::R2), "R2");
    assert_eq!(format!("{}", PredefinedAddress::R3), "R3");
    assert_eq!(format!("{}", PredefinedAddress::R4), "R4");
    assert_eq!(format!("{}", PredefinedAddress::R5), "R5");
    assert_eq!(format!("{}", PredefinedAddress::R6), "R6");
    assert_eq!(format!("{}", PredefinedAddress::R7), "R7");
    assert_eq!(format!("{}", PredefinedAddress::R8), "R8");
    assert_eq!(format!("{}", PredefinedAddress::R9), "R9");
    assert_eq!(format!("{}", PredefinedAddress::R10), "R10");
    assert_eq!(format!("{}", PredefinedAddress::R11), "R11");
    assert_eq!(format!("{}", PredefinedAddress::R12), "R12");
    assert_eq!(format!("{}", PredefinedAddress::R13), "R13");
    assert_eq!(format!("{}", PredefinedAddress::R14), "R14");
    assert_eq!(format!("{}", PredefinedAddress::R15), "R15");
    assert_eq!(format!("{}", PredefinedAddress::SCREEN), "SCREEN");
    assert_eq!(format!("{}", PredefinedAddress::KBD), "KBD");
  }

  #[test]
  fn try_from() {
    use std::convert::TryFrom;

    macro_rules! assert_predefined_address {
      ($text:expr, $result:expr) => {
        assert_eq!(PredefinedAddress::try_from($text.as_bytes()), Ok($result));
      };
    }

    assert_eq!(PredefinedAddress::try_from("".as_bytes()), Err(()));
    assert_eq!(PredefinedAddress::try_from("Foo".as_bytes()), Err(()));

    assert_predefined_address!("SP", PredefinedAddress::SP);
    assert_predefined_address!("LCL", PredefinedAddress::LCL);
    assert_predefined_address!("ARG", PredefinedAddress::ARG);
    assert_predefined_address!("THIS", PredefinedAddress::THIS);
    assert_predefined_address!("THAT", PredefinedAddress::THAT);
    assert_predefined_address!("R0", PredefinedAddress::R0);
    assert_predefined_address!("R1", PredefinedAddress::R1);
    assert_predefined_address!("R2", PredefinedAddress::R2);
    assert_predefined_address!("R3", PredefinedAddress::R3);
    assert_predefined_address!("R4", PredefinedAddress::R4);
    assert_predefined_address!("R5", PredefinedAddress::R5);
    assert_predefined_address!("R6", PredefinedAddress::R6);
    assert_predefined_address!("R7", PredefinedAddress::R7);
    assert_predefined_address!("R8", PredefinedAddress::R8);
    assert_predefined_address!("R9", PredefinedAddress::R9);
    assert_predefined_address!("R10", PredefinedAddress::R10);
    assert_predefined_address!("R11", PredefinedAddress::R11);
    assert_predefined_address!("R12", PredefinedAddress::R12);
    assert_predefined_address!("R13", PredefinedAddress::R13);
    assert_predefined_address!("R14", PredefinedAddress::R14);
    assert_predefined_address!("R15", PredefinedAddress::R15);
    assert_predefined_address!("SCREEN", PredefinedAddress::SCREEN);
    assert_predefined_address!("KBD", PredefinedAddress::KBD);
  }
}
