//! Predefined symbols for the HACK assembly language.

use crate::Buf;
use derive_more::Display;
use std::convert::TryFrom;

/// Predefined symbols as defined by the HACK assembly reference.
///
/// The binary representation is 15 bits wide and can fit in an
/// A-instruction.
///
/// # Examples
///
/// ```
/// use has::hack::Sym;
/// use std::convert::TryFrom;
///
/// let sym = Sym::LCL;
/// assert_eq!(u16::from(sym), 0x0001);
/// assert_eq!(format!("{}", sym), "LCL");
/// ```
#[derive(Display, Debug, PartialEq, Eq, Clone, Copy)]
pub enum Sym {
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

/// Serialize a [Sym] object to [u16].
///
/// # Examples
///
/// ```
/// use has::hack::Sym;
///
/// assert_eq!(u16::from(Sym::SP),     0x0000);
/// assert_eq!(u16::from(Sym::LCL),    0x0001);
/// assert_eq!(u16::from(Sym::ARG),    0x0002);
/// assert_eq!(u16::from(Sym::THIS),   0x0003);
/// assert_eq!(u16::from(Sym::THAT),   0x0004);
/// assert_eq!(u16::from(Sym::R0),     0x0000);
/// assert_eq!(u16::from(Sym::R1),     0x0001);
/// assert_eq!(u16::from(Sym::R2),     0x0002);
/// assert_eq!(u16::from(Sym::R3),     0x0003);
/// assert_eq!(u16::from(Sym::R4),     0x0004);
/// assert_eq!(u16::from(Sym::R5),     0x0005);
/// assert_eq!(u16::from(Sym::R6),     0x0006);
/// assert_eq!(u16::from(Sym::R7),     0x0007);
/// assert_eq!(u16::from(Sym::R8),     0x0008);
/// assert_eq!(u16::from(Sym::R9),     0x0009);
/// assert_eq!(u16::from(Sym::R10),    0x000A);
/// assert_eq!(u16::from(Sym::R11),    0x000B);
/// assert_eq!(u16::from(Sym::R12),    0x000C);
/// assert_eq!(u16::from(Sym::R13),    0x000D);
/// assert_eq!(u16::from(Sym::R14),    0x000E);
/// assert_eq!(u16::from(Sym::R15),    0x000F);
/// assert_eq!(u16::from(Sym::SCREEN), 0x4000);
/// assert_eq!(u16::from(Sym::KBD),    0x6000);
/// ```
impl From<Sym> for u16 {
  fn from(sym: Sym) -> Self {
    match sym {
      Sym::SP => 0x0000,
      Sym::LCL => 0x0001,
      Sym::ARG => 0x0002,
      Sym::THIS => 0x0003,
      Sym::THAT => 0x0004,
      Sym::R0 => 0x0000,
      Sym::R1 => 0x0001,
      Sym::R2 => 0x0002,
      Sym::R3 => 0x0003,
      Sym::R4 => 0x0004,
      Sym::R5 => 0x0005,
      Sym::R6 => 0x0006,
      Sym::R7 => 0x0007,
      Sym::R8 => 0x0008,
      Sym::R9 => 0x0009,
      Sym::R10 => 0x000A,
      Sym::R11 => 0x000B,
      Sym::R12 => 0x000C,
      Sym::R13 => 0x000D,
      Sym::R14 => 0x000E,
      Sym::R15 => 0x000F,
      Sym::SCREEN => 0x4000,
      Sym::KBD => 0x6000,
    }
  }
}

/// Parse a [Sym] object from a (byte buffer)(Buf).
///
/// An unrecognized input produces an `Err(())`.
///
/// # Examples
///
/// ```
/// use has::hack::Sym;
/// use std::convert::TryFrom;
///
/// assert_eq!(Sym::try_from("".as_bytes()),       Err(()));
/// assert_eq!(Sym::try_from("Foo".as_bytes()),    Err(()));
///
/// assert_eq!(Sym::try_from("SP".as_bytes()),     Ok(Sym::SP));
/// assert_eq!(Sym::try_from("LCL".as_bytes()),    Ok(Sym::LCL));
/// assert_eq!(Sym::try_from("ARG".as_bytes()),    Ok(Sym::ARG));
/// assert_eq!(Sym::try_from("THIS".as_bytes()),   Ok(Sym::THIS));
/// assert_eq!(Sym::try_from("THAT".as_bytes()),   Ok(Sym::THAT));
/// assert_eq!(Sym::try_from("R0".as_bytes()),     Ok(Sym::R0));
/// assert_eq!(Sym::try_from("R1".as_bytes()),     Ok(Sym::R1));
/// assert_eq!(Sym::try_from("R2".as_bytes()),     Ok(Sym::R2));
/// assert_eq!(Sym::try_from("R3".as_bytes()),     Ok(Sym::R3));
/// assert_eq!(Sym::try_from("R4".as_bytes()),     Ok(Sym::R4));
/// assert_eq!(Sym::try_from("R5".as_bytes()),     Ok(Sym::R5));
/// assert_eq!(Sym::try_from("R6".as_bytes()),     Ok(Sym::R6));
/// assert_eq!(Sym::try_from("R7".as_bytes()),     Ok(Sym::R7));
/// assert_eq!(Sym::try_from("R8".as_bytes()),     Ok(Sym::R8));
/// assert_eq!(Sym::try_from("R9".as_bytes()),     Ok(Sym::R9));
/// assert_eq!(Sym::try_from("R10".as_bytes()),    Ok(Sym::R10));
/// assert_eq!(Sym::try_from("R11".as_bytes()),    Ok(Sym::R11));
/// assert_eq!(Sym::try_from("R12".as_bytes()),    Ok(Sym::R12));
/// assert_eq!(Sym::try_from("R13".as_bytes()),    Ok(Sym::R13));
/// assert_eq!(Sym::try_from("R14".as_bytes()),    Ok(Sym::R14));
/// assert_eq!(Sym::try_from("R15".as_bytes()),    Ok(Sym::R15));
/// assert_eq!(Sym::try_from("SCREEN".as_bytes()), Ok(Sym::SCREEN));
/// assert_eq!(Sym::try_from("KBD".as_bytes()),    Ok(Sym::KBD));
/// ```
impl TryFrom<Buf<'_>> for Sym {
  type Error = ();

  fn try_from(buf: Buf) -> Result<Self, Self::Error> {
    match buf {
      b"SP" => Ok(Sym::SP),
      b"LCL" => Ok(Sym::LCL),
      b"ARG" => Ok(Sym::ARG),
      b"THIS" => Ok(Sym::THIS),
      b"THAT" => Ok(Sym::THAT),
      b"R0" => Ok(Sym::R0),
      b"R1" => Ok(Sym::R1),
      b"R2" => Ok(Sym::R2),
      b"R3" => Ok(Sym::R3),
      b"R4" => Ok(Sym::R4),
      b"R5" => Ok(Sym::R5),
      b"R6" => Ok(Sym::R6),
      b"R7" => Ok(Sym::R7),
      b"R8" => Ok(Sym::R8),
      b"R9" => Ok(Sym::R9),
      b"R10" => Ok(Sym::R10),
      b"R11" => Ok(Sym::R11),
      b"R12" => Ok(Sym::R12),
      b"R13" => Ok(Sym::R13),
      b"R14" => Ok(Sym::R14),
      b"R15" => Ok(Sym::R15),
      b"SCREEN" => Ok(Sym::SCREEN),
      b"KBD" => Ok(Sym::KBD),
      _ => Err(()),
    }
  }
}

#[cfg(test)]
mod tests {
  #[test]
  fn display() {
    use crate::hack::Sym;

    assert_eq!(format!("{}", Sym::SP), "SP");
    assert_eq!(format!("{}", Sym::LCL), "LCL");
    assert_eq!(format!("{}", Sym::ARG), "ARG");
    assert_eq!(format!("{}", Sym::THIS), "THIS");
    assert_eq!(format!("{}", Sym::THAT), "THAT");
    assert_eq!(format!("{}", Sym::R0), "R0");
    assert_eq!(format!("{}", Sym::R1), "R1");
    assert_eq!(format!("{}", Sym::R2), "R2");
    assert_eq!(format!("{}", Sym::R3), "R3");
    assert_eq!(format!("{}", Sym::R4), "R4");
    assert_eq!(format!("{}", Sym::R5), "R5");
    assert_eq!(format!("{}", Sym::R6), "R6");
    assert_eq!(format!("{}", Sym::R7), "R7");
    assert_eq!(format!("{}", Sym::R8), "R8");
    assert_eq!(format!("{}", Sym::R9), "R9");
    assert_eq!(format!("{}", Sym::R10), "R10");
    assert_eq!(format!("{}", Sym::R11), "R11");
    assert_eq!(format!("{}", Sym::R12), "R12");
    assert_eq!(format!("{}", Sym::R13), "R13");
    assert_eq!(format!("{}", Sym::R14), "R14");
    assert_eq!(format!("{}", Sym::R15), "R15");
    assert_eq!(format!("{}", Sym::SCREEN), "SCREEN");
    assert_eq!(format!("{}", Sym::KBD), "KBD");
  }
}
