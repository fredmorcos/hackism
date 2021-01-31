//! HACK predefined labels.

use std::convert::TryFrom;

use crate::utils::buf::Buf;

use derive_more::Display;

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
/// use has::com::symbol::Symbol;
///
/// assert_eq!(u16::from(Symbol::SP),     0x0000);
/// assert_eq!(u16::from(Symbol::LCL),    0x0001);
/// assert_eq!(u16::from(Symbol::ARG),    0x0002);
/// assert_eq!(u16::from(Symbol::THIS),   0x0003);
/// assert_eq!(u16::from(Symbol::THAT),   0x0004);
/// assert_eq!(u16::from(Symbol::R0),     0x0000);
/// assert_eq!(u16::from(Symbol::R1),     0x0001);
/// assert_eq!(u16::from(Symbol::R2),     0x0002);
/// assert_eq!(u16::from(Symbol::R3),     0x0003);
/// assert_eq!(u16::from(Symbol::R4),     0x0004);
/// assert_eq!(u16::from(Symbol::R5),     0x0005);
/// assert_eq!(u16::from(Symbol::R6),     0x0006);
/// assert_eq!(u16::from(Symbol::R7),     0x0007);
/// assert_eq!(u16::from(Symbol::R8),     0x0008);
/// assert_eq!(u16::from(Symbol::R9),     0x0009);
/// assert_eq!(u16::from(Symbol::R10),    0x000A);
/// assert_eq!(u16::from(Symbol::R11),    0x000B);
/// assert_eq!(u16::from(Symbol::R12),    0x000C);
/// assert_eq!(u16::from(Symbol::R13),    0x000D);
/// assert_eq!(u16::from(Symbol::R14),    0x000E);
/// assert_eq!(u16::from(Symbol::R15),    0x000F);
/// assert_eq!(u16::from(Symbol::SCREEN), 0x4000);
/// assert_eq!(u16::from(Symbol::KBD),    0x6000);
/// ```
///
/// # impl `TryFrom<&[u8]>` (`type Error = ()`)
///
/// A [Symbol] object can be created from a slice of bytes. A
/// `Result::Err(())` is returned if the input sequence is not
/// recognized.
///
/// ## Examples
///
/// ```
/// use has::com::symbol::Symbol;
///
/// use std::convert::TryFrom;
///
/// assert_eq!(Symbol::try_from(&b""[..]),    Err(()));
/// assert_eq!(Symbol::try_from(&b"Foo"[..]), Err(()));
///
/// assert_eq!(Symbol::try_from(&b"SP"[..]),     Ok(Symbol::SP));
/// assert_eq!(Symbol::try_from(&b"LCL"[..]),    Ok(Symbol::LCL));
/// assert_eq!(Symbol::try_from(&b"ARG"[..]),    Ok(Symbol::ARG));
/// assert_eq!(Symbol::try_from(&b"THIS"[..]),   Ok(Symbol::THIS));
/// assert_eq!(Symbol::try_from(&b"THAT"[..]),   Ok(Symbol::THAT));
/// assert_eq!(Symbol::try_from(&b"R0"[..]),     Ok(Symbol::R0));
/// assert_eq!(Symbol::try_from(&b"R1"[..]),     Ok(Symbol::R1));
/// assert_eq!(Symbol::try_from(&b"R2"[..]),     Ok(Symbol::R2));
/// assert_eq!(Symbol::try_from(&b"R3"[..]),     Ok(Symbol::R3));
/// assert_eq!(Symbol::try_from(&b"R4"[..]),     Ok(Symbol::R4));
/// assert_eq!(Symbol::try_from(&b"R5"[..]),     Ok(Symbol::R5));
/// assert_eq!(Symbol::try_from(&b"R6"[..]),     Ok(Symbol::R6));
/// assert_eq!(Symbol::try_from(&b"R7"[..]),     Ok(Symbol::R7));
/// assert_eq!(Symbol::try_from(&b"R8"[..]),     Ok(Symbol::R8));
/// assert_eq!(Symbol::try_from(&b"R9"[..]),     Ok(Symbol::R9));
/// assert_eq!(Symbol::try_from(&b"R10"[..]),    Ok(Symbol::R10));
/// assert_eq!(Symbol::try_from(&b"R11"[..]),    Ok(Symbol::R11));
/// assert_eq!(Symbol::try_from(&b"R12"[..]),    Ok(Symbol::R12));
/// assert_eq!(Symbol::try_from(&b"R13"[..]),    Ok(Symbol::R13));
/// assert_eq!(Symbol::try_from(&b"R14"[..]),    Ok(Symbol::R14));
/// assert_eq!(Symbol::try_from(&b"R15"[..]),    Ok(Symbol::R15));
/// assert_eq!(Symbol::try_from(&b"SCREEN"[..]), Ok(Symbol::SCREEN));
/// assert_eq!(Symbol::try_from(&b"KBD"[..]),    Ok(Symbol::KBD));
/// ```
///
/// # impl `Display`
///
/// ```
/// use has::com::symbol::Symbol;
///
/// assert_eq!(format!("{}", Symbol::SP),     "SP");
/// assert_eq!(format!("{}", Symbol::LCL),    "LCL");
/// assert_eq!(format!("{}", Symbol::ARG),    "ARG");
/// assert_eq!(format!("{}", Symbol::THIS),   "THIS");
/// assert_eq!(format!("{}", Symbol::THAT),   "THAT");
/// assert_eq!(format!("{}", Symbol::R0),     "R0");
/// assert_eq!(format!("{}", Symbol::R1),     "R1");
/// assert_eq!(format!("{}", Symbol::R2),     "R2");
/// assert_eq!(format!("{}", Symbol::R3),     "R3");
/// assert_eq!(format!("{}", Symbol::R4),     "R4");
/// assert_eq!(format!("{}", Symbol::R5),     "R5");
/// assert_eq!(format!("{}", Symbol::R6),     "R6");
/// assert_eq!(format!("{}", Symbol::R7),     "R7");
/// assert_eq!(format!("{}", Symbol::R8),     "R8");
/// assert_eq!(format!("{}", Symbol::R9),     "R9");
/// assert_eq!(format!("{}", Symbol::R10),    "R10");
/// assert_eq!(format!("{}", Symbol::R11),    "R11");
/// assert_eq!(format!("{}", Symbol::R12),    "R12");
/// assert_eq!(format!("{}", Symbol::R13),    "R13");
/// assert_eq!(format!("{}", Symbol::R14),    "R14");
/// assert_eq!(format!("{}", Symbol::R15),    "R15");
/// assert_eq!(format!("{}", Symbol::SCREEN), "SCREEN");
/// assert_eq!(format!("{}", Symbol::KBD),    "KBD");
/// ```
#[derive(Display, Debug, PartialEq, Eq, Clone, Copy)]
pub enum Symbol {
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

impl From<Symbol> for u16 {
  fn from(symbol: Symbol) -> Self {
    match symbol {
      Symbol::SP => 0x0000,
      Symbol::LCL => 0x0001,
      Symbol::ARG => 0x0002,
      Symbol::THIS => 0x0003,
      Symbol::THAT => 0x0004,
      Symbol::R0 => 0x0000,
      Symbol::R1 => 0x0001,
      Symbol::R2 => 0x0002,
      Symbol::R3 => 0x0003,
      Symbol::R4 => 0x0004,
      Symbol::R5 => 0x0005,
      Symbol::R6 => 0x0006,
      Symbol::R7 => 0x0007,
      Symbol::R8 => 0x0008,
      Symbol::R9 => 0x0009,
      Symbol::R10 => 0x000A,
      Symbol::R11 => 0x000B,
      Symbol::R12 => 0x000C,
      Symbol::R13 => 0x000D,
      Symbol::R14 => 0x000E,
      Symbol::R15 => 0x000F,
      Symbol::SCREEN => 0x4000,
      Symbol::KBD => 0x6000,
    }
  }
}

impl TryFrom<Buf<'_>> for Symbol {
  type Error = ();

  fn try_from(buf: Buf) -> Result<Self, Self::Error> {
    match buf {
      b"SP" => Ok(Symbol::SP),
      b"LCL" => Ok(Symbol::LCL),
      b"ARG" => Ok(Symbol::ARG),
      b"THIS" => Ok(Symbol::THIS),
      b"THAT" => Ok(Symbol::THAT),
      b"R0" => Ok(Symbol::R0),
      b"R1" => Ok(Symbol::R1),
      b"R2" => Ok(Symbol::R2),
      b"R3" => Ok(Symbol::R3),
      b"R4" => Ok(Symbol::R4),
      b"R5" => Ok(Symbol::R5),
      b"R6" => Ok(Symbol::R6),
      b"R7" => Ok(Symbol::R7),
      b"R8" => Ok(Symbol::R8),
      b"R9" => Ok(Symbol::R9),
      b"R10" => Ok(Symbol::R10),
      b"R11" => Ok(Symbol::R11),
      b"R12" => Ok(Symbol::R12),
      b"R13" => Ok(Symbol::R13),
      b"R14" => Ok(Symbol::R14),
      b"R15" => Ok(Symbol::R15),
      b"SCREEN" => Ok(Symbol::SCREEN),
      b"KBD" => Ok(Symbol::KBD),
      _ => Err(()),
    }
  }
}
