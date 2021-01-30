//! Structures related to HACK instructions.
//!
//! An [instruction](Inst) can represent different types of commands
//! in the HACK assembly language.

use crate::com::comp;
use crate::com::comp::Comp;
use crate::com::dest::Dest;
use crate::com::jump;
use crate::com::jump::Jump;
use crate::utils::buf::Buf;
use crate::utils::parser;

use std::convert::TryFrom;
use std::fmt;

use derive_more::Display;
use derive_more::From;

/// An instruction as defined by the HACK assembly reference.
///
/// An instruction consists of a [destination](Dest), a
/// [computation](Comp) and a [jump](Jump).
///
/// # impl `Into<u16>`
///
/// The binary representation is 16 bits wide where the three most
/// significant bits are `1` and the remaining 12 bits are the binary
/// representations of [Dest], [Comp] and [Jump] (from most
/// significant to least significant).
///
/// ## Examples
///
/// ```
/// use has::com::inst::Inst;
/// use has::com::dest::Dest;
/// use has::com::comp::Comp;
/// use has::com::jump::Jump;
///
/// let inst = Inst::new(Dest::D, Comp::DPlus1, Jump::Null).unwrap();
/// assert_eq!(u16::from(inst), 0b111_0011111_010_000);
///
/// let inst = Inst::new(Dest::Null, Comp::DPlus1, Jump::JEQ).unwrap();
/// assert_eq!(u16::from(inst), 0b111_0011111_000_010);
///
/// let inst = Inst::new(Dest::D, Comp::DPlus1, Jump::JEQ).unwrap();
/// assert_eq!(u16::from(inst), 0b111_0011111_010_010);
/// ```
///
/// # impl `Display`
///
/// ```
/// use has::com::inst::Inst;
/// use has::com::dest::Dest;
/// use has::com::comp::Comp;
/// use has::com::jump::Jump;
///
/// let inst = Inst::new(Dest::MD, Comp::DPlusA, Jump::JGT).unwrap();
/// assert_eq!(format!("{}", inst), "MD=D+A;JGT");
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Inst {
  /// The destination field.
  dest: Dest,
  /// The computation field.
  comp: Comp,
  /// The jump field.
  jump: Jump,
}

impl fmt::Display for Inst {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    if !self.dest.is_null() {
      write!(f, "{}=", self.dest)?;
    }

    write!(f, "{}", self.comp)?;

    if !self.jump.is_null() {
      write!(f, ";{}", self.jump)?;
    }

    Ok(())
  }
}

impl From<Inst> for u16 {
  fn from(inst: Inst) -> Self {
    0b111 << 13
      | u16::from(inst.comp()) << 6
      | u16::from(inst.dest()) << 3
      | u16::from(inst.jump())
  }
}

/// Errors when parsing an instruction from its compiled form.
#[derive(Display, Debug, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "Instruction decoding error: {}")]
pub enum DecodeErr {
  /// Invalid computation value.
  #[display(fmt = "`{:#b} ({})` is not a valid computation", _0, _0)]
  InvalidComp(u16),

  /// Invalid destination value.
  #[display(fmt = "`{:#b} ({})` is not a valid destination", _0, _0)]
  InvalidDest(u16),

  /// Invalid jump value.
  #[display(fmt = "`{:#b} ({})` is not a valid jump", _0, _0)]
  InvalidJump(u16),
}

impl TryFrom<u16> for Inst {
  type Error = DecodeErr;

  fn try_from(v: u16) -> Result<Self, Self::Error> {
    use DecodeErr::*;

    let comp_v = (v & 0b1111111000000) >> 6;
    let comp = Comp::try_from(comp_v).map_err(|_| InvalidComp(comp_v))?;

    let dest_v = (v & 0b111000) >> 3;
    let dest = Dest::try_from(dest_v).map_err(|_| InvalidDest(dest_v))?;

    let jump_v = v & 0b111;
    let jump = Jump::try_from(jump_v).map_err(|_| InvalidJump(jump_v))?;

    Ok(Self { dest, comp, jump })
  }
}

/// Error parsing or creating an instruction.
#[derive(Display, Debug, Clone, PartialEq, Eq, From)]
#[display(fmt = "Instruction error: {}")]
pub enum Err {
  /// An instruction must at least have a destination or a jump.
  #[display(fmt = "missing destination or jump")]
  #[from(ignore)]
  MissingDestJump,

  /// Invalid computation.
  #[display(fmt = "invalid computation: {}", _0)]
  InvalidComp(comp::Err),

  /// Invalid jump.
  #[display(fmt = "invalid jump: {}", _0)]
  InvalidJump(jump::Err),
}

impl Inst {
  /// Create a new instruction object.
  pub fn new(dest: Dest, comp: Comp, jump: Jump) -> Result<Self, Err> {
    if dest == Dest::Null && jump == Jump::Null {
      return Err(Err::MissingDestJump);
    }

    Ok(Self { dest, comp, jump })
  }

  /// Returns the [destination](Dest) of an instruction object.
  pub fn dest(&self) -> Dest {
    self.dest
  }

  /// Returns the [computation](Comp) of an instruction object.
  pub fn comp(&self) -> Comp {
    self.comp
  }

  /// Returns the [jump](Jump) of an instruction object.
  pub fn jump(&self) -> Jump {
    self.jump
  }
}

impl Inst {
  /// Read an instruction object from a buffer.
  ///
  /// Returns an instruction object, the remainder of the input buffer
  /// and the number of bytes that have been consumed for parsing.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::com::dest::Dest;
  /// use has::com::comp;
  /// use has::com::comp::Comp;
  /// use has::com::jump;
  /// use has::com::jump::Jump;
  /// use has::com::inst;
  /// use has::com::inst::Inst;
  ///
  /// let err = Err(inst::Err::InvalidComp(comp::Err::Unknown(String::from(""))));
  /// assert_eq!(Inst::read_from("".as_bytes()), err);
  ///
  /// let err = Err(inst::Err::InvalidComp(comp::Err::Unknown(String::from(""))));
  /// assert_eq!(Inst::read_from("Foo".as_bytes()), err);
  ///
  /// let err = Err(inst::Err::MissingDestJump);
  /// assert_eq!(Inst::read_from("D|A".as_bytes()), err);
  ///
  /// let err = Err(inst::Err::InvalidJump(jump::Err::Unknown(String::from(""))));
  /// assert_eq!(Inst::read_from("D|A;".as_bytes()), err);
  ///
  /// let err = Err(inst::Err::InvalidJump(jump::Err::Unknown(String::from("JJJ"))));
  /// assert_eq!(Inst::read_from("D|A;JJJ".as_bytes()), err);
  ///
  /// let inst = Inst::new(Dest::D, Comp::DPlusA, Jump::JGT).unwrap();
  /// let expected = (inst, "".as_bytes(), 9);
  /// assert_eq!(Inst::read_from("D=D+A;JGT".as_bytes()), Ok(expected));
  ///
  /// let inst = Inst::new(Dest::Null, Comp::DPlusA, Jump::JGT).unwrap();
  /// let expected = (inst, "".as_bytes(), 7);
  /// assert_eq!(Inst::read_from("D+A;JGT".as_bytes()), Ok(expected));
  ///
  /// let inst = Inst::new(Dest::D, Comp::DPlusA, Jump::Null).unwrap();
  /// let expected = (inst, "".as_bytes(), 5);
  /// assert_eq!(Inst::read_from("D=D+A".as_bytes()), Ok(expected));
  /// ```
  pub fn read_from(buf: Buf) -> Result<(Self, Buf, usize), Err> {
    let mut inst_len = 0;

    let (dest, buf, _) = if let Ok((dest, rem, len)) = Dest::read_from(buf) {
      if let Some((_, rem)) = parser::read_one(rem, |b| b == b'=') {
        inst_len += len + 1;
        (dest, rem, len)
      } else {
        (Dest::Null, buf, 0)
      }
    } else {
      (Dest::Null, buf, 0)
    };

    let (comp, buf, len) = Comp::read_from(buf)?;
    inst_len += len;

    let buf = if let Some((_, buf)) = parser::read_one(buf, |b| b == b';') {
      let (jump, rem, len) = Jump::read_from(buf)?;
      inst_len += len + 1;
      return Ok((Inst::new(dest, comp, jump)?, rem, inst_len));
    } else {
      buf
    };

    Ok((Inst::new(dest, comp, Jump::Null)?, buf, inst_len))
  }
}
