//! Structures related to HACK instructions.
//!
//! An [instruction](Inst) can represent different types of commands
//! in the HACK assembly language.

use crate::com::comp::Comp;
use crate::com::dest::Dest;
use crate::com::jump::Jump;
use crate::utils;
use crate::utils::Buf;

use std::convert::TryFrom;
use std::fmt;

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
  dest: Dest,
  comp: Comp,
  jump: Jump,
}

impl From<Inst> for u16 {
  fn from(inst: Inst) -> Self {
    0b111 << 13
      | u16::from(inst.comp()) << 6
      | u16::from(inst.dest()) << 3
      | u16::from(inst.jump())
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecodeErr {
  InvalidComp,
  InvalidDest,
  InvalidJump,
}

impl fmt::Display for DecodeErr {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      DecodeErr::InvalidComp => write!(f, "invalid computation"),
      DecodeErr::InvalidDest => write!(f, "invalid destination"),
      DecodeErr::InvalidJump => write!(f, "invalid jump"),
    }
  }
}

impl TryFrom<u16> for Inst {
  type Error = DecodeErr;

  fn try_from(v: u16) -> Result<Self, Self::Error> {
    use DecodeErr::*;

    let comp = Comp::try_from((v & 0b1111111000000) >> 6).map_err(|_| InvalidComp)?;
    let dest = Dest::try_from((v & 0b111000) >> 3).map_err(|_| InvalidDest)?;
    let jump = Jump::try_from(v & 0b111).map_err(|_| InvalidJump)?;

    Ok(Self { dest, comp, jump })
  }
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

/// Error parsing or creating an instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Err {
  /// An instruction must at least have a destination or a jump.
  MissingDestJump,
  /// Invalid computation.
  InvalidComp,
  /// Invalid jump.
  InvalidJump,
}

impl fmt::Display for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Err::MissingDestJump => write!(f, "missing destination or jump"),
      Err::InvalidComp => write!(f, "invalid computation"),
      Err::InvalidJump => write!(f, "invalid jump"),
    }
  }
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
  /// use has::com::comp::Comp;
  /// use has::com::jump::Jump;
  /// use has::com::inst;
  /// use has::com::inst::Inst;
  ///
  /// assert_eq!(Inst::read_from("".as_bytes()), Err(inst::Err::InvalidComp));
  /// assert_eq!(Inst::read_from("Foo".as_bytes()), Err(inst::Err::InvalidComp));
  /// assert_eq!(Inst::read_from("D|A".as_bytes()), Err(inst::Err::MissingDestJump));
  /// assert_eq!(Inst::read_from("D|A;".as_bytes()), Err(inst::Err::InvalidJump));
  /// assert_eq!(Inst::read_from("D|A;JJJ".as_bytes()), Err(inst::Err::InvalidJump));
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
      if let Some((_, rem)) = utils::read_one(rem, |b| b == b'=') {
        inst_len += len + 1;
        (dest, rem, len)
      } else {
        (Dest::Null, buf, 0)
      }
    } else {
      (Dest::Null, buf, 0)
    };

    let (comp, buf, _) = if let Ok((comp, rem, len)) = Comp::read_from(buf) {
      inst_len += len;
      (comp, rem, len)
    } else {
      return Err(Err::InvalidComp);
    };

    let buf = if let Some((_, buf)) = utils::read_one(buf, |b| b == b';') {
      if let Ok((jump, rem, len)) = Jump::read_from(buf) {
        inst_len += len + 1;
        return Ok((Inst::new(dest, comp, jump)?, rem, inst_len));
      } else {
        return Err(Err::InvalidJump);
      }
    } else {
      buf
    };

    Ok((Inst::new(dest, comp, Jump::Null)?, buf, inst_len))
  }
}
