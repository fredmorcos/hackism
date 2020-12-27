use std::convert::TryFrom;
use std::fmt;

use crate::label::Label;
use crate::symbol::Symbol;
use crate::utils;
use crate::utils::Buf;

use atoi::FromRadix10Checked;

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
/// use has::addr::Addr;
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
/// use has::addr::Addr;
/// use has::label::Label;
/// use std::convert::TryFrom;
///
/// assert_eq!(Addr::from(Label::try_from(&b"foobar1"[..]).unwrap()),
///            Addr::Label(Label::try_from(&b"foobar1"[..]).unwrap()));
/// ```
///
/// # impl `From<Symbol>`
///
/// Creates an [Addr::Symbol] object from a [Symbol].
///
/// ## Examples
///
/// ```
/// use has::addr::Addr;
/// use has::symbol::Symbol;
///
/// assert_eq!(Addr::from(Symbol::LCL), Addr::Symbol(Symbol::LCL));
/// ```
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Addr<'b> {
  Num(u16),
  Label(Label<'b>),
  Symbol(Symbol),
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

impl From<Symbol> for Addr<'_> {
  fn from(symbol: Symbol) -> Self {
    Addr::Symbol(symbol)
  }
}

impl fmt::Display for Addr<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Addr::Num(addr) => write!(f, "@{}", addr),
      Addr::Label(label) => write!(f, "@{}", label),
      Addr::Symbol(symbol) => write!(f, "@{}", symbol),
    }
  }
}

/// Errors when parsing addresses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Err {
  /// Value is not a number or is out of the 15-bits range.
  InvalidNum,
  /// Invalid label name.
  InvalidLabel,
}

impl<'b> Addr<'b> {
  /// Read an address object from a buffer.
  ///
  /// Returns an address object, the remainder of the input buffer and
  /// the number of bytes that have been consumed for parsing.
  ///
  /// # Examples
  ///
  /// ```
  /// use has::addr;
  /// use has::addr::Addr;
  /// use has::label::Label;
  /// use has::symbol::Symbol;
  /// use std::convert::TryFrom;
  ///
  /// assert_eq!(Addr::read_from("".as_bytes()), Err(addr::Err::InvalidLabel));
  /// assert_eq!(Addr::read_from("123Foo".as_bytes()), Err(addr::Err::InvalidNum));
  /// assert_eq!(Addr::read_from("%Foo".as_bytes()), Err(addr::Err::InvalidLabel));
  ///
  /// assert_eq!(Addr::read_from("123".as_bytes()),
  ///            Ok((Addr::Num(123), "".as_bytes(), 3)));
  /// assert_eq!(Addr::read_from("Foo".as_bytes()),
  ///            Ok((Addr::Label(Label::try_from("Foo".as_bytes()).unwrap()), "".as_bytes(), 3)));
  /// assert_eq!(Addr::read_from("F_B".as_bytes()),
  ///            Ok((Addr::Label(Label::try_from("F_B".as_bytes()).unwrap()), "".as_bytes(), 3)));
  /// assert_eq!(Addr::read_from("_FB".as_bytes()),
  ///            Ok((Addr::Label(Label::try_from("_FB".as_bytes()).unwrap()), "".as_bytes(), 3)));
  ///
  /// assert_eq!(Addr::read_from("LCL".as_bytes()),
  ///            Ok((Addr::Symbol(Symbol::try_from("LCL".as_bytes()).unwrap()), "".as_bytes(), 3)));
  /// assert_eq!(Addr::read_from("R0".as_bytes()),
  ///            Ok((Addr::Symbol(Symbol::try_from("R0".as_bytes()).unwrap()), "".as_bytes(), 2)));
  /// ```
  pub fn read_from(buf: Buf<'b>) -> Result<(Self, Buf<'b>, usize), Err> {
    if let Some((_, _)) = utils::read_one(buf, |b| b.is_ascii_digit()) {
      let (num, rem) = utils::read_until_ws(buf);

      match u16::from_radix_10_checked(num) {
        (Some(addr), used) if used == num.len() => {
          return Ok((Self::try_from(addr).map_err(|_| Err::InvalidNum)?, rem, num.len()))
        }
        (_, _) => return Err(Err::InvalidNum),
      }
    }

    let (txt, rem) = utils::read_until_ws(buf);

    if let Ok(symbol) = Symbol::try_from(txt) {
      return Ok((Self::from(symbol), rem, txt.len()));
    }

    if let Ok(label) = Label::try_from(txt) {
      return Ok((Self::from(label), rem, txt.len()));
    }

    Err(Err::InvalidLabel)
  }
}
