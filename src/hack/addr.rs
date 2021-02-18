//! Numerical and named addresses for the HACK assembly language.

use crate::hack::Label;
use crate::hack::Sym;
use crate::parser;
use crate::Buf;
use crate::Byte;
use atoi::FromRadix10Checked;
use derive_more::Display;
use derive_more::From;
use std::convert::TryFrom;

/// Address instructions (A-instructions) as defined by the HACK
/// assembly reference.
///
/// The binary representation is 16 bits wide as defined by the HACK
/// assembly language. The most significant bit is always `0` to
/// signify an A-instruction and the effective addressing width is the
/// remaining 15 bits.
///
/// Numerical address objects can be created from [u16] values and
/// named address objects from (labels)[Label] or (symbols)[Sym].
///
/// # Examples
///
/// ```
/// use has::hack::Addr;
/// use has::hack::AddrErr;
/// use has::hack::Sym;
/// use has::hack::Label;
/// use std::convert::TryFrom;
///
/// let num = 25;
/// assert_eq!(Addr::try_from(num), Ok(Addr::Num(25)));
///
/// let sym = Sym::LCL;
/// assert_eq!(Addr::from(sym), Addr::Sym(sym));
///
/// let label = Label::try_from("label".as_bytes()).unwrap();
/// assert_eq!(Addr::from(label), Addr::Label(label));
/// ```
#[derive(Display, Debug, PartialEq, Eq, Clone, Copy, From)]
#[display(fmt = "@{}")]
pub enum Addr<'b> {
  /// Numerical address.
  #[display(fmt = "{}", _0)]
  #[from(ignore)]
  Num(u16),

  /// User-defined label address.
  #[display(fmt = "{}", _0)]
  Label(Label<'b>),

  /// Predefined symbol address.
  #[display(fmt = "{}", _0)]
  Sym(Sym),
}

/// Build an [Addr] object from a [u16] address value.
///
/// If the value is outside the unsigned 15-bits range (> 32767), an
/// `Err(AddrErr)` is returned.
///
/// # Examples
///
/// ```
/// use has::hack::Addr;
/// use has::hack::AddrErr;
/// use has::hack::Sym;
/// use std::convert::TryFrom;
///
/// assert_eq!(Addr::try_from(25), Ok(Addr::Num(25)));
/// assert_eq!(Addr::try_from(32768), Err(AddrErr::Range(32768)));
/// ```
impl TryFrom<u16> for Addr<'_> {
  type Error = Err;

  fn try_from(addr: u16) -> Result<Self, Self::Error> {
    // 32767 (15 bits of address value)
    if addr > 32767 {
      return Err(Err::Range(addr));
    }

    Ok(Self::Num(addr))
  }
}

/// Errors when parsing an address.
#[derive(Display, Debug, Clone, PartialEq, Eq)]
#[display(fmt = "Address error: {}")]
pub enum Err {
  /// Value is not a number or is out of the 15-bits range.
  #[display(fmt = "invalid numerical address `{}`", _0)]
  InvalidNum(String),

  /// Value is outside the 15-bits range.
  #[display(fmt = "address `{}` is outside the 15-bits range", _0)]
  Range(u16),

  /// Invalid label name.
  #[display(fmt = "invalid named address `{}`", _0)]
  InvalidName(String),

  /// Converting byte buffers to UTF-8 strings.
  #[display(fmt = "named address `{:?}` is invalid: {}", _0, _1)]
  Convert(Vec<Byte>, std::string::FromUtf8Error),
}

impl Err {
  /// Constructs an `Err::InvalidNum` variant.
  pub fn invalid_num(buf: Buf) -> Self {
    match String::from_utf8(Vec::from(buf)) {
      Ok(num) => Err::InvalidNum(num),
      Err(e) => Err::Convert(Vec::from(buf), e),
    }
  }

  /// Constructs an `Err::InvalidName` variant.
  pub fn invalid_name(buf: Buf) -> Self {
    match String::from_utf8(Vec::from(buf)) {
      Ok(num) => Err::InvalidName(num),
      Err(e) => Err::Convert(Vec::from(buf), e),
    }
  }
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
  /// use has::hack::AddrErr;
  /// use has::hack::Addr;
  /// use has::hack::Label;
  /// use has::hack::Sym;
  /// use std::convert::TryFrom;
  ///
  /// let expected = AddrErr::InvalidName(String::from(""));
  /// assert_eq!(Addr::read_from("".as_bytes()), Err(expected));
  ///
  /// let expected = AddrErr::InvalidName(String::from("%Foo"));
  /// assert_eq!(Addr::read_from("%Foo".as_bytes()), Err(expected));
  ///
  /// let expected = AddrErr::InvalidNum(String::from("123Foo"));
  /// assert_eq!(Addr::read_from("123Foo".as_bytes()), Err(expected));
  ///
  /// let expected = (Addr::Num(123), "".as_bytes(), 3);
  /// assert_eq!(Addr::read_from("123".as_bytes()), Ok(expected));
  ///
  /// let label = Label::try_from("Foo".as_bytes()).unwrap();
  /// let expected = (Addr::Label(label), "".as_bytes(), 3);
  /// assert_eq!(Addr::read_from("Foo".as_bytes()), Ok(expected));
  ///
  /// let label = Label::try_from("F_B".as_bytes()).unwrap();
  /// let expected = (Addr::Label(label), "".as_bytes(), 3);
  /// assert_eq!(Addr::read_from("F_B".as_bytes()), Ok(expected));
  ///
  /// let label = Label::try_from("_FB".as_bytes()).unwrap();
  /// let expected = (Addr::Label(label), "".as_bytes(), 3);
  /// assert_eq!(Addr::read_from("_FB".as_bytes()), Ok(expected));
  ///
  /// let sym = Sym::try_from("LCL".as_bytes()).unwrap();
  /// let expected = (Addr::Sym(sym), "".as_bytes(), 3);
  /// assert_eq!(Addr::read_from("LCL".as_bytes()), Ok(expected));
  ///
  /// let sym = Sym::try_from("R0".as_bytes()).unwrap();
  /// let expected = (Addr::Sym(sym), "".as_bytes(), 2);
  /// assert_eq!(Addr::read_from("R0".as_bytes()), Ok(expected));
  /// ```
  pub fn read_from(buf: Buf<'b>) -> Result<(Self, Buf<'b>, usize), Err> {
    if parser::read_digit(buf).is_some() {
      let (num, rem) = parser::read_until_ws(buf);

      match u16::from_radix_10_checked(num) {
        (Some(addr), used) if used == num.len() => {
          let addr = Self::try_from(addr).map_err(|_| Err::Range(addr))?;
          return Ok((addr, rem, num.len()));
        }
        (_, _) => return Err(Err::invalid_num(num)),
      }
    }

    let (txt, rem) = parser::read_until_ws(buf);

    if let Ok(sym) = Sym::try_from(txt) {
      return Ok((Self::from(sym), rem, txt.len()));
    }

    if let Ok(label) = Label::try_from(txt) {
      return Ok((Self::from(label), rem, txt.len()));
    }

    Err(Err::invalid_name(txt))
  }
}
