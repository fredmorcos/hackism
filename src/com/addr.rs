use std::convert::TryFrom;

use crate::com::label::Label;
use crate::com::symbol::Symbol;
use crate::utils::buf::Buf;
use crate::utils::buf::Byte;
use crate::utils::parser;

use atoi::FromRadix10Checked;
use derive_more::Display;
use derive_more::From;

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
/// use has::com::addr;
/// use has::com::addr::Addr;
/// use has::com::symbol::Symbol;
///
/// use std::convert::TryFrom;
///
/// assert_eq!(Addr::try_from(25), Ok(Addr::Num(25)));
/// assert_eq!(Addr::try_from(32768), Err(addr::Err::Range(32768)));
/// ```
///
/// # impl `From<Label>`
///
/// Creates an [Addr::Label] object from a [Label].
///
/// ## Examples
///
/// ```
/// use has::com::addr::Addr;
/// use has::com::label::Label;
///
/// use std::convert::TryFrom;
///
/// let label = Label::try_from(&b"foobar1"[..]).unwrap();
/// assert_eq!(Addr::from(label.clone()), Addr::Label(label));
/// ```
///
/// # impl `From<Symbol>`
///
/// Creates an [Addr::Symbol] object from a [Symbol].
///
/// ## Examples
///
/// ```
/// use has::com::addr::Addr;
/// use has::com::symbol::Symbol;
///
/// assert_eq!(Addr::from(Symbol::LCL), Addr::Symbol(Symbol::LCL));
/// ```
#[derive(Display, Debug, PartialEq, Eq, Clone, From)]
#[display(fmt = "@{}")]
pub enum Addr<'b> {
  /// Numerical address
  #[display(fmt = "{}", _0)]
  #[from(ignore)]
  Num(u16),

  /// User-defined label address.
  #[display(fmt = "{}", _0)]
  Label(Label<'b>),

  /// Predefined symbol address.
  #[display(fmt = "{}", _0)]
  Symbol(Symbol),
}

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
  /// use has::com::addr;
  /// use has::com::addr::Addr;
  /// use has::com::label::Label;
  /// use has::com::symbol::Symbol;
  ///
  /// use std::convert::TryFrom;
  ///
  /// assert_eq!(Addr::read_from(&b""[..]), Err(addr::Err::InvalidName(String::from(""))));
  /// assert_eq!(Addr::read_from(&b"123Foo"[..]), Err(addr::Err::InvalidNum(String::from("123Foo"))));
  /// assert_eq!(Addr::read_from(&b"%Foo"[..]), Err(addr::Err::InvalidName(String::from("%Foo"))));
  ///
  /// let expected = (Addr::Num(123), &b""[..], 3);
  /// assert_eq!(Addr::read_from(&b"123"[..]), Ok(expected));
  ///
  /// let label = Label::try_from(&b"Foo"[..]).unwrap();
  /// let expected = (Addr::Label(label), &b""[..], 3);
  /// assert_eq!(Addr::read_from(&b"Foo"[..]), Ok(expected));
  ///
  /// let label = Label::try_from(&b"F_B"[..]).unwrap();
  /// let expected = (Addr::Label(label), &b""[..], 3);
  /// assert_eq!(Addr::read_from(&b"F_B"[..]), Ok(expected));
  ///
  /// let label = Label::try_from(&b"_FB"[..]).unwrap();
  /// let expected = (Addr::Label(label), &b""[..], 3);
  /// assert_eq!(Addr::read_from(&b"_FB"[..]), Ok(expected));
  ///
  /// let symbol = Symbol::try_from(&b"LCL"[..]).unwrap();
  /// let expected = (Addr::Symbol(symbol), &b""[..], 3);
  /// assert_eq!(Addr::read_from(&b"LCL"[..]), Ok(expected));
  ///
  /// let symbol = Symbol::try_from(&b"R0"[..]).unwrap();
  /// let expected = (Addr::Symbol(symbol), &b""[..], 2);
  /// assert_eq!(Addr::read_from(&b"R0"[..]), Ok(expected));
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

    if let Ok(symbol) = Symbol::try_from(txt) {
      return Ok((Self::from(symbol), rem, txt.len()));
    }

    if let Ok(label) = Label::try_from(txt) {
      return Ok((Self::from(label), rem, txt.len()));
    }

    Err(Err::invalid_name(txt))
  }
}
