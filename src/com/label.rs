use std::convert::TryFrom;
use std::fmt;

use crate::com::symbol::Symbol;
use crate::utils::buf::Buf;

/// An encoding for user-defined symbols as defined by the HACK
/// assembly reference.
///
/// # impl `TryFrom<&[u8]>` (`type Error = ()`)
///
/// A [Label] object can be created from a slice of bytes. A
/// `Result::Err(())` is returned if the input sequence is invalid.
///
/// ## Examples
///
/// ```
/// use has::com::label::Label;
/// use has::com::label;
///
/// use std::convert::TryFrom;
///
/// assert_eq!(Label::try_from(&b"@foobar"[..]), Err(label::Err::InvalidStart(b'@')));
/// assert_eq!(Label::try_from(&b"foobar@"[..]), Err(label::Err::InvalidByte(b'@')));
/// assert_eq!(Label::try_from(&b"1foobar"[..]), Err(label::Err::InvalidStart(b'1')));
///
/// let label = Label::try_from(&b"foobar1"[..]).unwrap();
/// assert_eq!(label.label(), "foobar1");
/// ```
///
/// # impl `Display`
///
/// ```
/// use has::com::label::Label;
///
/// use std::convert::TryFrom;
///
/// let label = Label::try_from(&b"foobar"[..]).unwrap();
/// assert_eq!(format!("{}", label), "foobar");
/// ```
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Label<'b>(&'b str);

impl<'b> Copy for Label<'b> {}

impl<'b> Clone for Label<'b> {
  fn clone(&self) -> Self {
    Label(self.0)
  }
}

impl Label<'_> {
  /// Whether a byte is a symbol that can be used in a [Label].
  ///
  /// Returns true if `byte` is either `_`, `.`, `$` or `:`.
  fn is_label_symbol(byte: u8) -> bool {
    byte == b'_' || byte == b'.' || byte == b'$' || byte == b':'
  }

  /// Whether a byte can be at the start of a [Label].
  ///
  /// Returns true if `byte` [is ASCII
  /// alphabetic](is_ascii_alphabetic) or [is a label
  /// symbol](is_label_symbol).
  pub(crate) fn is_label_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || Label::is_label_symbol(byte)
  }

  /// Whether a byte can be part of a [Label].
  ///
  /// Returns true if `byte` [is ASCII
  /// alphabetic](is_ascii_alphanumeric) or [is a label
  /// symbol](is_label_symbol).
  pub(crate) fn is_label_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || Label::is_label_symbol(byte)
  }

  /// Returns the label byte slice of a [Label].
  ///
  /// # Examples
  ///
  /// ```
  /// use has::com::label::Label;
  ///
  /// use std::convert::TryFrom;
  ///
  /// let label = Label::try_from(&b"foobar1"[..]).unwrap();
  /// assert_eq!(label.label(), "foobar1");
  pub fn label(&self) -> &str {
    self.0
  }
}

#[cfg(test)]
mod label_tests {
  use super::Label;

  #[test]
  fn test_is_label_symbol() {
    assert!(Label::is_label_symbol(b'_'));
    assert!(Label::is_label_symbol(b'.'));
    assert!(Label::is_label_symbol(b'$'));
    assert!(Label::is_label_symbol(b':'));

    assert!(!Label::is_label_symbol(b'@'));
    assert!(!Label::is_label_symbol(b'^'));
    assert!(!Label::is_label_symbol(b'&'));
    assert!(!Label::is_label_symbol(b'*'));
    assert!(!Label::is_label_symbol(b'('));
    assert!(!Label::is_label_symbol(b')'));
    assert!(!Label::is_label_symbol(b'%'));
    assert!(!Label::is_label_symbol(b'#'));
    assert!(!Label::is_label_symbol(b'!'));
  }
}

/// Errors when parsing labels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Err {
  /// Label is empty.
  Empty,
  /// Label starts with an invalid character.
  InvalidStart(u8),
  /// Label contains an invalid character.
  InvalidByte(u8),
  /// Label is a predefined HACK symbol.
  Symbol(Symbol),
}

impl fmt::Display for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Err::Empty => write!(f, "label is empty"),
      Err::InvalidStart(c) => {
        write!(f, "label starts with invalid character `{}`", char::from(*c))
      }
      Err::InvalidByte(c) => {
        write!(f, "label contains invalid character `{}`", char::from(*c))
      }
      Err::Symbol(s) => write!(f, "cannot use predefined symbol `{}` as a label", s),
    }
  }
}

impl<'b> TryFrom<Buf<'b>> for Label<'b> {
  type Error = Err;

  fn try_from(buf: Buf<'b>) -> Result<Self, Self::Error> {
    let c0 = if let Some(&c0) = buf.get(0) {
      c0
    } else {
      return Err(Err::Empty);
    };

    if !Label::is_label_start(c0) {
      return Err(Err::InvalidStart(c0));
    }

    for &c in &buf[1..] {
      if !Label::is_label_byte(c) {
        return Err(Err::InvalidByte(c));
      }
    }

    if let Ok(symbol) = Symbol::try_from(buf) {
      return Err(Err::Symbol(symbol));
    }

    Ok(Self(unsafe { std::str::from_utf8_unchecked(buf) }))
  }
}

impl fmt::Display for Label<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.0)
  }
}
