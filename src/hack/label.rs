//! User defined variables for the HACK assembly language.

use crate::hack::Sym;
use crate::Buf;
use derive_more::Display;
use std::convert::TryFrom;

/// User defined labels as defined by the HACK assembly reference.
///
/// The binary representation is 15 bits wide and can fit in an
/// A-instruction.
///
/// # Examples
///
/// ```
/// use has::hack::Label;
/// use std::convert::TryFrom;
///
/// let label = Label::try_from("label".as_bytes()).unwrap();
/// assert_eq!(label.name(), "label");
/// ```
#[derive(Display, Debug, PartialEq, Eq, Hash)]
#[display(fmt = "{}", _0)]
pub struct Label<'b>(&'b str);

impl<'b> Copy for Label<'b> {}

/// Clone a [Label].
///
/// This is a shallow clone. Only the reference to the label name
/// string is copied, not the string itself.
impl<'b> Clone for Label<'b> {
  fn clone(&self) -> Self {
    Label(self.0)
  }
}

impl Label<'_> {
  /// Whether a byte is a symbol that can be used in a [Label].
  ///
  /// Returns true if `byte` is either `_`, `.`, `$` or `:`.
  fn is_label_sym(byte: u8) -> bool {
    byte == b'_' || byte == b'.' || byte == b'$' || byte == b':'
  }

  /// Whether a byte can be at the start of a [Label].
  ///
  /// Returns true if `byte` [is ASCII
  /// alphabetic](char::is_ascii_alphabetic) or [is a label
  /// symbol](Label::is_label_sym).
  pub(crate) fn is_label_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || Label::is_label_sym(byte)
  }

  /// Whether a byte can be part of a [Label].
  ///
  /// Returns true if `byte` [is ASCII
  /// alphabetic](u8::is_ascii_alphanumeric) or [is a label
  /// symbol](Label::is_label_sym).
  pub(crate) fn is_label_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || Label::is_label_sym(byte)
  }

  /// Returns the name byte slice of a [Label].
  ///
  /// # Examples
  ///
  /// ```
  /// use has::hack::Label;
  /// use std::convert::TryFrom;
  ///
  /// let label = Label::try_from("label".as_bytes()).unwrap();
  /// assert_eq!(label.name(), "label");
  pub fn name(&self) -> &str {
    self.0
  }
}

#[cfg(test)]
mod tests {
  use super::Label;

  #[test]
  fn test_is_label_sym() {
    assert!(Label::is_label_sym(b'_'));
    assert!(Label::is_label_sym(b'.'));
    assert!(Label::is_label_sym(b'$'));
    assert!(Label::is_label_sym(b':'));

    assert!(!Label::is_label_sym(b'@'));
    assert!(!Label::is_label_sym(b'^'));
    assert!(!Label::is_label_sym(b'&'));
    assert!(!Label::is_label_sym(b'*'));
    assert!(!Label::is_label_sym(b'('));
    assert!(!Label::is_label_sym(b')'));
    assert!(!Label::is_label_sym(b'%'));
    assert!(!Label::is_label_sym(b'#'));
    assert!(!Label::is_label_sym(b'!'));
  }

  #[test]
  fn display() {
    use std::convert::TryFrom;

    let label = Label::try_from("label".as_bytes()).unwrap();
    assert_eq!(format!("{}", label), "label");
  }
}

/// Errors when parsing labels.
#[derive(Display, Debug, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "Label error: {}")]
pub enum Err {
  /// Label is empty.
  #[display(fmt = "label is empty")]
  Empty,

  /// Label starts with an invalid character.
  #[display(fmt = "label starts with invalid character `{}`", "char::from(*_0)")]
  InvalidStart(u8),

  /// Label contains an invalid character.
  #[display(fmt = "label contains invalid character `{}`", "char::from(*_0)")]
  InvalidByte(u8),

  /// Label is a predefined HACK symbol.
  #[display(fmt = "cannot use predefined symbol `{}` as a label", _0)]
  Sym(Sym),
}

/// Parse a [Label] object from a (byte buffer)(Buf).
///
/// Invalid input produces an `Err(LabelErr)`.
///
/// # Examples
///
/// ```
/// use has::hack::Label;
/// use has::hack::LabelErr;
/// use std::convert::TryFrom;
///
/// let label = Label::try_from("@foobar".as_bytes());
/// assert_eq!(label, Err(LabelErr::InvalidStart(b'@')));
///
/// let label = Label::try_from("foobar@".as_bytes());
/// assert_eq!(label, Err(LabelErr::InvalidByte(b'@')));
///
/// let label = Label::try_from("1foobar".as_bytes());
/// assert_eq!(label, Err(LabelErr::InvalidStart(b'1')));
///
/// let label = Label::try_from("foobar1".as_bytes()).unwrap();
/// assert_eq!(label.name(), "foobar1");
/// ```
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

    if let Ok(sym) = Sym::try_from(buf) {
      return Err(Err::Sym(sym));
    }

    Ok(Self(unsafe { std::str::from_utf8_unchecked(buf) }))
  }
}
