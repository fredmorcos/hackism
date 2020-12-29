use std::convert::TryFrom;
use std::fmt;

use crate::utils::Buf;

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
/// use has::asm::label::Label;
///
/// use std::convert::TryFrom;
///
/// assert_eq!(Label::try_from(&b"@foobar"[..]), Err(()));
/// assert_eq!(Label::try_from(&b"foobar@"[..]), Err(()));
/// assert_eq!(Label::try_from(&b"1foobar"[..]), Err(()));
///
/// let label = Label::try_from(&b"foobar1"[..]).unwrap();
/// assert_eq!(label.label(), &b"foobar1"[..]);
/// ```
///
/// # impl `Display`
///
/// ```
/// use has::asm::label::Label;
///
/// use std::convert::TryFrom;
///
/// let label = Label::try_from(&b"foobar"[..]).unwrap();
/// assert_eq!(format!("{}", label), "foobar");
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Label<'b>(&'b [u8]);

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
  /// use has::asm::label::Label;
  ///
  /// use std::convert::TryFrom;
  ///
  /// let label = Label::try_from(&b"foobar1"[..]).unwrap();
  /// assert_eq!(label.label(), &b"foobar1"[..]);
  pub fn label(&self) -> &[u8] {
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

impl<'b> TryFrom<Buf<'b>> for Label<'b> {
  type Error = ();

  fn try_from(buf: Buf<'b>) -> Result<Self, Self::Error> {
    let c0 = if let Some(&c0) = buf.get(0) {
      c0
    } else {
      return Err(());
    };

    if !Label::is_label_start(c0) {
      return Err(());
    }

    for &c in &buf[1..] {
      if !Label::is_label_byte(c) {
        return Err(());
      }
    }

    Ok(Self(buf))
  }
}

impl fmt::Display for Label<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", unsafe { std::str::from_utf8_unchecked(self.0) })
  }
}
