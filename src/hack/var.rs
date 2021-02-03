//! User defined variables for the HACK assembly language.

use crate::hack::Sym;
use crate::Buf;
use derive_more::Display;
use std::convert::TryFrom;

/// User defined variables as defined by the HACK assembly reference.
///
/// The binary representation is 15 bits wide and can fit in an
/// A-instruction.
///
/// # Examples
///
/// ```
/// use has::hack::Var;
/// use std::convert::TryFrom;
///
/// let var = Var::try_from("label".as_bytes()).unwrap();
/// assert_eq!(var.name(), "label");
/// ```
#[derive(Display, Debug, PartialEq, Eq, Hash)]
#[display(fmt = "{}", _0)]
pub struct Var<'b>(&'b str);

impl<'b> Copy for Var<'b> {}

/// Clone a [Var].
///
/// This is a shallow clone. Only the reference to the variable name
/// string is copied, not the string itself.
impl<'b> Clone for Var<'b> {
  fn clone(&self) -> Self {
    Var(self.0)
  }
}

impl Var<'_> {
  /// Whether a byte is a symbol that can be used in a [Var].
  ///
  /// Returns true if `byte` is either `_`, `.`, `$` or `:`.
  fn is_var_sym(byte: u8) -> bool {
    byte == b'_' || byte == b'.' || byte == b'$' || byte == b':'
  }

  /// Whether a byte can be at the start of a [Var].
  ///
  /// Returns true if `byte` [is ASCII
  /// alphabetic](char::is_ascii_alphabetic) or [is a variable
  /// symbol](Var::is_var_sym).
  pub(crate) fn is_var_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || Var::is_var_sym(byte)
  }

  /// Whether a byte can be part of a [Var].
  ///
  /// Returns true if `byte` [is ASCII
  /// alphabetic](u8::is_ascii_alphanumeric) or [is a variable
  /// symbol](Var::is_var_sym).
  pub(crate) fn is_var_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || Var::is_var_sym(byte)
  }

  /// Returns the name byte slice of a [Var].
  ///
  /// # Examples
  ///
  /// ```
  /// use has::hack::Var;
  /// use std::convert::TryFrom;
  ///
  /// let var = Var::try_from("label".as_bytes()).unwrap();
  /// assert_eq!(var.name(), "label");
  pub fn name(&self) -> &str {
    self.0
  }
}

#[cfg(test)]
mod tests {
  use super::Var;

  #[test]
  fn test_is_var_sym() {
    assert!(Var::is_var_sym(b'_'));
    assert!(Var::is_var_sym(b'.'));
    assert!(Var::is_var_sym(b'$'));
    assert!(Var::is_var_sym(b':'));

    assert!(!Var::is_var_sym(b'@'));
    assert!(!Var::is_var_sym(b'^'));
    assert!(!Var::is_var_sym(b'&'));
    assert!(!Var::is_var_sym(b'*'));
    assert!(!Var::is_var_sym(b'('));
    assert!(!Var::is_var_sym(b')'));
    assert!(!Var::is_var_sym(b'%'));
    assert!(!Var::is_var_sym(b'#'));
    assert!(!Var::is_var_sym(b'!'));
  }

  #[test]
  fn display() {
    use std::convert::TryFrom;

    let var = Var::try_from("label".as_bytes()).unwrap();
    assert_eq!(format!("{}", var), "label");
  }
}

/// Errors when parsing variables.
#[derive(Display, Debug, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "Variable error: {}")]
pub enum Err {
  /// Variable is empty.
  #[display(fmt = "variable is empty")]
  Empty,

  /// Variable starts with an invalid character.
  #[display(fmt = "variable starts with invalid character `{}`", "char::from(*_0)")]
  InvalidStart(u8),

  /// Variable contains an invalid character.
  #[display(fmt = "variable contains invalid character `{}`", "char::from(*_0)")]
  InvalidByte(u8),

  /// Variable is a predefined HACK symbol.
  #[display(fmt = "cannot use predefined symbol `{}` as a variable", _0)]
  Sym(Sym),
}

/// Parse a [Var] object from a (byte buffer)(Buf).
///
/// Invalid input produces an `Err(VarErr)`.
///
/// # Examples
///
/// ```
/// use has::hack::Var;
/// use has::hack::VarErr;
/// use std::convert::TryFrom;
///
/// let var = Var::try_from("@foobar".as_bytes());
/// assert_eq!(var, Err(VarErr::InvalidStart(b'@')));
///
/// let var = Var::try_from("foobar@".as_bytes());
/// assert_eq!(var, Err(VarErr::InvalidByte(b'@')));
///
/// let var = Var::try_from("1foobar".as_bytes());
/// assert_eq!(var, Err(VarErr::InvalidStart(b'1')));
///
/// let var = Var::try_from("foobar1".as_bytes()).unwrap();
/// assert_eq!(var.name(), "foobar1");
/// ```
impl<'b> TryFrom<Buf<'b>> for Var<'b> {
  type Error = Err;

  fn try_from(buf: Buf<'b>) -> Result<Self, Self::Error> {
    let c0 = if let Some(&c0) = buf.get(0) {
      c0
    } else {
      return Err(Err::Empty);
    };

    if !Var::is_var_start(c0) {
      return Err(Err::InvalidStart(c0));
    }

    for &c in &buf[1..] {
      if !Var::is_var_byte(c) {
        return Err(Err::InvalidByte(c));
      }
    }

    if let Ok(sym) = Sym::try_from(buf) {
      return Err(Err::Sym(sym));
    }

    Ok(Self(unsafe { std::str::from_utf8_unchecked(buf) }))
  }
}
