//! A `HACK` address statement.

use crate::hack::NamedAddressToken;
use crate::hack::NumericAddressToken;
use crate::hack::PredefinedAddressToken;
use derive_more::Display;
use derive_more::From;

/// An address instruction as defined by the `HACK` assembly reference.
///
/// The binary representation of an address instruction is 16 bits wide.
#[derive(new, From, Display, Debug, PartialEq, Eq, Clone, Copy)]
pub enum Address {
  /// A numeric address.
  #[display(fmt = "@{}", _0)]
  Numeric(NumericAddressToken),

  /// A named address.
  #[display(fmt = "@{}", _0)]
  Named(NamedAddressToken),

  /// A predefined address.
  #[display(fmt = "@{}", _0)]
  Predefined(PredefinedAddressToken),
}
