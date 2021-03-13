//! Utilities for writing tests.

/// Shorthand to assert the output of [`format!`] on an object.
///
/// Calls `format!("{}", $object)` and asserts the output against
/// `$text`.
///
/// # Notes
///
/// * Only available under `#[cfg(test)]`.
#[cfg(test)]
#[macro_export]
macro_rules! assert_format {
  ($object:expr, $text:expr) => {
    assert_eq!(format!("{}", $object), $text)
  };
}
