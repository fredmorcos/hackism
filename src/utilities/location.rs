//! Locations in source code.

use derive_more::Display;
use std::ops::Sub;

/// A location in source code or input buffer.
#[derive(Display, Debug, PartialEq, Eq, Clone, Copy)]
#[display(fmt = "line {}, column {} (byte index {})", line, column, index)]
pub struct Location {
  /// Character index in a buffer.
  index: usize,

  /// Line in a buffer.
  line: usize,

  /// Column on a line in a buffer.
  column: usize,
}

/// Create a default location a line `1`, column `1`.
impl Default for Location {
  fn default() -> Self {
    Self { index: 0, line: 1, column: 1 }
  }
}

/// Create a location from a triple.
impl From<(usize, usize, usize)> for Location {
  fn from(triple: (usize, usize, usize)) -> Self {
    Self { index: triple.0, line: triple.1, column: triple.2 }
  }
}

/// Location distances.
impl Sub for Location {
  type Output = usize;

  fn sub(self, rhs: Self) -> Self::Output {
    self.index() - rhs.index()
  }
}

impl Location {
  /// Create a location at `index`, `line` and `column`.
  ///
  /// # Arguments
  ///
  /// * `index` - The byte index in the input buffer.
  ///
  /// * `line` - The line in the input buffer.
  ///
  /// * `column` - The column in the input buffer.
  pub fn new(index: usize, line: usize, column: usize) -> Self {
    Self { index, line, column }
  }

  /// Increment the location by a non-newline byte.
  ///
  /// This can be used during reading when the byte being consumed is
  /// known to not be a newline.
  pub fn increment(&mut self) {
    self.index += 1;
    self.column += 1;
  }

  /// Increment the location by a newline byte.
  ///
  /// This can be used during reading when the byte being consumed is
  /// known to be a newline.
  pub fn newline(&mut self) {
    self.index += 1;
    self.line += 1;
    self.column = 1;
  }

  /// Returns the location's line.
  pub fn line(&self) -> usize {
    self.line
  }

  /// Returns the location's column.
  pub fn column(&self) -> usize {
    self.column
  }

  /// Returns the location's index.
  pub fn index(&self) -> usize {
    self.index
  }

  /// Returns a triple with the location's index, line and column.
  ///
  /// # Notes
  ///
  /// * Only available under `#[cfg(test)]`.
  #[cfg(test)]
  pub(crate) fn triple(&self) -> (usize, usize, usize) {
    (self.index, self.line, self.column)
  }
}

/// Shorthand for creating [`Location`] objects.
///
/// See [`Location::new`].
#[macro_export]
macro_rules! location {
  ($index:expr, $line:expr, $column:expr) => {
    Location::new($index, $line, $column)
  };
}

#[cfg(test)]
mod tests {
  use super::Location;

  #[test]
  fn default() {
    let location = Location::default();
    assert_eq!(location.triple(), (0, 1, 1));
  }

  #[test]
  fn increment() {
    let mut location = Location::default();
    location.increment();
    assert_eq!(location.triple(), (1, 1, 2));
    location.newline();
    assert_eq!(location.triple(), (2, 2, 1));
  }

  #[test]
  fn distance() {
    let start = Location::default();
    let end = Location::new(5, 3, 1);
    assert_eq!(end - start, 5);
  }
}
