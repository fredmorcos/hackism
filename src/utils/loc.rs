//! Helpers for locations in source code.

use crate::Buf;
use crate::Byte;
use derive_more::Display;

/// Locations in source code.
#[derive(new, Display, Debug, PartialEq, Eq, Clone, Copy)]
#[display(fmt = "line {}, column {}", line, col)]
pub struct Loc {
  /// Line in buffer.
  line: usize,

  /// Column in line.
  col: usize,
}

/// Create a default location at line `1`, column `1`.
///
/// # Examples
///
/// ```
/// use has::Loc;
///
/// assert_eq!(Loc::default(), Loc::new(1, 1));
/// ```
impl Default for Loc {
  fn default() -> Self {
    Self { line: 1, col: 1 }
  }
}

/// Alias for locations in byte buffers.
pub type Index = usize;

impl Loc {
  /// Calculate the line and column (location) of an index in a [Buf].
  ///
  /// Returns a [location](Loc) corresponding to the line and column
  /// of an index in the input buffer.
  ///
  /// # Panics
  ///
  /// Panics if the index is out of the buffer's bounds.
  pub fn from_index(buf: Buf, index: Index) -> Loc {
    let mut loc = Loc::default();

    for &b in &buf[..index] {
      loc.inc(b)
    }

    loc
  }

  /// Increment the location based on `byte`.
  ///
  /// If `byte` is a newline, `line` is incremented and `column` is
  /// reset to `1`. Otherwise, `column` is incremented.
  pub fn inc(&mut self, byte: Byte) {
    if byte == b'\n' {
      self.line += 1;
      self.col = 1;
    } else {
      self.col += 1;
    }
  }

  /// Returns the line for a location.
  pub fn line(&self) -> usize {
    self.line
  }

  /// Returns the column on the location's line.
  pub fn col(&self) -> usize {
    self.col
  }
}

#[cfg(test)]
mod tests {
  #[test]
  fn display() {
    use crate::Loc;

    let loc = Loc::new(2, 3);
    assert_eq!(format!("{}", loc), "line 2, column 3");
  }
}
