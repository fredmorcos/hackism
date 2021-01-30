//! Helpers for locations in source code.

use crate::utils::buf::Buf;
use crate::utils::buf::Byte;

use std::fmt;

/// Location type.
///
/// # impl `Display`
///
/// The `Display` implementation will print out `line X, column Y`.
///
/// ## Examples
///
/// ```
/// use has::utils::loc::Loc;
///
/// let loc = Loc::new(2, 3);
/// assert_eq!(format!("{}", loc), "line 2, column 3");
/// ```
///
/// # impl `Default`
///
/// The `Default` implementation will create a location with line `1`
/// at column `1`.
///
/// ## Examples
///
/// ```
/// use has::utils::loc::Loc;
///
/// assert_eq!(Loc::default(), Loc::new(1, 1));
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Loc {
  /// Line in buffer.
  line: usize,

  /// Column in line.
  col: usize,
}

impl fmt::Display for Loc {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "line {}, column {}", self.line, self.col)
  }
}

impl Default for Loc {
  fn default() -> Self {
    Self { line: 1, col: 1 }
  }
}

impl Loc {
  /// Create a new location from `line` and `col`.
  pub fn new(line: usize, col: usize) -> Self {
    Self { line, col }
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

/// Alias for locations in byte buffers.
pub type Index = usize;

/// Calculate the line and column (location) of an index in a [Buf].
///
/// Returns a [location](Loc) corresponding to the line and column
/// location of an index in the input buffer.
pub fn loc(buf: Buf, index: Index) -> Loc {
  let mut loc = Loc::default();

  for &b in &buf[..index] {
    loc.inc(b)
  }

  loc
}
