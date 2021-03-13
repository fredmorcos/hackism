//! Location ranges in source code.

use super::Location;
use std::fmt;

/// A location range in source code or input buffer.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Span {
  /// Starting location.
  start: Location,

  /// Ending location,
  end: Location,
}

/// Display "from <start> to <end> (<N> bytes)" for a [`Span`].
impl fmt::Display for Span {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "from {} to {} ({} bytes)", self.start, self.end, self.length())
  }
}

impl Span {
  /// Create a new span starting at `start` and ending at `end`.
  ///
  /// # Arguments
  ///
  /// * `start` - The starting [`Location`] of the span.
  ///
  /// * `end` - The ending [`Location`] of the span.
  pub fn new(start: Location, end: Location) -> Self {
    Self { start, end }
  }

  /// The span's starting location.
  pub fn start(&self) -> Location {
    self.start
  }

  /// The span's ending location.
  pub fn end(&self) -> Location {
    self.end
  }

  /// The span's length.
  pub fn length(&self) -> usize {
    self.start - self.end
  }
}

/// Shorthand for creating [`Span`] objects.
///
/// See [`Span::new`].
///
/// # Variants
///
/// * `(start_index, start_line, start_column, end_index, end_line,
/// end_column)` - Creates two [`Location`] objects out of the
/// `$start_` and `$end_` arguments, then creates the [`Span`] object.
///
/// * `(start, end)` - Creates two [`Location`] objects using
/// [`Location::from`], then creates the [`Span`] object. This means
/// that location triples and location objects can be passed to this
/// variant.
#[macro_export]
macro_rules! span {
  ($start_index:expr, $start_line:expr, $start_column:expr,
   $end_index:expr, $end_line:expr, $end_column:expr) => {
    Span::new(
      location!($start_index, $start_line, $start_column),
      location!($end_index, $end_line, $end_column),
    )
  };
  ($start:expr, $end:expr) => {
    Span::new(Location::from($start), Location::from($end))
  };
}
