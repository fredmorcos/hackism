//! Helpers for locations in source code.

use crate::utils::buf::Buf;

/// Alias for locations in byte buffers.
pub type Loc = usize;

/// Calculate the line and column of an index in a [Buf].
///
/// Returns a tuple `(line, column)` corresponding to the location
/// of an index in the input buffer.
pub fn loc(buf: Buf, loc: Loc) -> (usize, usize) {
  let mut linecol = (1, 1);

  for &b in &buf[..loc] {
    if b == b'\n' {
      linecol.0 += 1;
      linecol.1 = 1;
    } else {
      linecol.1 += 1;
    }
  }

  linecol
}
