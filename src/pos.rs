#![warn(clippy::all)]

use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pos {
  line: usize,
  col: usize,
}

impl Pos {
  pub fn inc(&mut self, c: u8) {
    if c == b'\n' {
      self.line += 1;
      self.col = 0;
    } else {
      self.col += 1;
    }
  }
}

impl Default for Pos {
  fn default() -> Self {
    Self { line: 1, col: 0 }
  }
}

impl fmt::Display for Pos {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}:{}", self.line, self.col)
  }
}

#[cfg(test)]
impl Pos {
  pub fn new(line: usize, col: usize) -> Self {
    Self { line, col }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn with_newline() {
    let mut p = Pos::default();
    p.inc(b'a');
    assert_eq!(p, Pos::new(1, 1));
    p.inc(b'\n');
    assert_eq!(p, Pos::new(2, 0));
    p.inc(b'b');
    assert_eq!(p, Pos::new(2, 1));
    p.inc(b'c');
    assert_eq!(p, Pos::new(2, 2));
  }

  #[test]
  fn without_newline() {
    let mut p = Pos::default();
    p.inc(b'a');
    assert_eq!(p, Pos::new(1, 1));
    p.inc(b'b');
    assert_eq!(p, Pos::new(1, 2));
    p.inc(b'c');
    assert_eq!(p, Pos::new(1, 3));
  }
}
