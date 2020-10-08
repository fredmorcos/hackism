#![warn(clippy::all)]

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

#[cfg(test)]
impl Pos {
  pub fn new(line: usize, col: usize) -> Self {
    Self { line, col }
  }
}
