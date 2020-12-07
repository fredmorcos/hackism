use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SrcLoc {
  file: &'static str,
  line: u32,
}

impl SrcLoc {
  pub fn new(file: &'static str, line: u32) -> Self {
    Self { file, line }
  }
}

impl fmt::Display for SrcLoc {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "file {}, line {}", self.file, self.line)
  }
}

#[macro_export]
macro_rules! srcloc {
  () => {
    SrcLoc::new(file!(), line!())
  };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Loc {
  line: usize,
  col: usize,
}

impl Loc {
  pub fn inc(&mut self, byte: u8) {
    if byte == b'\n' {
      self.line += 1;
      self.col = 0;
    } else {
      self.col += 1;
    }
  }
}

impl Default for Loc {
  fn default() -> Self {
    Self { line: 1, col: 0 }
  }
}

impl fmt::Display for Loc {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "line {}, column {}", self.line, self.col)
  }
}

#[cfg(test)]
impl Loc {
  pub fn new(line: usize, col: usize) -> Self {
    Self { line, col }
  }
}

#[macro_export]
macro_rules! loc {
  () => {
    Loc::default()
  };
  ($line:expr, $col:expr) => {
    Loc::new($line, $col)
  };
}

#[cfg(test)]
mod tests {
  use super::Loc;

  #[test]
  fn with_newline() {
    let mut loc = loc!();
    loc.inc(b'a');
    assert_eq!(loc, loc!(1, 1));
    loc.inc(b'\n');
    assert_eq!(loc, loc!(2, 0));
    loc.inc(b'b');
    assert_eq!(loc, loc!(2, 1));
    loc.inc(b'c');
    assert_eq!(loc, loc!(2, 2));
  }

  #[test]
  fn without_newline() {
    let mut loc = loc!();
    loc.inc(b'a');
    assert_eq!(loc, loc!(1, 1));
    loc.inc(b'b');
    assert_eq!(loc, loc!(1, 2));
    loc.inc(b'c');
    assert_eq!(loc, loc!(1, 3));
  }
}
