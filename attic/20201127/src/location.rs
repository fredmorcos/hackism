#![warn(clippy::all)]

use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceLocation {
  file: &'static str,
  line: u32,
}

impl SourceLocation {
  pub fn new(file: &'static str, line: u32) -> Self {
    Self { file, line }
  }
}

impl fmt::Display for SourceLocation {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}:{}", self.file, self.line)
  }
}

#[macro_export]
macro_rules! source_location {
  () => {
    SourceLocation::new(file!(), line!())
  };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
  line: usize,
  col: usize,
}

impl Location {
  pub fn increment(&mut self, byte: u8) {
    if byte == b'\n' {
      self.line += 1;
      self.col = 0;
    } else {
      self.col += 1;
    }
  }

  pub fn increment_newline(&mut self) {
    self.col = 1;
    self.line += 1;
  }

  pub fn increment_non_newline(&mut self) {
    self.col += 1;
  }

  pub fn increment_non_newline_by(&mut self, n: usize) {
    self.col += n;
  }
}

impl Default for Location {
  fn default() -> Self {
    Self { line: 1, col: 0 }
  }
}

impl fmt::Display for Location {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}:{}", self.line, self.col)
  }
}

#[cfg(test)]
impl Location {
  pub fn new(line: usize, col: usize) -> Self {
    Self { line, col }
  }
}

#[cfg(test)]
mod tests {
  use super::Location;

  #[test]
  fn with_newline() {
    let mut location = Location::default();
    location.increment(b'a');
    assert_eq!(location, Location::new(1, 1));
    location.increment(b'\n');
    assert_eq!(location, Location::new(2, 0));
    location.increment(b'b');
    assert_eq!(location, Location::new(2, 1));
    location.increment(b'c');
    assert_eq!(location, Location::new(2, 2));
  }

  #[test]
  fn without_newline() {
    let mut location = Location::default();
    location.increment(b'a');
    assert_eq!(location, Location::new(1, 1));
    location.increment(b'b');
    assert_eq!(location, Location::new(1, 2));
    location.increment(b'c');
    assert_eq!(location, Location::new(1, 3));
  }
}
