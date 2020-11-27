use std::fmt;

use super::Scanner;
use crate::location::Location;
use crate::location::SourceLocation;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
  EOF {
    source_location: SourceLocation,
    expecting: &'static str,
  },
  Unexpected {
    source_location: SourceLocation,
    byte: u8,
    expecting: &'static str,
  },
  Range {
    expecting: &'static str,
  },
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Error::EOF {
        source_location,
        expecting,
      } => write!(
        f,
        "Unexpected end of file, expecting {} (happened at {})",
        expecting, source_location
      ),
      Error::Unexpected {
        source_location,
        byte,
        expecting,
      } => write!(
        f,
        "Unexpected character {}, expecting {} (happened at {})",
        char::from(*byte),
        expecting,
        source_location
      ),
      Error::Range { expecting } => {
        write!(f, "Value out of range, expecting {}", expecting)
      }
    }
  }
}

impl Error {
  pub fn location(&self, scanner: &Scanner) -> Location {
    match self {
      Error::EOF {
        source_location: _,
        expecting: _,
      }
      | Error::Unexpected {
        source_location: _,
        byte: _,
        expecting: _,
      } => scanner.current_location,
      Error::Range { expecting: _ } => scanner.token_location,
    }
  }

  pub(crate) fn new_eof(
    source_location: SourceLocation, expecting: &'static str,
  ) -> Self {
    Error::EOF {
      source_location,
      expecting,
    }
  }

  pub(crate) fn new_unexpected(
    source_location: SourceLocation, byte: u8, expecting: &'static str,
  ) -> Self {
    Error::Unexpected {
      source_location,
      byte,
      expecting,
    }
  }

  pub(crate) fn new_range(expecting: &'static str) -> Self {
    Error::Range { expecting }
  }
}
