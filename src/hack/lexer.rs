//! A lexer for `HACK` assembly programs.

use super::Computation;
use super::Destination;
use super::Jump;
use super::PredefinedAddress;
use super::Token;
use crate::span;
use crate::utilities::Location;
use crate::utilities::Span;
use atoi::FromRadix10Checked;
use derive_more::Display;
use std::convert::TryFrom;

/// Lexer for `HACK` assembly programs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lexer {
  /// The input buffer.
  input: Vec<u8>,

  /// The current location in the input buffer.
  location: Location,
}

impl Lexer {
  /// Whether a byte is a symbol that can be used in a label.
  ///
  /// Returns true if `byte` is either `_`, `.`, `$` or `:`.
  fn is_label_symbol(byte: u8) -> bool {
    byte == b'_' || byte == b'.' || byte == b'$' || byte == b':'
  }

  /// Whether a byte can be at the start of a [Label].
  ///
  /// Returns true if `byte` [is ASCII
  /// alphabetic](char::is_ascii_alphabetic) or [is a label
  /// symbol](Lexer::is_label_sym).
  pub(crate) fn is_label_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || Lexer::is_label_symbol(byte)
  }

  /// Whether a byte can be part of a [Label].
  ///
  /// Returns true if `byte` [is ASCII
  /// alphabetic](u8::is_ascii_alphanumeric) or [is a label
  /// symbol](Lexer::is_label_sym).
  pub(crate) fn is_label_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || Lexer::is_label_symbol(byte)
  }
}

/// Create a new lexer to scan a byte buffer.
impl From<Vec<u8>> for Lexer {
  fn from(input: Vec<u8>) -> Self {
    Self { input, location: Location::default() }
  }
}

/// Create a new lexer to scan a string's byte buffer.
impl From<String> for Lexer {
  fn from(input: String) -> Self {
    Self::from(input.into_bytes())
  }
}

/// Errors returned by the `HACK` lexer.
#[derive(new, Display, Debug, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "Lexing error: {}")]
pub enum Error {
  /// Lexing error when scanning a token that begins with `/`.
  #[display(fmt = "Expecting another `/` at {} to form a comment", start)]
  Comment {
    /// Error location.
    start: Location,
  },

  /// An unrecognized input byte was reached.
  #[display(fmt = "Unknown input byte `{}` at {}", byte, start)]
  Unknown {
    /// The unknown input byte.
    byte: char,

    /// Error location.
    start: Location,
  },

  /// Unexpected end of file.
  #[display(fmt = "Unexpected end of file at {}", start)]
  UnexpectedEOF {
    /// Error location.
    start: Location,
  },

  /// Label name contains an invalid character.
  #[display(fmt = "Invalid label or named address at {}", start)]
  InvalidLabelName {
    /// Error location.
    start: Location,
  },

  /// Expecting a closing `)` for label.
  #[display(fmt = "Expected a `)` at {} to close a label", start)]
  ExpectedLabelClosing {
    /// Error location.
    start: Location,
  },

  /// Numeric address contains invalid bytes.
  #[display(fmt = "Invalid numeric address at {}", start)]
  InvalidNumericAddress {
    /// Error location.
    start: Location,
  },

  /// Numeric address is out of range.
  #[display(fmt = "Numeric address at {} is out of the 15-bit range", start)]
  NumericAddressOutOfRange {
    /// Error location.
    start: Location,
  },

  /// Named address contains an invalid byte.
  #[display(fmt = "Invalid byte in named address at {}", start)]
  InvalidNamedAddress {
    /// Error location.
    start: Location,
  },

  /// Unknown destination.
  #[display(fmt = "Invalid destination at {}", start)]
  InvalidDestination {
    /// Error location.
    start: Location,
  },

  /// Unknown computation.
  #[display(fmt = "Invalid computation at {}", start)]
  InvalidComputation {
    /// Error location.
    start: Location,
  },

  /// Could not find either a computation or a jump.
  #[display(fmt = "Invalid computation or jump at {}", start)]
  InvalidComputationOrJump {
    /// Error location.
    start: Location,
  },
}

/// Consume input bytes, producing [Token]s.
///
/// # Returns
///
/// `None` - end of file has been successfully reached.
///
/// `Some(Err(LexerError))` - a lexing error has occurred.
///
/// `Some(Ok(Token))` - a token parsed from the input buffer.
impl Iterator for Lexer {
  type Item = Result<Token, Error>;

  fn next(&mut self) -> Option<Self::Item> {
    // Consume a byte if available and store its location.
    let &byte = self.input.get(self.location.index())?;
    let start = self.location;

    if byte == b'\n' {
      self.location.newline();

      // If it's newlines, keep consuming newlines until we find a
      // non-newline byte.
      while let Some(&byte) = self.input.get(self.location.index()) {
        if byte != b'\n' {
          break;
        }

        self.location.newline();
      }

      Some(Ok(Token::newlines(span!(start, self.location))))
    } else if byte.is_ascii_whitespace() {
      self.location.increment();

      // If it's whitespaces, keep consuming whitespace until we find
      // a non-whitespace byte or a newline.
      while let Some(&byte) = self.input.get(self.location.index()) {
        if byte == b'\n' || !byte.is_ascii_whitespace() {
          break;
        } else {
          self.location.increment();
        }
      }

      Some(Ok(Token::whitespace(span!(start, self.location))))
    } else if byte == b'/' {
      self.location.increment();

      // If it's a /, look for another / to start reading a
      // comment. If another / is not found then that's an error.
      if let Some(b'/') = self.input.get(self.location.index()) {
        self.location.increment();
      } else {
        return Some(Err(Error::new_comment(self.location)));
      };

      // Keep consuming the comment until the next newline.
      while let Some(&byte) = self.input.get(self.location.index()) {
        if byte == b'\n' {
          break;
        }

        self.location.increment();
      }

      Some(Ok(Token::comment(span!(start, self.location))))
    } else if byte == b'@' {
      // Found an address marker.
      self.location.increment();

      // Expect to consume at least one more byte for the address.
      if let Some(&byte) = self.input.get(self.location.index()) {
        if byte.is_ascii_digit() {
          // It starts with a digit, it's a numeric address.
          self.location.increment();

          // Keep consuming until a newline or whitespace.
          while let Some(&byte) = self.input.get(self.location.index()) {
            if byte.is_ascii_whitespace() {
              break;
            }

            // If the byte is not a digit then that's an error.
            if !byte.is_ascii_digit() {
              return Some(Err(Error::new_invalid_numeric_address(self.location)));
            }

            self.location.increment();
          }

          // Parse the value into a u16 address.
          let range = start.index() + 1..self.location.index();
          let text = &self.input[range];

          match u16::from_radix_10_checked(text) {
            (Some(address), used) if used == text.len() => {
              // 32767 (15 bits of address value).
              if address > 32767 {
                return Some(Err(Error::new_numeric_address_out_of_range(start)));
              }

              Some(Ok(Token::numeric_address(span!(start, self.location), address)))
            }
            (_, _) => Some(Err(Error::new_invalid_numeric_address(start))),
          }
        } else if Self::is_label_start(byte) {
          // It starts with a label starting byte, it's a named address.
          self.location.increment();

          // Keep consuming until a newline or whitespace.
          while let Some(&byte) = self.input.get(self.location.index()) {
            if byte.is_ascii_whitespace() {
              break;
            }

            // If the byte is not a valid label byte then that's an error.
            if !Self::is_label_byte(byte) {
              return Some(Err(Error::new_invalid_named_address(self.location)));
            }

            self.location.increment();
          }

          // Try to parse the value into a predefined address.
          let range = start.index() + 1..self.location.index();
          let text = &self.input[range];

          if let Ok(address) = PredefinedAddress::try_from(text) {
            let span = span!(start, self.location);
            return Some(Ok(Token::predefined_address(span, address)));
          }

          Some(Ok(Token::named_address(span!(start, self.location))))
        } else {
          // The first byte of the address is an invalid label byte.
          Some(Err(Error::new_invalid_named_address(self.location)))
        }
      } else {
        // Could not consume at least one byte for the address.
        Some(Err(Error::new_unexpected_eof(self.location)))
      }
    } else if byte == b'(' {
      // Found a label start.
      self.location.increment();

      // Expect to consume at least one more valid label byte.
      if let Some(&byte) = self.input.get(self.location.index()) {
        if Self::is_label_start(byte) {
          self.location.increment();

          // Consume label bytes until a non-label byte is reached.
          while let Some(&byte) = self.input.get(self.location.index()) {
            if !Self::is_label_byte(byte) {
              if byte == b')' {
                // The non-label byte is a label closing parenthesis.
                self.location.increment();
                break;
              } else {
                return Some(Err(Error::new_expected_label_closing(self.location)));
              }
            }

            self.location.increment();
          }

          Some(Ok(Token::label(span!(start, self.location))))
        } else {
          // Error if the starting byte is not a valid label byte.
          Some(Err(Error::new_invalid_label_name(self.location)))
        }
      } else {
        // Could not consume at least one byte for the label.
        Some(Err(Error::new_unexpected_eof(self.location)))
      }
    } else if byte == b'=' {
      self.location.increment();
      Some(Ok(Token::equal(span!(start, self.location))))
    } else if byte == b';' {
      self.location.increment();
      Some(Ok(Token::semicolon(span!(start, self.location))))
    } else {
      // Read until an equal `=` (for destinations), semicolon `;`
      // (for computations), newline, whitespace or EOF (for
      // computations and jumps) is reached.
      while let Some(&byte) = self.input.get(self.location.index()) {
        if byte == b'=' {
          // Reached an equal `=`. Check for a destination.
          let range = start.index()..self.location.index();

          if let Ok(destination) = Destination::try_from(dbg!(&self.input[range])) {
            let span = span!(start, self.location);
            return Some(Ok(Token::destination(span, destination)));
          }

          return Some(Err(Error::new_invalid_destination(start)));
        } else if byte == b';' {
          // Reached a semicolon `;`. Check for a computation.
          let range = start.index()..self.location.index();

          if let Ok(computation) = Computation::try_from(&self.input[range]) {
            let span = span!(start, self.location);
            return Some(Ok(Token::computation(span, computation)));
          }

          return Some(Err(Error::new_invalid_computation(start)));
        } else if byte.is_ascii_whitespace() {
          // Newline or whitespace.
          break;
        }

        self.location.increment();
      }

      // Reached newline, whitespace or EOF. Check for a computation.
      let range = start.index()..self.location.index();

      if let Ok(computation) = Computation::try_from(&self.input[range]) {
        return Some(Ok(Token::computation(span!(start, self.location), computation)));
      }

      // Was not a computation, check for a jump.
      let range = start.index()..self.location.index();

      if let Ok(jump) = Jump::try_from(&self.input[range]) {
        return Some(Ok(Token::jump(span!(start, self.location), jump)));
      }

      Some(Err(Error::new_invalid_computation_or_jump(start)))
    }
  }
}

#[cfg(test)]
mod misc_tests {
  use super::Lexer;

  #[test]
  fn label_symbols() {
    assert!(Lexer::is_label_symbol(b'_'));
    assert!(Lexer::is_label_symbol(b'.'));
    assert!(Lexer::is_label_symbol(b'$'));
    assert!(Lexer::is_label_symbol(b':'));
  }

  #[test]
  fn non_label_symbols() {
    assert!(!Lexer::is_label_symbol(b'@'));
    assert!(!Lexer::is_label_symbol(b'^'));
    assert!(!Lexer::is_label_symbol(b'&'));
    assert!(!Lexer::is_label_symbol(b'*'));
    assert!(!Lexer::is_label_symbol(b'('));
    assert!(!Lexer::is_label_symbol(b')'));
    assert!(!Lexer::is_label_symbol(b'%'));
    assert!(!Lexer::is_label_symbol(b'#'));
    assert!(!Lexer::is_label_symbol(b'!'));
  }
}

#[cfg(test)]
mod tests {
  use super::Lexer;
  use crate::hack::Token;
  use crate::span;
  use crate::utilities::Location;
  use crate::utilities::Span;

  macro_rules! lexer {
    ($filename:expr) => {{
      let contents = include_bytes!(concat!("../../tests/snippets/", $filename, ".asm"));
      Lexer::from(contents.to_vec())
    }};
  }

  #[test]
  fn empty() {
    let mut lexer = lexer!("empty");
    assert_eq!(lexer.next(), None);
    assert_eq!(lexer.location.triple(), (0, 1, 1));
  }

  #[test]
  fn newlines() {
    let mut lexer = lexer!("newlines");
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((0, 1, 1), (4, 5, 1))))));
    assert_eq!(lexer.next(), None);
    assert_eq!(lexer.location.triple(), (4, 5, 1));
  }

  #[test]
  fn whitespace() {
    let mut lexer = lexer!("whitespace");

    assert_eq!(lexer.next(), Some(Ok(Token::whitespace(span!((0, 1, 1), (5, 1, 6))))));
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((5, 1, 6), (6, 2, 1))))));

    assert_eq!(lexer.next(), Some(Ok(Token::whitespace(span!((6, 2, 1), (10, 2, 5))))));
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((10, 2, 5), (11, 3, 1))))));

    assert_eq!(lexer.next(), None);
    assert_eq!(lexer.location.triple(), (11, 3, 1));
  }

  #[test]
  fn comments() {
    let mut lexer = lexer!("comments");

    assert_eq!(lexer.next(), Some(Ok(Token::comment(span!((0, 1, 1), (10, 1, 11))))));
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((10, 1, 11), (11, 2, 1))))));

    assert_eq!(lexer.next(), Some(Ok(Token::whitespace(span!((11, 2, 1), (13, 2, 3))))));
    assert_eq!(lexer.next(), Some(Ok(Token::comment(span!((13, 2, 3), (25, 2, 15))))));
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((25, 2, 15), (26, 3, 1))))));

    assert_eq!(lexer.next(), None);
    assert_eq!(lexer.location.triple(), (26, 3, 1));
  }

  #[test]
  fn numeric_addresses() {
    macro_rules! assert_numeric_address {
      ($result:expr, $span:expr, $address:literal) => {
        assert_eq!($result, Some(Ok(Token::numeric_address($span, $address))))
      };
    }

    let mut lexer = lexer!("numeric_addresses");

    assert_numeric_address!(lexer.next(), span!((0, 1, 1), (4, 1, 5)), 123);
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((4, 1, 5), (5, 2, 1))))));

    assert_eq!(lexer.next(), Some(Ok(Token::whitespace(span!((5, 2, 1), (9, 2, 5))))));
    assert_numeric_address!(lexer.next(), span!((9, 2, 5), (14, 2, 10)), 5566);
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((14, 2, 10), (15, 3, 1))))));

    assert_eq!(lexer.next(), None);
    assert_eq!(lexer.location.triple(), (15, 3, 1));
  }

  #[test]
  fn named_addresses() {
    use super::PredefinedAddress;

    macro_rules! assert_predefined_address {
      ($result:expr, $span:expr, $address:ident) => {
        assert_eq!(
          $result,
          Some(Ok(Token::predefined_address($span, PredefinedAddress::$address)))
        );
      };
    }

    macro_rules! assert_named_address {
      ($result:expr, $span:expr) => {
        assert_eq!($result, Some(Ok(Token::named_address($span))))
      };
    }

    let mut lexer = lexer!("named_addresses");

    assert_eq!(lexer.next(), Some(Ok(Token::named_address(span!((0, 1, 1), (4, 1, 5))))));
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((4, 1, 5), (5, 2, 1))))));

    assert_eq!(lexer.next(), Some(Ok(Token::whitespace(span!((5, 2, 1), (7, 2, 3))))));
    assert_named_address!(lexer.next(), span!((7, 2, 3), (11, 2, 7)));
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((11, 2, 7), (12, 3, 1))))));

    assert_eq!(lexer.next(), Some(Ok(Token::whitespace(span!((12, 3, 1), (14, 3, 3))))));
    assert_predefined_address!(lexer.next(), span!((14, 3, 3), (18, 3, 7)), KBD);
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((18, 3, 7), (19, 4, 1))))));

    assert_named_address!(lexer.next(), span!((19, 4, 1), (25, 4, 7)));
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((25, 4, 7), (26, 5, 1))))));

    assert_predefined_address!(lexer.next(), span!((26, 5, 1), (29, 5, 4)), SP);
    assert_eq!(lexer.next(), Some(Ok(Token::whitespace(span!((29, 5, 4), (30, 5, 5))))));
    assert_named_address!(lexer.next(), span!((30, 5, 5), (34, 5, 9)));
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((34, 5, 9), (35, 6, 1))))));

    assert_predefined_address!(lexer.next(), span!((35, 6, 1), (38, 6, 4)), R1);
    assert_eq!(lexer.next(), Some(Ok(Token::whitespace(span!((38, 6, 4), (39, 6, 5))))));
    assert_predefined_address!(lexer.next(), span!((39, 6, 5), (43, 6, 9)), R11);
    assert_eq!(lexer.next(), Some(Ok(Token::whitespace(span!((43, 6, 9), (44, 6, 10))))));
    assert_named_address!(lexer.next(), span!((44, 6, 10), (53, 6, 19)));
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((53, 6, 19), (54, 7, 1))))));

    assert_eq!(lexer.next(), None);
    assert_eq!(lexer.location.triple(), (54, 7, 1));
  }

  #[test]
  fn labels() {
    let mut lexer = lexer!("labels");

    assert_eq!(lexer.next(), Some(Ok(Token::label(span!((0, 1, 1), (7, 1, 8))))));
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((7, 1, 8), (8, 2, 1))))));

    assert_eq!(lexer.next(), Some(Ok(Token::whitespace(span!((8, 2, 1), (10, 2, 3))))));
    assert_eq!(lexer.next(), Some(Ok(Token::label(span!((10, 2, 3), (15, 2, 8))))));
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((15, 2, 8), (16, 3, 1))))));

    assert_eq!(lexer.next(), None);
    assert_eq!(lexer.location.triple(), (16, 3, 1));
  }

  #[test]
  fn instructions() {
    use super::Computation;
    use super::Destination;
    use super::Jump;

    macro_rules! assert_destination {
      ($result:expr, $span:expr, $destination:expr) => {
        assert_eq!($result, Some(Ok(Token::destination($span, $destination))));
      };
    }

    macro_rules! assert_computation {
      ($result:expr, $span:expr, $computation:ident) => {
        assert_eq!(
          $result,
          Some(Ok(Token::computation($span, Computation::$computation)))
        );
      };
    }

    macro_rules! assert_jump {
      ($result:expr, $span:expr, $jump:expr) => {
        assert_eq!($result, Some(Ok(Token::jump($span, $jump))));
      };
    }

    let mut lexer = lexer!("instructions");

    assert_destination!(lexer.next(), span!((0, 1, 1), (1, 1, 2)), Destination::A);
    assert_eq!(lexer.next(), Some(Ok(Token::equal(span!((1, 1, 2), (2, 1, 3))))));
    assert_computation!(lexer.next(), span!((2, 1, 3), (5, 1, 6)), MMinus1);
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((5, 1, 6), (6, 2, 1))))));

    assert_destination!(lexer.next(), span!((6, 2, 1), (8, 2, 3)), Destination::AM);
    assert_eq!(lexer.next(), Some(Ok(Token::equal(span!((8, 2, 3), (9, 2, 4))))));
    assert_computation!(lexer.next(), span!((9, 2, 4), (12, 2, 7)), DOrA);
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((12, 2, 7), (13, 3, 1))))));

    assert_destination!(lexer.next(), span!((13, 3, 1), (16, 3, 4)), Destination::AMD);
    assert_eq!(lexer.next(), Some(Ok(Token::equal(span!((16, 3, 4), (17, 3, 5))))));
    assert_computation!(lexer.next(), span!((17, 3, 5), (20, 3, 8)), APlus1);
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((20, 3, 8), (21, 4, 1))))));

    assert_computation!(lexer.next(), span!((21, 4, 1), (24, 4, 4)), MMinus1);
    assert_eq!(lexer.next(), Some(Ok(Token::semicolon(span!((24, 4, 4), (25, 4, 5))))));
    assert_jump!(lexer.next(), span!((25, 4, 5), (28, 4, 8)), Jump::JEQ);
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((28, 4, 8), (29, 5, 1))))));

    assert_destination!(lexer.next(), span!((29, 5, 1), (31, 5, 3)), Destination::AM);
    assert_eq!(lexer.next(), Some(Ok(Token::equal(span!((31, 5, 3), (32, 5, 4))))));
    assert_computation!(lexer.next(), span!((32, 5, 4), (35, 5, 7)), DOrA);
    assert_eq!(lexer.next(), Some(Ok(Token::semicolon(span!((35, 5, 7), (36, 5, 8))))));
    assert_jump!(lexer.next(), span!((36, 5, 8), (39, 5, 11)), Jump::JNE);
    assert_eq!(lexer.next(), Some(Ok(Token::newlines(span!((39, 5, 11), (40, 6, 1))))));

    assert_eq!(lexer.next(), None);
    assert_eq!(lexer.location.triple(), (40, 6, 1));
  }
}
