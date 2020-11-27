#![warn(clippy::all)]

mod ascii;
mod errors;
mod helpers;
mod tokens;

use either::Either;

use crate::address_range;
use crate::eof;
use crate::location::Location;
use crate::location::SourceLocation;
use crate::source_location;
use crate::unexpected_token;

use self::ascii::is_label_byte;
use self::ascii::is_label_start;
use self::errors::Error;
use self::tokens::Computation;
use self::tokens::Destination;
use self::tokens::Token;

pub struct Scanner<'b> {
  buffer: &'b [u8],
  current_location: Location,
  token_location: Location,
}

impl<'b> From<&'b [u8]> for Scanner<'b> {
  fn from(buffer: &'b [u8]) -> Self {
    Self {
      buffer,
      current_location: Location::default(),
      token_location: Location::default(),
    }
  }
}

macro_rules! make_address_label {
  ($lifetime:lifetime) => {
    |label: &$lifetime [u8]| Token::AddressLabel(&label[1..])
  };
}

macro_rules! label_next {
  ($scanner:expr, $index:expr, $token_closure:expr
   $( , $byte:expr => $block:block )*) => {
    match $scanner.buffer.get($index) {
      $( Some(&$byte) => $block ),*
      Some(&byte) if is_label_byte(byte) => return $scanner.address_label($index + 1),
      Some(&byte) if byte.is_ascii_whitespace() => {
        $scanner.current_location.increment_non_newline_by($index - 1);
        let split = $scanner.buffer.split_at($index);
        $scanner.buffer = split.1;
        return Some(Ok($token_closure(split.0)));
      }
      Some(&byte) => return unexpected_token!(byte, "a label address"),
      None => {
        $scanner.current_location.increment_non_newline_by($index - 1);
        let split = $scanner.buffer.split_at($index);
        $scanner.buffer = split.1;
        return Some(Ok($token_closure(split.0)));
      }
    }
  };
}

macro_rules! instruction_next {
  ($scanner:expr, $index:expr, $expect:expr
   $( , $whitespace_block:block )?
   $( , $byte:expr => $block:block )*) => {
    match $scanner.buffer.get($index) {
      $( Some(&$byte) => $block ),*
      $( Some(&byte) if byte.is_ascii_whitespace() => $whitespace_block, )?
      Some(&byte) => unexpected_token!(byte, $expect),
      None => eof!($expect),
    }
  };
}

type Output<T> = Option<Result<T, Error>>;
type TokenOutput<'b> = Output<Token<'b>>;

impl<'b> Scanner<'b> {
  pub fn token_location(&self) -> Location {
    self.token_location
  }

  pub fn current_location(&self) -> Location {
    self.current_location
  }

  #[inline(always)]
  fn skip_whitespace(&mut self, mut index: usize) {
    while let Some(&byte) = self.buffer.get(index) {
      if !byte.is_ascii_whitespace() {
        break;
      }

      self.current_location.increment(byte);
      index += 1;
    }

    self.buffer = self.buffer.split_at(index).1;
  }

  #[inline(always)]
  fn skip_comment(&mut self, mut index: usize) {
    while let Some(&byte) = self.buffer.get(index) {
      if byte == b'\n' {
        break;
      }

      index += 1;
    }

    self.buffer = self.buffer.split_at(index).1;
  }

  #[inline(always)]
  fn label(&mut self, mut index: usize) -> TokenOutput {
    while let Some(&byte) = self.buffer.get(index) {
      if !is_label_byte(byte) {
        self.current_location.increment_non_newline_by(index - 1);

        if byte.is_ascii_whitespace() {
          return unexpected_token!(byte, "a label");
        } else if byte == b')' {
          index += 1;
        }

        break;
      }

      index += 1;
    }

    let split = self.buffer.split_at(index);
    self.buffer = split.1;

    Some(Ok(Token::Label(&split.0[1..index - 1])))
  }

  #[inline(always)]
  fn address_numerical(&mut self, mut index: usize) -> TokenOutput {
    while let Some(&byte) = self.buffer.get(index) {
      if !byte.is_ascii_digit() {
        self.current_location.increment_non_newline_by(index - 1);

        if !byte.is_ascii_whitespace() {
          return unexpected_token!(byte, "a numerical address");
        }

        break;
      }

      index += 1;
    }

    let split = self.buffer.split_at(index);
    self.buffer = split.1;

    if let Some(address) = Token::new_numerical_address(&split.0[1..]) {
      Some(Ok(Token::AddressNumerical(address)))
    } else {
      address_range!("a value within the range of 15 bits (0-32767)")
    }
  }

  #[inline(always)]
  fn address_label(&mut self, mut index: usize) -> TokenOutput {
    while let Some(&byte) = self.buffer.get(index) {
      if !is_label_byte(byte) {
        self.current_location.increment_non_newline_by(index - 1);

        if !byte.is_ascii_whitespace() {
          return unexpected_token!(byte, "a label address");
        }

        break;
      }

      index += 1;
    }

    let split = self.buffer.split_at(index);
    self.buffer = split.1;

    Some(Ok(Token::AddressLabel(&split.0[1..])))
  }

  #[inline(always)]
  fn address_label_s(&mut self, index: usize) -> TokenOutput {
    label_next! {
      self, index, make_address_label!('b),
      b'P' => { label_next!(self, index + 1, |_| Token::AddressSP) },
      b'C' => {}
    };
    label_next!(self, index + 1, make_address_label!('b), b'R' => {});
    label_next!(self, index + 2, make_address_label!('b), b'E' => {});
    label_next!(self, index + 3, make_address_label!('b), b'E' => {});
    label_next!(self, index + 4, make_address_label!('b), b'N' => {});
    label_next!(self, index + 5, |_| Token::AddressSCREEN);
  }

  #[inline(always)]
  fn address_label_r(&mut self, index: usize) -> TokenOutput {
    label_next! {
      self, index, make_address_label!('b),
      b'0' => { label_next!(self, index + 1, |_| Token::AddressR0) },
      b'1' => {},
      b'2' => { label_next!(self, index + 1, |_| Token::AddressR2) },
      b'3' => { label_next!(self, index + 1, |_| Token::AddressR3) },
      b'4' => { label_next!(self, index + 1, |_| Token::AddressR4) },
      b'5' => { label_next!(self, index + 1, |_| Token::AddressR5) },
      b'6' => { label_next!(self, index + 1, |_| Token::AddressR6) },
      b'7' => { label_next!(self, index + 1, |_| Token::AddressR7) },
      b'8' => { label_next!(self, index + 1, |_| Token::AddressR8) },
      b'9' => { label_next!(self, index + 1, |_| Token::AddressR9) }
    };
    label_next! {
      self, index + 1, |_| Token::AddressR1,
      b'0' => { label_next!(self, index + 2, |_| Token::AddressR10) },
      b'1' => { label_next!(self, index + 2, |_| Token::AddressR11) },
      b'2' => { label_next!(self, index + 2, |_| Token::AddressR12) },
      b'3' => { label_next!(self, index + 2, |_| Token::AddressR13) },
      b'4' => { label_next!(self, index + 2, |_| Token::AddressR14) },
      b'5' => { label_next!(self, index + 2, |_| Token::AddressR15) }
    };
  }

  #[inline(always)]
  fn address_label_t(&mut self, index: usize) -> TokenOutput {
    label_next!(self, index, make_address_label!('b), b'H' => {});
    label_next! {
      self, index + 1, make_address_label!('b),
      b'I' => {},
      b'A' => {
        label_next! {
          self, index + 2, make_address_label!('b),
          b'T' => {
            label_next!(self, index + 3, |_| Token::AddressTHAT);
          }
        }
      }
    };
    label_next!(self, index + 2, make_address_label!('b), b'S' => {});
    label_next!(self, index + 3, |_| Token::AddressTHIS);
  }

  #[inline(always)]
  fn address_label_k(&mut self, index: usize) -> TokenOutput {
    label_next!(self, index, make_address_label!('b), b'B' => {});
    label_next!(self, index + 1, make_address_label!('b), b'D' => {});
    label_next!(self, index + 2, |_| Token::AddressKBD);
  }

  #[inline(always)]
  fn address_label_l(&mut self, index: usize) -> TokenOutput {
    label_next!(self, index, make_address_label!('b), b'C' => {});
    label_next!(self, index + 1, make_address_label!('b), b'L' => {});
    label_next!(self, index + 2, |_| Token::AddressLCL);
  }

  #[inline(always)]
  fn address_label_a(&mut self, index: usize) -> TokenOutput {
    label_next!(self, index, make_address_label!('b), b'R' => {});
    label_next!(self, index + 1, make_address_label!('b), b'G' => {});
    label_next!(self, index + 2, |_| Token::AddressARG);
  }

  #[inline(always)]
  fn destination_or_computation_a(
    &mut self, index: usize,
  ) -> Output<(Either<Destination, Computation>, u8)> {
    instruction_next! {
      self, index, "A, AM, AD, AMD, A+1, A-1 or A-D",
      b'M' => {
        instruction_next! {
          self, index + 1, "AM or AMD",
          b'D' => {
            instruction_next! {
              self, index + 2, "AMD",
              b'=' => { Some(Ok((Either::Left(Destination::AMD), b'='))) }
            }
          },
          b'=' => { Some(Ok((Either::Left(Destination::AM), b'='))) }
        }
      },
      b'D' => {
        instruction_next! {
          self, index + 1, "AD",
          b'=' => { Some(Ok((Either::Left(Destination::AD), b'='))) }
        }
      },
      b'=' => { Some(Ok((Either::Left(Destination::A), b'='))) },
      b';' => { Some(Ok((Either::Right(Computation::A), b';'))) }
    }
  }

  #[inline(always)]
  fn computation_a(&mut self, index: usize) -> TokenOutput {
    instruction_next! {
      self, index, "A+1, A-1 or A-D",
      b'+' => {
        instruction_next! {
          self, index + 1, "A+1",
          b'1' => {
            instruction_next! {
              self, index + 2, "A+1",
              b'=' => { todo!() }
            }
          }
        }
      },
      b'-' => {
        instruction_next! {
          self, index + 1, "A-1 or A-D",
          b'1' => {
            instruction_next! {
              self, index + 2, "A-1",
              b'=' => { todo!() }
            }
          },
          b'D' => {
            instruction_next! {
              self, index + 2, "A-D",
              b'=' => { todo!() }
            }
          }
        }
      },
      b';' => { todo!() }
    }
  }

  pub fn next(&mut self) -> TokenOutput {
    'MAIN_LOOP: loop {
      let byte0 = *self.buffer.get(0)?;

      if byte0.is_ascii_whitespace() {
        self.current_location.increment(byte0);
        self.skip_whitespace(1);
        continue 'MAIN_LOOP;
      } else if byte0 == b'/' {
        self.current_location.increment_non_newline();
        if let Some(&b'/') = self.buffer.get(1) {
          self.skip_comment(2);
          continue 'MAIN_LOOP;
        } else {
          return eof!("a second forward slash (/) to form a comment");
        }
      } else if byte0 == b'(' {
        self.current_location.increment_non_newline();
        self.token_location = self.current_location;
        return match self.buffer.get(1) {
          Some(&byte1) if is_label_start(byte1) => self.label(2),
          Some(&byte1) => unexpected_token!(byte1, "a label"),
          None => eof!("a label"),
        };
      } else if byte0 == b'@' {
        self.current_location.increment_non_newline();
        self.token_location = self.current_location;

        return match self.buffer.get(1) {
          Some(b'S') => self.address_label_s(2),
          Some(b'L') => self.address_label_l(2),
          Some(b'A') => self.address_label_a(2),
          Some(b'T') => self.address_label_t(2),
          Some(b'R') => self.address_label_r(2),
          Some(b'K') => self.address_label_k(2),
          Some(&byte1) if is_label_start(byte1) => self.address_label(2),
          Some(byte1) if byte1.is_ascii_digit() => self.address_numerical(2),
          Some(&byte1) => unexpected_token!(byte1, "a label address"),
          None => eof!("a numerical or label address"),
        };
      // } else if byte0 == b'A' {
      //   return self.destination_or_computation_a(2);
      // } else if byte0 == b'M' {
      //   self.destination_or_computation_m(2)
      // } else if byte0 == b'D' {
      //   self.destination_or_computation_d(2)
      // } else if byte0 == b'-' {
      //   self.computation_neg(2)
      // } else if byte0 == b'!' {
      //   self.computation_not(2)
      } else {
        return None;
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::tokens::Computation;
  use super::tokens::Destination;
  use super::tokens::Jump;
  use super::Scanner;
  use super::Token;
  use crate::location::Location;

  macro_rules! scanner {
    ($f:expr) => {
      Scanner::from(&include_bytes!(concat!("../tests/data/", $f))[..])
    };
  }

  macro_rules! assert_next {
    ($scanner:expr, $expected_token:expr, $expected_location:expr) => {
      assert_eq!($scanner.next(), Some(Ok($expected_token)));
      assert_eq!($scanner.token_location(), $expected_location);
    };
  }

  #[test]
  fn empty() {
    let mut scanner = scanner!("empty");
    assert_eq!(scanner.current_location, Location::new(1, 0));
    assert_eq!(scanner.next(), None);
    assert_eq!(scanner.current_location, Location::new(1, 0));
  }

  #[test]
  fn spaces() {
    let mut scanner = scanner!("spaces");
    assert_eq!(scanner.next(), None);
    assert_eq!(scanner.current_location, Location::new(5, 0));
  }

  #[test]
  fn comments() {
    let mut scanner = scanner!("comments");
    assert_eq!(scanner.next(), None);
    assert_eq!(scanner.current_location, Location::new(5, 0));
  }

  #[test]
  fn address_numericals() {
    let mut scanner = scanner!("address_numericals");
    assert_next!(scanner, Token::AddressNumerical(8192), Location::new(3, 5));
    assert_next!(scanner, Token::AddressNumerical(123), Location::new(5, 1));
    assert_next!(scanner, Token::AddressNumerical(556), Location::new(9, 5));
    assert_eq!(scanner.next(), None);
  }

  #[test]
  fn address_labels() {
    let mut scanner = scanner!("address_labels");
    assert_next!(
      scanner,
      Token::AddressLabel(&b"FOO"[..]),
      Location::new(3, 5)
    );
    assert_next!(
      scanner,
      Token::AddressLabel(&b"BARBAZ"[..]),
      Location::new(5, 1)
    );
    assert_next!(scanner, Token::AddressKBD, Location::new(9, 5));
    assert_next!(
      scanner,
      Token::AddressLabel(&b"BAZOO"[..]),
      Location::new(11, 1)
    );
    assert_next!(scanner, Token::AddressLCL, Location::new(13, 1));
    assert_next!(
      scanner,
      Token::AddressLabel(&b"LCLCL"[..]),
      Location::new(13, 6)
    );
    assert_next!(scanner, Token::AddressSCREEN, Location::new(14, 1));
    assert_next!(scanner, Token::AddressSP, Location::new(14, 9));
    assert_next!(
      scanner,
      Token::AddressLabel(&b"SPP"[..]),
      Location::new(14, 13)
    );
    assert_next!(scanner, Token::AddressARG, Location::new(15, 1));
    assert_next!(
      scanner,
      Token::AddressLabel(&b"ARG0"[..]),
      Location::new(15, 6)
    );
    assert_next!(scanner, Token::AddressTHIS, Location::new(16, 1));
    assert_next!(scanner, Token::AddressTHAT, Location::new(16, 7));
    assert_next!(
      scanner,
      Token::AddressLabel(&b"THOSE"[..]),
      Location::new(16, 13)
    );
    assert_next!(scanner, Token::AddressR0, Location::new(17, 1));
    assert_next!(scanner, Token::AddressR1, Location::new(17, 5));
    assert_next!(scanner, Token::AddressR11, Location::new(17, 9));
    assert_next!(
      scanner,
      Token::AddressLabel(&b"R1_hello"[..]),
      Location::new(17, 14)
    );
    assert_next!(
      scanner,
      Token::AddressLabel(&b"R11_hello"[..]),
      Location::new(17, 24)
    );
    assert_eq!(scanner.next(), None);
  }

  #[test]
  fn label() {
    let mut scanner = scanner!("label");
    assert_next!(
      scanner,
      Token::AddressLabel(&b"FOO"[..]),
      Location::new(3, 5)
    );
    assert_next!(scanner, Token::Label(&b"LABEL"[..]), Location::new(5, 1));
    assert_next!(
      scanner,
      Token::AddressLabel(&b"LABEL"[..]),
      Location::new(9, 5)
    );
    assert_next!(
      scanner,
      Token::AddressLabel(&b"BAR"[..]),
      Location::new(11, 1)
    );
    assert_next!(scanner, Token::Label(&b"BAR"[..]), Location::new(13, 1));
    assert_next!(
      scanner,
      Token::AddressLabel(&b"LAB0"[..]),
      Location::new(15, 1)
    );
    assert_next!(scanner, Token::Label(&b"LAB0"[..]), Location::new(17, 1));
    assert_eq!(scanner.next(), None);
  }

  #[test]
  fn assignments() {
    let mut scanner = scanner!("assignments");
    assert_next!(
      scanner,
      Token::Assignment(Destination::A, Computation::MMinus1),
      Location::new(1, 1)
    );
    assert_next!(
      scanner,
      Token::Assignment(Destination::AM, Computation::DOrA),
      Location::new(2, 1)
    );
    assert_next!(
      scanner,
      Token::Assignment(Destination::AMD, Computation::APlus1),
      Location::new(3, 1)
    );
    assert_eq!(scanner.next(), None);
  }

  // #[test]
  // fn branches() {
  //   let mut scanner = scanner!("branches");
  //   assert_next!(scanner, tbuf, Token::Comp(Comp::MMinus1));
  //   assert_eq!(scanner.token_pos(), Location::new(1, 1));
  //   assert_next!(scanner, tbuf, Token::Semi);
  //   assert_eq!(scanner.token_pos(), Location::new(1, 4));
  //   assert_next!(scanner, tbuf, Token::Jump(Jump::JEQ));
  //   assert_eq!(scanner.token_pos(), Location::new(1, 5));
  //   assert_next!(scanner, tbuf, Token::Comp(Comp::DOrA));
  //   assert_eq!(scanner.token_pos(), Location::new(2, 1));
  //   assert_next!(scanner, tbuf, Token::Semi);
  //   assert_eq!(scanner.token_pos(), Location::new(2, 4));
  //   assert_next!(scanner, tbuf, Token::Jump(Jump::JNE));
  //   assert_eq!(scanner.token_pos(), Location::new(2, 5));
  //   assert_next!(scanner, tbuf, Token::Comp(Comp::APlus1));
  //   assert_eq!(scanner.token_pos(), Location::new(3, 1));
  //   assert_next!(scanner, tbuf, Token::Semi);
  //   assert_eq!(scanner.token_pos(), Location::new(3, 4));
  //   assert_next!(scanner, tbuf, Token::Jump(Jump::JMP));
  //   assert_eq!(scanner.token_pos(), Location::new(3, 5));
  //   assert_eq!(scanner.next(), None);
  // }

  // #[test]
  // fn instructions() {
  //   let mut scanner = scanner!("instructions");
  //   assert_next!(scanner, tbuf, Token::Dest(Dest::A));
  //   assert_eq!(scanner.token_pos(), Location::new(1, 1));
  //   assert_next!(scanner, tbuf, Token::Comp(Comp::MMinus1));
  //   assert_eq!(scanner.token_pos(), Location::new(1, 3));
  //   assert_next!(scanner, tbuf, Token::Semi);
  //   assert_eq!(scanner.token_pos(), Location::new(1, 6));
  //   assert_next!(scanner, tbuf, Token::Jump(Jump::JEQ));
  //   assert_eq!(scanner.token_pos(), Location::new(1, 7));
  //   assert_next!(scanner, tbuf, Token::Dest(Dest::AM));
  //   assert_eq!(scanner.token_pos(), Location::new(2, 1));
  //   assert_next!(scanner, tbuf, Token::Comp(Comp::DOrA));
  //   assert_eq!(scanner.token_pos(), Location::new(2, 4));
  //   assert_next!(scanner, tbuf, Token::Semi);
  //   assert_eq!(scanner.token_pos(), Location::new(2, 7));
  //   assert_next!(scanner, tbuf, Token::Jump(Jump::JNE));
  //   assert_eq!(scanner.token_pos(), Location::new(2, 8));
  //   assert_next!(scanner, tbuf, Token::Dest(Dest::AMD));
  //   assert_eq!(scanner.token_pos(), Location::new(3, 1));
  //   assert_next!(scanner, tbuf, Token::Comp(Comp::APlus1));
  //   assert_eq!(scanner.token_pos(), Location::new(3, 5));
  //   assert_next!(scanner, tbuf, Token::Semi);
  //   assert_eq!(scanner.token_pos(), Location::new(3, 8));
  //   assert_next!(scanner, tbuf, Token::Jump(Jump::JMP));
  //   assert_eq!(scanner.token_pos(), Location::new(3, 9));
  //   assert_eq!(scanner.next(), None);
  // }
}
