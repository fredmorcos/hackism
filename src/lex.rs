#![warn(clippy::all)]

use io::{Bytes, Read};
use std::convert::TryFrom;
use std::fmt;
use std::io;

use atoi::FromRadix10Checked;

use crate::pos::Pos;

pub struct Lex<R: Read> {
  bytes: Bytes<R>,
  pos: Pos,
  la: Option<u8>,
}

impl<R: Read> Lex<R> {
  pub fn new(bytes: Bytes<R>) -> Self {
    Self {
      bytes,
      pos: Pos::default(),
      la: Option::default(),
    }
  }
}

#[derive(PartialEq, Eq)]
pub enum Err {
  IO(Pos, io::ErrorKind),
  EOF(Pos, &'static str),
  Unexpected(Pos, u8, &'static str),
  Range(Pos, Vec<u8>, &'static str),
}

impl fmt::Display for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Err::IO(pos, e) => write!(f, "IO error at {}: {}", pos, io::Error::from(*e)),
      Err::EOF(pos, msg) => write!(f, "Unexpected end of file at {}: {}", pos, msg),
      Err::Unexpected(pos, c, msg) => {
        write!(f, "Unexpected character {} at {}: {}", c, pos, msg)
      }
      Err::Range(pos, addr, msg) => write!(
        f,
        "Value out of range: address {:?} at {}: {}",
        addr, pos, msg
      ),
    }
  }
}

impl fmt::Debug for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    (self as &dyn fmt::Display).fmt(f)
  }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Dest {
  M,
  D,
  MD,
  A,
  AM,
  AD,
  AMD,
}

impl fmt::Display for Dest {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Dest::M => write!(f, "M"),
      Dest::D => write!(f, "D"),
      Dest::MD => write!(f, "MD"),
      Dest::A => write!(f, "A"),
      Dest::AM => write!(f, "AM"),
      Dest::AD => write!(f, "AD"),
      Dest::AMD => write!(f, "AMD"),
    }
  }
}

impl TryFrom<&[u8]> for Dest {
  type Error = ();

  fn try_from(v: &[u8]) -> Result<Self, Self::Error> {
    match v {
      b"M" => Ok(Dest::M),
      b"D" => Ok(Dest::D),
      b"MD" => Ok(Dest::MD),
      b"A" => Ok(Dest::A),
      b"AM" => Ok(Dest::AM),
      b"AD" => Ok(Dest::AD),
      b"AMD" => Ok(Dest::AMD),
      _ => Err(()),
    }
  }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Comp {
  Zero,
  One,
  Neg1,
  D,
  A,
  NotD,
  NotA,
  NegD,
  NegA,
  DPlus1,
  APlus1,
  DMinus1,
  AMinus1,
  DPlusA,
  DMinusA,
  AMinusD,
  DAndA,
  DOrA,
  M,
  NotM,
  NegM,
  MPlus1,
  MMinus1,
  DPlusM,
  DMinusM,
  MMinusD,
  DAndM,
  DOrM,
}

impl fmt::Display for Comp {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Comp::Zero => write!(f, "0"),
      Comp::One => write!(f, "1"),
      Comp::Neg1 => write!(f, "-1"),
      Comp::D => write!(f, "D"),
      Comp::A => write!(f, "A"),
      Comp::NotD => write!(f, "!D"),
      Comp::NotA => write!(f, "!A"),
      Comp::NegD => write!(f, "-D"),
      Comp::NegA => write!(f, "-A"),
      Comp::DPlus1 => write!(f, "D+1"),
      Comp::APlus1 => write!(f, "A+1"),
      Comp::DMinus1 => write!(f, "D-1"),
      Comp::AMinus1 => write!(f, "A-1"),
      Comp::DPlusA => write!(f, "D+A"),
      Comp::DMinusA => write!(f, "D-A"),
      Comp::AMinusD => write!(f, "A-D"),
      Comp::DAndA => write!(f, "D&A"),
      Comp::DOrA => write!(f, "D|A"),
      Comp::M => write!(f, "M"),
      Comp::NotM => write!(f, "!M"),
      Comp::NegM => write!(f, "-M"),
      Comp::MPlus1 => write!(f, "M+1"),
      Comp::MMinus1 => write!(f, "M-1"),
      Comp::DPlusM => write!(f, "D+M"),
      Comp::DMinusM => write!(f, "D-M"),
      Comp::MMinusD => write!(f, "M-D"),
      Comp::DAndM => write!(f, "D&M"),
      Comp::DOrM => write!(f, "D|M"),
    }
  }
}

impl TryFrom<&[u8]> for Comp {
  type Error = ();

  fn try_from(v: &[u8]) -> Result<Self, Self::Error> {
    match v {
      b"0" => Ok(Comp::Zero),
      b"1" => Ok(Comp::One),
      b"-1" => Ok(Comp::Neg1),
      b"D" => Ok(Comp::D),
      b"A" => Ok(Comp::A),
      b"!D" => Ok(Comp::NotD),
      b"!A" => Ok(Comp::NotA),
      b"-D" => Ok(Comp::NegD),
      b"-A" => Ok(Comp::NegA),
      b"D+1" => Ok(Comp::DPlus1),
      b"A+1" => Ok(Comp::APlus1),
      b"D-1" => Ok(Comp::DMinus1),
      b"A-1" => Ok(Comp::AMinus1),
      b"D+A" => Ok(Comp::DPlusA),
      b"D-A" => Ok(Comp::DMinusA),
      b"A-D" => Ok(Comp::AMinusD),
      b"D&A" => Ok(Comp::DAndA),
      b"D|A" => Ok(Comp::DOrA),
      b"M" => Ok(Comp::M),
      b"!M" => Ok(Comp::NotM),
      b"-M" => Ok(Comp::NegM),
      b"M+1" => Ok(Comp::MPlus1),
      b"M-1" => Ok(Comp::MMinus1),
      b"D+M" => Ok(Comp::DPlusM),
      b"D-M" => Ok(Comp::DMinusM),
      b"M-D" => Ok(Comp::MMinusD),
      b"D&M" => Ok(Comp::DAndM),
      b"D|M" => Ok(Comp::DOrM),
      _ => Err(()),
    }
  }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Tok {
  NumAddr(Pos, u16),
  NameAddr(Pos, Vec<u8>),
  Label(Pos, Vec<u8>),
  Dest(Pos, Dest),
  Comp(Pos, Comp),
}

impl Tok {
  fn num_addr(addr: &[u8]) -> Option<u16> {
    if let Some(addr) = u16::from_radix_10_checked(addr).0 {
      // 32767 (15 bits of address value)
      if addr <= 32767 {
        return Some(addr);
      }
    }

    None
  }
}

impl<R: Read> Iterator for Lex<R> {
  type Item = Result<Tok, Err>;

  fn next(&mut self) -> Option<Self::Item> {
    macro_rules! next {
      ($b:block) => {
        match self.bytes.next() {
          Some(Ok(c)) => c,
          Some(Err(e)) => return Some(Err(Err::IO(self.pos, e.kind()))),
          None => $b,
        };
      };
    }

    macro_rules! eof {
      ($msg:expr) => {
        Some(Err(Err::EOF(self.pos, $msg)))
      };
    }

    macro_rules! unexpected {
      ($c:expr, $msg:expr) => {
        Some(Err(Err::Unexpected(self.pos, $c, $msg)))
      };
    }

    fn is_ascii_symbol(c: u8) -> bool {
      c == b'_' || c == b'.' || c == b'$' || c == b':'
    }

    let c1 = if let Some(la) = self.la.take() {
      la
    } else {
      next!({ return None })
    };

    self.pos.inc(c1);

    if c1.is_ascii_whitespace() {
      loop {
        let c2 = next!({ return None });

        if c2.is_ascii_whitespace() {
          self.pos.inc(c2);
        } else {
          self.la = Some(c2);
          return self.next();
        }
      }
    } else if c1 == b'/' {
      static MSG: &str = "a second / to create a comment";

      let c2 = next!({ return eof!(MSG) });
      self.pos.inc(c2);

      if c2 == b'/' {
        loop {
          let c = next!({ return None });
          self.pos.inc(c);

          if c == b'\n' {
            return self.next();
          }
        }
      } else {
        unexpected!(c2, MSG)
      }
    } else if c1 == b'@' {
      static MSG: &str = "an address, name or register";

      let pos = self.pos;
      let c2 = next!({ return eof!(MSG) });
      self.pos.inc(c2);

      if c2.is_ascii_digit() {
        let mut addr = vec![c2];

        loop {
          let c = next!({
            return if let Some(addr) = Tok::num_addr(&addr) {
              Some(Ok(Tok::NumAddr(pos, addr)))
            } else {
              Some(Err(Err::Range(pos, addr, "a numeric address")))
            };
          });
          self.pos.inc(c);

          if c.is_ascii_whitespace() {
            return if let Some(addr) = Tok::num_addr(&addr) {
              Some(Ok(Tok::NumAddr(pos, addr)))
            } else {
              Some(Err(Err::Range(pos, addr, "a numeric address")))
            };
          }

          if !c.is_ascii_digit() {
            return unexpected!(c, "a digit, space or newline to form an address");
          }

          addr.push(c);
        }
      } else if c2.is_ascii_alphabetic() || is_ascii_symbol(c2) {
        let mut addr = vec![c2];

        loop {
          let c = next!({
            return Some(Ok(Tok::NameAddr(pos, addr)));
          });
          self.pos.inc(c);

          if c.is_ascii_whitespace() {
            return Some(Ok(Tok::NameAddr(pos, addr)));
          }

          addr.push(c);
        }
      } else {
        unexpected!(c2, MSG)
      }
    } else if c1 == b'(' {
      static MSG: &str = "a label (cannot start with a digit)";

      let pos = self.pos;
      let c2 = next!({ return eof!(MSG) });
      self.pos.inc(c2);

      if c2.is_ascii_alphabetic() || is_ascii_symbol(c2) {
        let mut label = vec![c2];

        loop {
          let c = next!({ return eof!(MSG) });
          self.pos.inc(c);

          if c == b')' {
            return Some(Ok(Tok::Label(pos, label)));
          }

          if !c.is_ascii_alphabetic() && !is_ascii_symbol(c) {
            return unexpected!(c, MSG);
          }

          label.push(c);
        }
      } else {
        unexpected!(c2, MSG)
      }
    } else {
      static MSG: &str = "a destination (M, D, MD, A, AM, AD or AMD) \
                          or a computation (0, 1, -1, D, A, !D, !A, -D, \
                          -A, D+1, A+1, D-1, A-1, D+A, D-A, A-D, D&A, D|A, \
                          M, !M, -M, M+1, M-1, D+M, D-M, M-D, D&M or D|M)";

      let pos = self.pos;
      let mut dest_or_comp = vec![c1];

      loop {
        let c = next!({
          return if let Ok(dest) = Dest::try_from(dest_or_comp.as_slice()) {
            Some(Ok(Tok::Dest(pos, dest)))
          } else if Comp::try_from(dest_or_comp.as_slice()).is_ok() {
            eof!("a destination (M, D, MD, A, AM, AD or AMD) followed by an = sign")
          } else {
            eof!(MSG)
          };
        });
        self.pos.inc(c);

        if c == b'=' {
          if let Ok(dest) = Dest::try_from(dest_or_comp.as_slice()) {
            return Some(Ok(Tok::Dest(pos, dest)));
          }
        } else if c == b';' || c.is_ascii_whitespace() {
          if let Ok(comp) = Comp::try_from(dest_or_comp.as_slice()) {
            return Some(Ok(Tok::Comp(pos, comp)));
          }
        }

        dest_or_comp.push(c);
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use std::io::{BufReader, Read};

  use crate::pos::Pos;

  use super::Comp;
  use super::Dest;
  use super::Lex;
  use super::Tok;

  macro_rules! lex {
    ($f:expr) => {
      Lex::new(BufReader::new(&include_bytes!(concat!("../tests/data/", $f))[..]).bytes())
    };
  }

  macro_rules! assert_next {
    ($lex:expr, $e:expr) => {
      assert_eq!($lex.next(), Some(Ok($e)))
    };
  }

  #[test]
  fn empty() {
    let mut lex = lex!("empty");
    assert_eq!(lex.pos, Pos::new(1, 0));
    assert_eq!(lex.next(), None);
    assert_eq!(lex.pos, Pos::new(1, 0));
  }

  #[test]
  fn spaces() {
    let mut lex = lex!("spaces");
    assert_eq!(lex.next(), None);
    assert_eq!(lex.pos, Pos::new(5, 0));
  }

  #[test]
  fn comments() {
    let mut lex = lex!("comments");
    assert_eq!(lex.next(), None);
    assert_eq!(lex.pos, Pos::new(5, 0));
  }

  #[test]
  fn num_address() {
    let mut lex = lex!("num_address");
    assert_next!(lex, Tok::NumAddr(Pos::new(3, 5), 8192));
    assert_next!(lex, Tok::NumAddr(Pos::new(5, 1), 123));
    assert_next!(lex, Tok::NumAddr(Pos::new(9, 5), 556));
    assert_eq!(lex.next(), None);
  }

  #[test]
  fn name_address() {
    let mut lex = lex!("name_address");
    assert_eq!(
      lex.next(),
      Some(Ok(Tok::NameAddr(Pos::new(3, 5), Vec::from(&b"FOO"[..]))))
    );
    assert_eq!(
      lex.next(),
      Some(Ok(Tok::NameAddr(Pos::new(5, 1), Vec::from(&b"BAR"[..]))))
    );
    assert_eq!(
      lex.next(),
      Some(Ok(Tok::NameAddr(Pos::new(9, 5), Vec::from(&b"R2"[..]))))
    );
    assert_eq!(lex.next(), None);
  }

  #[test]
  fn labels() {
    let mut lex = lex!("labels");
    assert_eq!(
      lex.next(),
      Some(Ok(Tok::NameAddr(Pos::new(3, 5), Vec::from(&b"FOO"[..]))))
    );
    assert_eq!(
      lex.next(),
      Some(Ok(Tok::Label(Pos::new(5, 1), Vec::from(&b"LABEL"[..]))))
    );
    assert_eq!(
      lex.next(),
      Some(Ok(Tok::NameAddr(Pos::new(9, 5), Vec::from(&b"LABEL"[..]))))
    );
    assert_eq!(
      lex.next(),
      Some(Ok(Tok::NameAddr(Pos::new(11, 1), Vec::from(&b"BAR"[..]))))
    );
    assert_eq!(
      lex.next(),
      Some(Ok(Tok::Label(Pos::new(13, 1), Vec::from(&b"BAR"[..]))))
    );
    assert_eq!(lex.next(), None);
  }

  #[test]
  fn assignments() {
    let mut lex = lex!("assignments");
    assert_eq!(lex.next(), Some(Ok(Tok::Dest(Pos::new(1, 1), Dest::A))));
    assert_eq!(
      lex.next(),
      Some(Ok(Tok::Comp(Pos::new(1, 3), Comp::MMinus1)))
    );
    assert_eq!(lex.next(), Some(Ok(Tok::Dest(Pos::new(2, 1), Dest::AM))));
    assert_eq!(lex.next(), Some(Ok(Tok::Comp(Pos::new(2, 4), Comp::DOrA))));
    assert_eq!(lex.next(), Some(Ok(Tok::Dest(Pos::new(3, 1), Dest::AMD))));
    assert_eq!(
      lex.next(),
      Some(Ok(Tok::Comp(Pos::new(3, 5), Comp::APlus1)))
    );
    assert_eq!(lex.next(), None);
  }
}
