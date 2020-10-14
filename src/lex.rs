#![warn(clippy::all)]

use io::{Bytes, Read};
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
pub enum Tok {
  NumAddr(Pos, u16),
  NameAddr(Pos, Vec<u8>),
  Label(Pos, Vec<u8>),
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
      Some(Err(Err::Unknown(self.pos, c1)))
    }
  }
}

#[cfg(test)]
mod tests {
  use std::io::{BufReader, Read};

  use crate::pos::Pos;

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
}
