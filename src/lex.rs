#![warn(clippy::all)]

use std::fmt;
use std::slice;

use atoi::FromRadix10Checked;
use smallvec::SmallVec;

use crate::loc::Loc;

pub type Txt = SmallVec<[u8; 32]>;

pub struct Lex<'buf> {
  buf: slice::Iter<'buf, u8>,
  tbuf: Txt,
  pos: Loc,
  tpos: Loc,
  la: Option<u8>,
}

impl<'buf> From<&'buf [u8]> for Lex<'buf> {
  fn from(buf: &'buf [u8]) -> Self {
    Self {
      buf: buf.iter(),
      tbuf: Txt::default(),
      pos: Loc::default(),
      tpos: Loc::default(),
      la: Option::default(),
    }
  }
}

#[derive(PartialEq, Eq)]
pub enum Err {
  EOF(&'static str, u32, Loc, &'static str),
  Unexpected(&'static str, u32, Loc, u8, &'static str),
  Range(&'static str),
}

impl fmt::Display for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Err::EOF(file, line, pos, msg) => write!(
        f,
        "{}:{}: Unexpected end of file at {}: {}",
        file, line, pos, msg
      ),
      Err::Unexpected(file, line, pos, c, msg) => write!(
        f,
        "{}:{}: Unexpected character {} at {}: {}",
        file, line, c, pos, msg
      ),
      Err::Range(msg) => write!(f, "Value out of range (expecting {})", msg),
    }
  }
}

impl fmt::Debug for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    (self as &dyn fmt::Display).fmt(f)
  }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Jump {
  JGT,
  JEQ,
  JGE,
  JLT,
  JNE,
  JLE,
  JMP,
}

impl fmt::Display for Jump {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Jump::JGT => write!(f, "JGT"),
      Jump::JEQ => write!(f, "JEQ"),
      Jump::JGE => write!(f, "JGE"),
      Jump::JLT => write!(f, "JLT"),
      Jump::JNE => write!(f, "JNE"),
      Jump::JLE => write!(f, "JLE"),
      Jump::JMP => write!(f, "JMP"),
    }
  }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Tok {
  NumAddr(u16),
  NameAddr,
  Label,
  Semi,
  Dest(Dest),
  Comp(Comp),
  Jump(Jump),
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

macro_rules! next {
  ($buf:expr, $b:block) => {
    match $buf.next() {
      Some(c) => *c,
      None => $b,
    };
  };
}

macro_rules! eof {
  ($pos:expr, $msg:expr) => {
    Some(Err(Err::EOF(file!(), line!(), $pos, $msg)))
  };
}

macro_rules! unexpected {
  ($pos:expr, $c:expr, $msg:expr) => {
    Some(Err(Err::Unexpected(file!(), line!(), $pos, $c, $msg)))
  };
}

impl Lex<'_> {
  pub fn token_pos(&self) -> Loc {
    self.tpos
  }

  pub fn text(&self) -> &Txt {
    &self.tbuf
  }

  pub fn take_text(&mut self) -> Txt {
    std::mem::take(&mut self.tbuf)
  }

  pub fn whitespace(&mut self) -> Option<Result<Tok, Err>> {
    loop {
      let c2 = next!(self.buf, { return None });

      if c2.is_ascii_whitespace() {
        self.pos.inc(c2);
      } else {
        self.la = Some(c2);
        return self.next();
      }
    }
  }

  pub fn comment(&mut self) -> Option<Result<Tok, Err>> {
    static MSG: &str = "a second / to create a comment";

    let c2 = next!(self.buf, { return eof!(self.pos, MSG) });
    self.pos.inc(c2);

    if c2 == b'/' {
      loop {
        let c = next!(self.buf, { return None });
        self.pos.inc(c);

        if c == b'\n' {
          return self.next();
        }
      }
    } else {
      unexpected!(self.pos, c2, MSG)
    }
  }

  pub fn next(&mut self) -> Option<Result<Tok, Err>> {
    macro_rules! dest {
      ($v:ident) => {
        Some(Ok(Tok::Dest(Dest::$v)))
      };
    }

    macro_rules! comp {
      ($v:ident) => {
        Some(Ok(Tok::Comp(Comp::$v)))
      };
    }

    macro_rules! jump {
      ($v:ident) => {
        Some(Ok(Tok::Jump(Jump::$v)))
      };
    }

    fn is_ascii_symbol(c: u8) -> bool {
      c == b'_' || c == b'.' || c == b'$' || c == b':'
    }

    let c1 = if let Some(la) = self.la.take() {
      la
    } else {
      next!(self.buf, { return None })
    };

    self.pos.inc(c1);

    if c1.is_ascii_whitespace() {
      self.whitespace()
    } else if c1 == b'/' {
      self.comment()
    } else if c1 == b'@' {
      static MSG: &str = "an address, name or register";

      self.tpos = self.pos;
      let c2 = next!(self.buf, { return eof!(self.pos, MSG) });
      self.pos.inc(c2);

      if c2.is_ascii_digit() {
        self.tbuf.clear();
        self.tbuf.push(c2);

        loop {
          let c = next!(self.buf, {
            return if let Some(addr) = Tok::num_addr(&self.tbuf) {
              Some(Ok(Tok::NumAddr(addr)))
            } else {
              Some(Err(Err::Range("a numeric address")))
            };
          });
          self.pos.inc(c);

          if c.is_ascii_whitespace() {
            return if let Some(addr) = Tok::num_addr(&self.tbuf) {
              Some(Ok(Tok::NumAddr(addr)))
            } else {
              Some(Err(Err::Range("a numeric address")))
            };
          }

          if !c.is_ascii_digit() {
            return unexpected!(
              self.pos,
              c,
              "a digit, space or newline to form an address"
            );
          }

          self.tbuf.push(c);
        }
      } else if c2.is_ascii_alphabetic() || is_ascii_symbol(c2) {
        self.tbuf.clear();
        self.tbuf.push(c2);

        loop {
          let c = next!(self.buf, {
            return Some(Ok(Tok::NameAddr));
          });
          self.pos.inc(c);

          if c.is_ascii_whitespace() {
            return Some(Ok(Tok::NameAddr));
          }

          self.tbuf.push(c);
        }
      } else {
        unexpected!(self.pos, c2, MSG)
      }
    } else if c1 == b'(' {
      static MSG: &str = "a label (cannot start with a digit)";

      self.tpos = self.pos;
      let c2 = next!(self.buf, { return eof!(self.pos, MSG) });
      self.pos.inc(c2);

      if c2.is_ascii_alphabetic() || is_ascii_symbol(c2) {
        self.tbuf.clear();
        self.tbuf.push(c2);

        loop {
          let c = next!(self.buf, { return eof!(self.pos, MSG) });
          self.pos.inc(c);

          if c == b')' {
            return Some(Ok(Tok::Label));
          }

          if !c.is_ascii_alphanumeric() && !is_ascii_symbol(c) {
            return unexpected!(self.pos, c, MSG);
          }

          self.tbuf.push(c);
        }
      } else {
        unexpected!(self.pos, c2, MSG)
      }
    } else if c1 == b'J' {
      self.tpos = self.pos;
      let c2 = next!(self.buf, {
        return eof!(self.pos, "JGT|JEQ|JGE|JLT|JNE|JLE|JMP");
      });
      self.pos.inc(c2);
      match c2 {
        b'G' => {
          let c3 = next!(self.buf, { return eof!(self.pos, "JGT|JGE") });
          self.pos.inc(c3);
          match c3 {
            b'T' => jump!(JGT),
            b'E' => jump!(JGE),
            c => unexpected!(self.pos, c, "JGT|JGE"),
          }
        }
        b'E' => {
          let c3 = next!(self.buf, { return eof!(self.pos, "JEQ") });
          self.pos.inc(c3);
          match c3 {
            b'Q' => jump!(JEQ),
            c => unexpected!(self.pos, c, "JEQ"),
          }
        }
        b'L' => {
          let c3 = next!(self.buf, { return eof!(self.pos, "JLT|JLE") });
          self.pos.inc(c3);
          match c3 {
            b'T' => jump!(JLT),
            b'E' => jump!(JLE),
            c => unexpected!(self.pos, c, "JLT|JLE"),
          }
        }
        b'N' => {
          let c3 = next!(self.buf, { return eof!(self.pos, "JNE") });
          self.pos.inc(c3);
          match c3 {
            b'E' => jump!(JNE),
            c => unexpected!(self.pos, c, "JNE"),
          }
        }
        b'M' => {
          let c3 = next!(self.buf, { return eof!(self.pos, "JMP") });
          self.pos.inc(c3);
          match c3 {
            b'P' => jump!(JMP),
            c => unexpected!(self.pos, c, "JMP"),
          }
        }
        c => unexpected!(self.pos, c, "JGT|JEQ|JGE|JLT|JNE|JLE|JMP"),
      }
    } else if c1 == b'A' {
      self.tpos = self.pos;
      let c2 = next!(self.buf, { return comp!(A) });
      self.pos.inc(c2);
      match c2 {
        b'M' => {
          let c3 = next!(self.buf, {
            return eof!(self.pos, "an instruction AM[D]=...");
          });
          self.pos.inc(c3);
          match c3 {
            b'D' => {
              let c4 = next!(self.buf, {
                return eof!(self.pos, "an instruction AMD=...");
              });
              self.pos.inc(c4);
              match c4 {
                b'=' => dest!(AMD),
                c => unexpected!(self.pos, c, "an instruction AMD=..."),
              }
            }
            b'=' => Some(Ok(Tok::Dest(Dest::AM))),
            c => unexpected!(self.pos, c, "an instruction AM[D]=..."),
          }
        }
        b'D' => {
          let c3 = next!(self.buf, { return eof!(self.pos, "an instruction AD=...") });
          self.pos.inc(c3);
          match c3 {
            b'=' => dest!(AD),
            c => unexpected!(self.pos, c, "an instruction AD=..."),
          }
        }
        b'+' => {
          let c3 = next!(self.buf, { return eof!(self.pos, "a computation A+1") });
          self.pos.inc(c3);
          match c3 {
            b'1' => comp!(APlus1),
            c => unexpected!(self.pos, c, "a computation A+1"),
          }
        }
        b'-' => {
          let c3 = next!(self.buf, { return eof!(self.pos, "a computation A-1|A-D") });
          self.pos.inc(c3);
          match c3 {
            b'1' => comp!(AMinus1),
            b'D' => comp!(AMinusD),
            c => unexpected!(self.pos, c, "a computation A-1|A-D"),
          }
        }
        b'=' => dest!(A),
        b';' => {
          self.la = Some(b';');
          comp!(A)
        }
        c if c.is_ascii_whitespace() => comp!(A),
        c => unexpected!(self.pos, c, "a destination A= or a computation A"),
      }
    } else if c1 == b'M' {
      self.tpos = self.pos;
      let c2 = next!(self.buf, { return comp!(M) });
      self.pos.inc(c2);
      match c2 {
        b'D' => {
          let c3 = next!(self.buf, { return eof!(self.pos, "an instruction MD=...") });
          self.pos.inc(c3);
          match c3 {
            b'=' => dest!(MD),
            c => unexpected!(self.pos, c, "an instruction MD=..."),
          }
        }
        b'+' => {
          let c3 = next!(self.buf, { return eof!(self.pos, "a computation M+1") });
          self.pos.inc(c3);
          match c3 {
            b'1' => comp!(MPlus1),
            c => unexpected!(self.pos, c, "a computation M+1"),
          }
        }
        b'-' => {
          let c3 = next!(self.buf, {
            return eof!(self.pos, "a computation M-1 or M-D");
          });
          self.pos.inc(c3);
          match c3 {
            b'1' => comp!(MMinus1),
            b'D' => comp!(MMinusD),
            c => unexpected!(self.pos, c, "a computation M-1 or M-D"),
          }
        }
        b'=' => dest!(M),
        b';' => {
          self.la = Some(b';');
          comp!(M)
        }
        c if c.is_ascii_whitespace() => comp!(M),
        c => unexpected!(self.pos, c, "a destination M= or a computation M"),
      }
    } else if c1 == b'D' {
      self.tpos = self.pos;
      let c2 = next!(self.buf, { return comp!(D) });
      self.pos.inc(c2);
      match c2 {
        b'+' => {
          let c3 = next!(self.buf, {
            return eof!(self.pos, "a computation D+1|D+A|D+M");
          });
          self.pos.inc(c3);
          match c3 {
            b'1' => comp!(DPlus1),
            b'A' => comp!(DPlusA),
            b'M' => comp!(DPlusM),
            c => unexpected!(self.pos, c, "a computation D+1|D+A|D+M"),
          }
        }
        b'-' => {
          let c3 = next!(self.buf, {
            return eof!(self.pos, "a computation D-1|D-A|D-M");
          });
          self.pos.inc(c3);
          match c3 {
            b'1' => comp!(DMinus1),
            b'A' => comp!(DMinusA),
            b'M' => comp!(DMinusM),
            c => unexpected!(self.pos, c, "a computation D-1|D-A|D-M"),
          }
        }
        b'&' => {
          let c3 = next!(self.buf, {
            return eof!(self.pos, "a computation D&A or D&M");
          });
          self.pos.inc(c3);
          match c3 {
            b'A' => comp!(DAndA),
            b'M' => comp!(DAndM),
            c => unexpected!(self.pos, c, "a computation D&A or D&M"),
          }
        }
        b'|' => {
          let c3 = next!(self.buf, {
            return eof!(self.pos, "a computation D|A or D|M");
          });
          self.pos.inc(c3);
          match c3 {
            b'A' => comp!(DOrA),
            b'M' => comp!(DOrM),
            c => unexpected!(self.pos, c, "a computation D|A or D|M"),
          }
        }
        b'=' => dest!(D),
        b';' => {
          self.la = Some(b';');
          comp!(D)
        }
        c if c.is_ascii_whitespace() => comp!(D),
        c => unexpected!(self.pos, c, "a destination D= or a computation D"),
      }
    } else if c1 == b'-' {
      self.tpos = self.pos;
      let c2 = next!(self.buf, {
        return eof!(self.pos, "a computation -A|-M|-D");
      });
      self.pos.inc(c2);
      match c2 {
        b'1' => comp!(Neg1),
        b'A' => comp!(NegA),
        b'M' => comp!(NegM),
        b'D' => comp!(NegD),
        c => unexpected!(self.pos, c, "a computation -A|-M|-D"),
      }
    } else if c1 == b'!' {
      self.tpos = self.pos;
      let c2 = next!(self.buf, {
        return eof!(self.pos, "a computation !A|!M|!D");
      });
      self.pos.inc(c2);
      match c2 {
        b'A' => comp!(NotA),
        b'M' => comp!(NotM),
        b'D' => comp!(NotD),
        c => unexpected!(self.pos, c, "a computation !A|!M|!D"),
      }
    } else if c1 == b'0' {
      self.tpos = self.pos;
      Some(Ok(Tok::Comp(Comp::Zero)))
    } else if c1 == b'1' {
      self.tpos = self.pos;
      Some(Ok(Tok::Comp(Comp::One)))
    } else if c1 == b';' {
      self.tpos = self.pos;
      Some(Ok(Tok::Semi))
    } else {
      unexpected!(self.pos, c1, "an address or an instruction")
    }
  }
}

#[cfg(test)]
mod tests {
  use crate::loc::Loc;

  use super::Comp;
  use super::Dest;
  use super::Jump;
  use super::Lex;
  use super::Tok;
  use super::Txt;

  macro_rules! lex {
    ($f:expr) => {
      Lex::from(&include_bytes!(concat!("../tests/data/", $f))[..])
    };
  }

  macro_rules! assert_next {
    ($lex:expr, $tbuf:expr, $e:expr) => {
      assert_eq!($lex.next(), Some(Ok($e)))
    };
  }

  #[test]
  fn empty() {
    let mut lex = lex!("empty");
    assert_eq!(lex.pos, Loc::new(1, 0));
    assert_eq!(lex.next(), None);
    assert_eq!(lex.pos, Loc::new(1, 0));
  }

  #[test]
  fn spaces() {
    let mut lex = lex!("spaces");
    assert_eq!(lex.next(), None);
    assert_eq!(lex.pos, Loc::new(5, 0));
  }

  #[test]
  fn comments() {
    let mut lex = lex!("comments");
    assert_eq!(lex.next(), None);
    assert_eq!(lex.pos, Loc::new(5, 0));
  }

  #[test]
  fn num_address() {
    let mut lex = lex!("num_address");
    assert_next!(lex, tbuf, Tok::NumAddr(8192));
    assert_eq!(lex.token_pos(), Loc::new(3, 5));
    assert_next!(lex, tbuf, Tok::NumAddr(123));
    assert_eq!(lex.token_pos(), Loc::new(5, 1));
    assert_next!(lex, tbuf, Tok::NumAddr(556));
    assert_eq!(lex.token_pos(), Loc::new(9, 5));
    assert_eq!(lex.next(), None);
  }

  #[test]
  fn name_address() {
    let mut lex = lex!("name_address");
    assert_next!(lex, tbuf, Tok::NameAddr);
    assert_eq!(lex.token_pos(), Loc::new(3, 5));
    assert_eq!(lex.text(), &Txt::from(&b"FOO"[..]));
    assert_next!(lex, tbuf, Tok::NameAddr);
    assert_eq!(lex.token_pos(), Loc::new(5, 1));
    assert_eq!(lex.text(), &Txt::from(&b"BAR"[..]));
    assert_next!(lex, tbuf, Tok::NameAddr);
    assert_eq!(lex.token_pos(), Loc::new(9, 5));
    assert_eq!(lex.text(), &Txt::from(&b"R2"[..]));
    assert_eq!(lex.next(), None);
  }

  #[test]
  fn labels() {
    let mut lex = lex!("labels");
    assert_next!(lex, tbuf, Tok::NameAddr);
    assert_eq!(lex.token_pos(), Loc::new(3, 5));
    assert_eq!(lex.text(), &Txt::from(&b"FOO"[..]));
    assert_next!(lex, tbuf, Tok::Label);
    assert_eq!(lex.token_pos(), Loc::new(5, 1));
    assert_eq!(lex.text(), &Txt::from(&b"LABEL"[..]));
    assert_next!(lex, tbuf, Tok::NameAddr);
    assert_eq!(lex.token_pos(), Loc::new(9, 5));
    assert_eq!(lex.text(), &Txt::from(&b"LABEL"[..]));
    assert_next!(lex, tbuf, Tok::NameAddr);
    assert_eq!(lex.token_pos(), Loc::new(11, 1));
    assert_eq!(lex.text(), &Txt::from(&b"BAR"[..]));
    assert_next!(lex, tbuf, Tok::Label);
    assert_eq!(lex.token_pos(), Loc::new(13, 1));
    assert_eq!(lex.text(), &Txt::from(&b"BAR"[..]));
    assert_next!(lex, tbuf, Tok::NameAddr);
    assert_eq!(lex.token_pos(), Loc::new(15, 1));
    assert_eq!(lex.text(), &Txt::from(&b"LAB0"[..]));
    assert_next!(lex, tbuf, Tok::Label);
    assert_eq!(lex.token_pos(), Loc::new(17, 1));
    assert_eq!(lex.text(), &Txt::from(&b"LAB0"[..]));
    assert_eq!(lex.next(), None);
  }

  #[test]
  fn assignments() {
    let mut lex = lex!("assignments");
    assert_next!(lex, tbuf, Tok::Dest(Dest::A));
    assert_eq!(lex.token_pos(), Loc::new(1, 1));
    assert_next!(lex, tbuf, Tok::Comp(Comp::MMinus1));
    assert_eq!(lex.token_pos(), Loc::new(1, 3));
    assert_next!(lex, tbuf, Tok::Dest(Dest::AM));
    assert_eq!(lex.token_pos(), Loc::new(2, 1));
    assert_next!(lex, tbuf, Tok::Comp(Comp::DOrA));
    assert_eq!(lex.token_pos(), Loc::new(2, 4));
    assert_next!(lex, tbuf, Tok::Dest(Dest::AMD));
    assert_eq!(lex.token_pos(), Loc::new(3, 1));
    assert_next!(lex, tbuf, Tok::Comp(Comp::APlus1));
    assert_eq!(lex.token_pos(), Loc::new(3, 5));
    assert_eq!(lex.next(), None);
  }

  #[test]
  fn branches() {
    let mut lex = lex!("branches");
    assert_next!(lex, tbuf, Tok::Comp(Comp::MMinus1));
    assert_eq!(lex.token_pos(), Loc::new(1, 1));
    assert_next!(lex, tbuf, Tok::Semi);
    assert_eq!(lex.token_pos(), Loc::new(1, 4));
    assert_next!(lex, tbuf, Tok::Jump(Jump::JEQ));
    assert_eq!(lex.token_pos(), Loc::new(1, 5));
    assert_next!(lex, tbuf, Tok::Comp(Comp::DOrA));
    assert_eq!(lex.token_pos(), Loc::new(2, 1));
    assert_next!(lex, tbuf, Tok::Semi);
    assert_eq!(lex.token_pos(), Loc::new(2, 4));
    assert_next!(lex, tbuf, Tok::Jump(Jump::JNE));
    assert_eq!(lex.token_pos(), Loc::new(2, 5));
    assert_next!(lex, tbuf, Tok::Comp(Comp::APlus1));
    assert_eq!(lex.token_pos(), Loc::new(3, 1));
    assert_next!(lex, tbuf, Tok::Semi);
    assert_eq!(lex.token_pos(), Loc::new(3, 4));
    assert_next!(lex, tbuf, Tok::Jump(Jump::JMP));
    assert_eq!(lex.token_pos(), Loc::new(3, 5));
    assert_eq!(lex.next(), None);
  }

  #[test]
  fn instructions() {
    let mut lex = lex!("instructions");
    assert_next!(lex, tbuf, Tok::Dest(Dest::A));
    assert_eq!(lex.token_pos(), Loc::new(1, 1));
    assert_next!(lex, tbuf, Tok::Comp(Comp::MMinus1));
    assert_eq!(lex.token_pos(), Loc::new(1, 3));
    assert_next!(lex, tbuf, Tok::Semi);
    assert_eq!(lex.token_pos(), Loc::new(1, 6));
    assert_next!(lex, tbuf, Tok::Jump(Jump::JEQ));
    assert_eq!(lex.token_pos(), Loc::new(1, 7));
    assert_next!(lex, tbuf, Tok::Dest(Dest::AM));
    assert_eq!(lex.token_pos(), Loc::new(2, 1));
    assert_next!(lex, tbuf, Tok::Comp(Comp::DOrA));
    assert_eq!(lex.token_pos(), Loc::new(2, 4));
    assert_next!(lex, tbuf, Tok::Semi);
    assert_eq!(lex.token_pos(), Loc::new(2, 7));
    assert_next!(lex, tbuf, Tok::Jump(Jump::JNE));
    assert_eq!(lex.token_pos(), Loc::new(2, 8));
    assert_next!(lex, tbuf, Tok::Dest(Dest::AMD));
    assert_eq!(lex.token_pos(), Loc::new(3, 1));
    assert_next!(lex, tbuf, Tok::Comp(Comp::APlus1));
    assert_eq!(lex.token_pos(), Loc::new(3, 5));
    assert_next!(lex, tbuf, Tok::Semi);
    assert_eq!(lex.token_pos(), Loc::new(3, 8));
    assert_next!(lex, tbuf, Tok::Jump(Jump::JMP));
    assert_eq!(lex.token_pos(), Loc::new(3, 9));
    assert_eq!(lex.next(), None);
  }
}
