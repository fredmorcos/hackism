#![warn(clippy::all)]

use crate::pos::Pos;

#[derive(Debug, PartialEq, Eq)]
pub enum Inst {
  Addr(Pos, u16),
}

impl Inst {
  pub fn encode(&self) -> u16 {
    match self {
      Inst::Addr(_, val) => *val,
    }
  }
}

#[cfg(test)]
mod tests {
  use crate::pos::Pos;

  use super::Inst;

  #[test]
  fn num_address() {
    assert_eq!(Inst::Addr(Pos::new(0, 0), 8192).encode(), 8192);
    assert_eq!(Inst::Addr(Pos::new(0, 0), 123).encode(), 123);
    assert_eq!(Inst::Addr(Pos::new(0, 0), 556).encode(), 556);
  }

  #[test]
  fn name_address() {
    assert_eq!(Inst::Addr(Pos::new(0, 0), 16).encode(), 16);
    assert_eq!(Inst::Addr(Pos::new(0, 0), 17).encode(), 17);
    assert_eq!(Inst::Addr(Pos::new(0, 0), 2).encode(), 2);
  }
}
