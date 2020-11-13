#![warn(clippy::all)]

use std::collections::HashMap as Map;

use crate::lex::Comp;
use crate::lex::Dest;
use crate::lex::Jump;
use crate::lex::Txt;
use crate::parse::Stmt;
use crate::parse::SymInfo;

pub struct Gen {
  addr: u16,
}

impl Default for Gen {
  fn default() -> Self {
    Self { addr: 16 }
  }
}

impl Gen {
  fn encode_dest(dest: Dest) -> u16 {
    match dest {
      Dest::M => 1,
      Dest::D => 2,
      Dest::MD => 3,
      Dest::A => 4,
      Dest::AM => 5,
      Dest::AD => 6,
      Dest::AMD => 7,
    }
  }

  fn encode_comp(comp: Comp) -> u16 {
    match comp {
      Comp::Zero => 0b0101010,
      Comp::One => 0b0111111,
      Comp::Neg1 => 0b0111010,
      Comp::D => 0b0001100,
      Comp::A => 0b0110000,
      Comp::NotD => 0b0001101,
      Comp::NotA => 0b0110001,
      Comp::NegD => 0b0001111,
      Comp::NegA => 0b0110011,
      Comp::DPlus1 => 0b0011111,
      Comp::APlus1 => 0b0110111,
      Comp::DMinus1 => 0b0001110,
      Comp::AMinus1 => 0b0110010,
      Comp::DPlusA => 0b0000010,
      Comp::DMinusA => 0b0010011,
      Comp::AMinusD => 0b0000111,
      Comp::DAndA => 0b0000000,
      Comp::DOrA => 0b0010101,
      Comp::M => 0b1110000,
      Comp::NotM => 0b1110001,
      Comp::NegM => 0b1110011,
      Comp::MPlus1 => 0b1110111,
      Comp::MMinus1 => 0b1110010,
      Comp::DPlusM => 0b1000010,
      Comp::DMinusM => 0b1010011,
      Comp::MMinusD => 0b1000111,
      Comp::DAndM => 0b1000000,
      Comp::DOrM => 0b1010101,
    }
  }

  fn encode_jump(jump: Jump) -> u16 {
    match jump {
      Jump::JGT => 1,
      Jump::JEQ => 2,
      Jump::JGE => 3,
      Jump::JLT => 4,
      Jump::JNE => 5,
      Jump::JLE => 6,
      Jump::JMP => 7,
    }
  }

  pub fn encode(&mut self, stmt: &Stmt, st: &mut Map<Txt, SymInfo>) -> u16 {
    match stmt {
      Stmt::Addr(addr) => *addr,
      Stmt::UnresolvedAddr(pos, name) => {
        st.entry(name.clone())
          .or_insert_with(|| {
            let info = SymInfo::new(*pos, self.addr);
            self.addr += 1;
            info
          })
          .addr
      }
      Stmt::Assign(_, dest, comp) => {
        (0b111 << 13) | (Gen::encode_comp(*comp) << 6) | (Gen::encode_dest(*dest) << 3)
      }
      Stmt::Branch(_, comp, jump) => {
        (0b111 << 13) | (Gen::encode_comp(*comp) << 6) | Gen::encode_jump(*jump)
      }
      Stmt::Inst(_, dest, comp, jump) => {
        (0b111 << 13)
          | (Gen::encode_comp(*comp) << 6)
          | (Gen::encode_dest(*dest) << 3)
          | Gen::encode_jump(*jump)
      }
    }
  }

  pub fn text_encode(val: u16) -> [u8; 16] {
    const VALS: [u8; 2] = [b'0', b'1'];
    [
      VALS[(val >> 15 & 1) as usize],
      VALS[(val >> 14 & 1) as usize],
      VALS[(val >> 13 & 1) as usize],
      VALS[(val >> 12 & 1) as usize],
      VALS[(val >> 11 & 1) as usize],
      VALS[(val >> 10 & 1) as usize],
      VALS[(val >> 9 & 1) as usize],
      VALS[(val >> 8 & 1) as usize],
      VALS[(val >> 7 & 1) as usize],
      VALS[(val >> 6 & 1) as usize],
      VALS[(val >> 5 & 1) as usize],
      VALS[(val >> 4 & 1) as usize],
      VALS[(val >> 3 & 1) as usize],
      VALS[(val >> 2 & 1) as usize],
      VALS[(val >> 1 & 1) as usize],
      VALS[(val & 1) as usize],
    ]
  }
}
