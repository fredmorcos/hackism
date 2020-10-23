use std::collections::HashMap as Map;

use crate::lex::Comp;
use crate::lex::Dest;
use crate::lex::Jump;
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
      Dest::Mem => 1,
      Dest::Data => 2,
      Dest::MemData => 3,
      Dest::Addr => 4,
      Dest::AddrMem => 5,
      Dest::AddrData => 6,
      Dest::AddrMemData => 7,
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
      Jump::Jgt => 1,
      Jump::Jeq => 2,
      Jump::Jge => 3,
      Jump::Jlt => 4,
      Jump::Jne => 5,
      Jump::Jle => 6,
      Jump::Jmp => 7,
    }
  }

  pub fn encode(&mut self, stmt: &Stmt, st: &mut Map<Vec<u8>, SymInfo>) -> u16 {
    match stmt {
      Stmt::Addr(_, addr) => *addr,
      Stmt::UnresolvedAddr(pos, name) => {
        st.entry(name.clone())
          .or_insert_with(|| {
            let info = SymInfo::new(*pos, self.addr);
            self.addr += 1;
            info
          })
          .addr
      }
      Stmt::Assign(_, dest, _, comp) => {
        (0b111 << 13) | (Gen::encode_comp(*comp) << 6) | (Gen::encode_dest(*dest) << 3)
      }
      Stmt::Branch(_, comp, _, jump) => {
        (0b111 << 13) | (Gen::encode_comp(*comp) << 6) | Gen::encode_jump(*jump)
      }
      Stmt::Inst(_, dest, _, comp, _, jump) => {
        (0b111 << 13)
          | (Gen::encode_comp(*comp) << 6)
          | (Gen::encode_dest(*dest) << 3)
          | Gen::encode_jump(*jump)
      }
    }
  }
}
