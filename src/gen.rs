use std::collections::HashMap as Map;

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
  pub fn encode(&mut self, stmt: Stmt, st: &mut Map<Vec<u8>, SymInfo>) -> u16 {
    match stmt {
      Stmt::Addr(_, addr) => addr,
      Stmt::UnresolvedAddr(pos, name) => {
        st.entry(name)
          .or_insert_with(|| {
            let info = SymInfo::new(pos, self.addr);
            self.addr += 1;
            info
          })
          .addr
      }
    }
  }
}
