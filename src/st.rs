#![warn(clippy::all)]

use std::collections::HashMap as Map;

#[derive(Debug)]
pub struct ST {
  idx: u16,
  map: Map<Vec<u8>, u16>,
}

impl Default for ST {
  fn default() -> Self {
    let mut map = Map::new();
    map.insert(Vec::from(&b"SP"[..]), 0);
    map.insert(Vec::from(&b"LCL"[..]), 1);
    map.insert(Vec::from(&b"ARG"[..]), 2);
    map.insert(Vec::from(&b"THIS"[..]), 3);
    map.insert(Vec::from(&b"THAT"[..]), 4);
    map.insert(Vec::from(&b"R0"[..]), 0);
    map.insert(Vec::from(&b"R1"[..]), 1);
    map.insert(Vec::from(&b"R2"[..]), 2);
    map.insert(Vec::from(&b"R3"[..]), 3);
    map.insert(Vec::from(&b"R4"[..]), 4);
    map.insert(Vec::from(&b"R5"[..]), 5);
    map.insert(Vec::from(&b"R6"[..]), 6);
    map.insert(Vec::from(&b"R7"[..]), 7);
    map.insert(Vec::from(&b"R8"[..]), 8);
    map.insert(Vec::from(&b"R9"[..]), 9);
    map.insert(Vec::from(&b"R10"[..]), 10);
    map.insert(Vec::from(&b"R11"[..]), 11);
    map.insert(Vec::from(&b"R12"[..]), 12);
    map.insert(Vec::from(&b"R13"[..]), 13);
    map.insert(Vec::from(&b"R14"[..]), 14);
    map.insert(Vec::from(&b"R15"[..]), 15);
    map.insert(Vec::from(&b"SCREEN"[..]), 16384);
    map.insert(Vec::from(&b"KBD"[..]), 24576);
    Self { idx: 16, map }
  }
}

impl ST {
  pub fn get(&mut self, name: &[u8]) -> Option<u16> {
    self.map.get(name).copied().or_else(|| {
      // 32767 (15 bits of address value)
      if self.idx == 32767 {
        None
      } else {
        self.map.insert(name.into(), self.idx);
        self.idx += 1;
        Some(self.idx - 1)
      }
    })
  }
}

#[cfg(test)]
mod tests {
  use super::ST;

  #[test]
  fn seq() {
    let mut st = ST::default();
    assert_eq!(st.get(b"R5"), Some(5));
    assert_eq!(st.get(b"FOO"), Some(16));
    assert_eq!(st.get(b"FOO"), Some(16));
    assert_eq!(st.get(b"BAR"), Some(17));
    assert_eq!(st.get(b"FOO"), Some(16));
    assert_eq!(st.get(b"FOO"), Some(16));
    assert_eq!(st.get(b"BAR"), Some(17));
    assert_eq!(st.get(b"BAZ"), Some(18));
    assert_eq!(st.get(b"FOO"), Some(16));
    assert_eq!(st.get(b"BAR"), Some(17));
    assert_eq!(st.get(b"ARG"), Some(2));
  }
}
