#![warn(clippy::all)]

use std::collections::HashMap as Map;

pub struct ST {
  idx: u16,
  map: Map<Vec<u8>, u16>,
}

impl Default for ST {
  fn default() -> Self {
    Self {
      idx: 16,
      map: Map::new(),
    }
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
    assert_eq!(st.get(b"FOO"), Some(16));
    assert_eq!(st.get(b"FOO"), Some(16));
    assert_eq!(st.get(b"BAR"), Some(17));
    assert_eq!(st.get(b"FOO"), Some(16));
    assert_eq!(st.get(b"FOO"), Some(16));
    assert_eq!(st.get(b"BAR"), Some(17));
    assert_eq!(st.get(b"BAZ"), Some(18));
    assert_eq!(st.get(b"FOO"), Some(16));
    assert_eq!(st.get(b"BAR"), Some(17));
  }
}
