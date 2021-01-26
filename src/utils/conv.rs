//! Helpers for converting (mostly integer) values.

/// Converts a [u16] value into 16 ASCII bytes representing the binary
/// representations of the value.
///
/// # Arguments
///
/// * `val` - The value to be converted.
pub fn u16_bintext(val: u16) -> [u8; 16] {
  const VALS: [u8; 2] = [b'0', b'1'];
  [
    VALS[(val >> 0xF & 1) as usize],
    VALS[(val >> 0xE & 1) as usize],
    VALS[(val >> 0xD & 1) as usize],
    VALS[(val >> 0xC & 1) as usize],
    VALS[(val >> 0xB & 1) as usize],
    VALS[(val >> 0xA & 1) as usize],
    VALS[(val >> 0x9 & 1) as usize],
    VALS[(val >> 0x8 & 1) as usize],
    VALS[(val >> 0x7 & 1) as usize],
    VALS[(val >> 0x6 & 1) as usize],
    VALS[(val >> 0x5 & 1) as usize],
    VALS[(val >> 0x4 & 1) as usize],
    VALS[(val >> 0x3 & 1) as usize],
    VALS[(val >> 0x2 & 1) as usize],
    VALS[(val >> 0x1 & 1) as usize],
    VALS[(val & 1) as usize],
  ]
}
