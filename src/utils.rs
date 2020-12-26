//! Helpers for parsing byte buffers.

/// Alias for [u8].
pub type Byte = u8;

/// Alias for byte slices.
pub type Buf<'b> = &'b [Byte];

/// Splits a buffer `buf` at the point when `pred` returns false for a
/// byte.
///
/// Returns the parsed part of the buffer and the remainder.
///
/// # Arguments
///
/// * `buf` - The input buffer.
///
/// * `pred` - A predicate that should return `true` as long as
/// `read_while` should continue to consume input.
pub fn read_while<P>(buf: Buf, pred: P) -> (Buf, Buf)
where
  P: Fn(Byte) -> bool,
{
  let split = buf
    .iter()
    .enumerate()
    .find_map(|(i, &c)| if pred(c) { None } else { Some(i) })
    .unwrap_or_else(|| buf.len());

  (&buf[..split], &buf[split..])
}

/// Removes a byte (the head) of `buf` if it passes the predicate
/// `pred`.
///
/// Returns the consumed byte and the remainder of the buffer.
///
/// # Arguments
///
/// * `buf` - The input buffer.
///
/// * `pred` - A predicate that should return `true` if `read_char`
/// should consume the byte.
pub fn read_one<P>(buf: Buf, pred: P) -> Option<(Byte, Buf)>
where
  P: Fn(Byte) -> bool,
{
  if let Some(&b) = buf.get(0) {
    if pred(b) {
      Some((b, &buf[1..]))
    } else {
      None
    }
  } else {
    None
  }
}
