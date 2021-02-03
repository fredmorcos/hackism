//! Helpers for parsing byte buffers.

use crate::Buf;
use crate::Byte;

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

/// Consume whitespace from `buf`.
///
/// Returns the number of consumed whitespace bytes and the remainder
/// of the buffer.
///
/// # Arguments
///
/// * `buf` - The input buffer.
pub fn read_ws(buf: Buf) -> (usize, Buf) {
  let (ws, rem) = read_while(buf, |b| b.is_ascii_whitespace());
  (ws.len(), rem)
}

/// Consume input until a newline.
///
/// Returns the consumed part of the input and the remainder of the
/// buffer.
///
/// * `buf` - The input buffer.
pub fn read_until_nl(buf: Buf) -> (Buf, Buf) {
  read_while(buf, |b| b != b'\n')
}

/// Consume input until whitespace.
///
/// Returns the consumed part of the input and the remainder of the
/// buffer.
///
/// * `buf` - The input buffer.
pub fn read_until_ws(buf: Buf) -> (Buf, Buf) {
  read_while(buf, |b| !b.is_ascii_whitespace())
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

/// Removes a byte (the head) of `buf` if it's a digit.
///
/// Returns the consumed byte and the remainder of the buffer.
///
/// # Arguments
///
/// * `buf` - The input buffer.
pub fn read_digit(buf: Buf) -> Option<(Byte, Buf)> {
  read_one(buf, |b| b.is_ascii_digit())
}
