pub type Byte = u8;
pub type Buf<'b> = &'b [Byte];

/// Splits a buffer `b` at the point when `p` returns false for a
/// byte.
///
/// Returns the parsed part of the buffer and the remainder.
///
/// # Arguments
///
/// * `b` - The input buffer.
///
/// * `p` - A predicate that should return true as long as
///         `read_while` should continue to consume input.
pub fn read_while<P>(b: Buf, p: P) -> (Buf, Buf)
where
  P: Fn(Byte) -> bool,
{
  let split = b
    .iter()
    .enumerate()
    .find_map(|(i, &c)| if p(c) { None } else { Some(i) })
    .unwrap_or_else(|| b.len());

  (&b[..split], &b[split..])
}
