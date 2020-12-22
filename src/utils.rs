use std::str::FromStr;

/// Reads an object of type `T` from an input buffer.
///
/// Returns a parsed object of type `T`, the remainder of the input
/// buffer and the number of characters that have been consumed during
/// the parse.
///
/// Once an unrecognized character has been reached, `read_from` will
/// create the object using its `FromStr` implementation. `Err(E)` is
/// returned if that fails.
///
/// # Arguments
///
/// * `buf` - The input buffer.
///
/// * `p` - The alphabet predicate. Must return true if the input
///         character is part of the alphabet.
pub fn read_from<T, E, F>(buf: &str, p: F) -> Result<(T, &str, usize), E>
where
  T: FromStr<Err = E>,
  F: Fn(char) -> bool,
{
  let split = buf
    .char_indices()
    .find_map(|(i, c)| if p(c) { None } else { Some(i) })
    .unwrap_or_else(|| buf.len());

  let dest = T::from_str(&buf[..split]).map_err(|e| e)?;
  Ok((dest, &buf[split..], split))
}
