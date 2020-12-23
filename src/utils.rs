/// Splits a string `s` at the point when `p` returns false for a character.
///
/// Returns the parsed string and the remainder.
///
/// # Arguments
///
/// * `s` - The input string.
///
/// * `p` - A predicate that should return true as long as
///         `read_while` should continue to consume input.
pub fn read_while<P>(s: &str, p: P) -> (&str, &str)
where
  P: Fn(char) -> bool,
{
  let split = s
    .char_indices()
    .find_map(|(i, c)| if p(c) { None } else { Some(i) })
    .unwrap_or_else(|| s.len());

  (&s[..split], &s[split..])
}
