#![warn(clippy::all)]

use smallvec::SmallVec;

pub type Text = SmallVec<[u8; 16]>;

pub fn text_str(text: &Text) -> String {
  unsafe { String::from_utf8_unchecked(text.to_vec()) }
}
