fn is_symbol(byte: u8) -> bool {
  byte == b'_' || byte == b'.' || byte == b'$' || byte == b':'
}

pub(crate) fn is_label_start(byte: u8) -> bool {
  byte.is_ascii_alphabetic() || is_symbol(byte)
}

pub(crate) fn is_label_byte(byte: u8) -> bool {
  byte.is_ascii_alphanumeric() || is_symbol(byte)
}
