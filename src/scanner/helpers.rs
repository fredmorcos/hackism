#[macro_export]
macro_rules! eof {
  ($expecting:expr) => {
    Some(Err(Error::new_eof(source_location!(), $expecting)))
  };
}

#[macro_export]
macro_rules! unexpected_token {
  ($byte:expr, $expecting:expr) => {
    Some(Err(Error::new_unexpected(
      source_location!(),
      $byte,
      $expecting,
    )))
  };
}

#[macro_export]
macro_rules! address_range {
  ($expecting:expr) => {
    Some(Err(Error::new_range($expecting)))
  };
}
