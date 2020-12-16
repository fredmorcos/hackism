//! Structures related to locations in source code.
//!
//! This module offers [SrcLoc] for locations in HAS's sources and
//! [Loc] for locations in input programs. The macros [srcloc!] and
//! [loc!] can respectively be used as shorthands to create these
//! structures.

use std::fmt;

/// Denotes locations in the HAS crates sources (e.g. to track where
/// in the HAS sources error objects were created).
///
/// # impl `Display` examples
///
/// ```
/// use has::loc::SrcLoc;
///
/// let src_loc = SrcLoc::new("foo.asm", 30);
/// assert_eq!(format!("{}", src_loc), "file foo.asm, line 30");
/// ```
#[doc(alias = "sourcelocation")]
#[doc(alias = "sourceloc")]
#[doc(alias = "srclocation")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SrcLoc {
  file: &'static str,
  line: u32,
}

impl fmt::Display for SrcLoc {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "file {}, line {}", self.file, self.line)
  }
}

impl SrcLoc {
  /// Creates a new [SrcLoc] object. You probably want to use the
  /// provided [srcloc!()] macro instead.
  ///
  /// # Arguments
  ///
  /// * `file` - Filename which would typically be created by a call
  /// to [core::file!()].
  ///
  /// * `line` - Line in `file` which Would typically be created by a
  /// call to [core::line!()].
  ///
  /// # Examples
  ///
  /// ```
  /// use has::loc::SrcLoc;
  ///
  /// let src_loc = SrcLoc::new("foo.asm", 26);
  /// ```
  pub fn new(file: &'static str, line: u32) -> Self {
    Self { file, line }
  }

  /// Returns the filename of a [SrcLoc] object.
  pub fn file(&self) -> &'static str {
    self.file
  }

  /// Returns the line of a [SrcLoc] object.
  pub fn line(&self) -> u32 {
    self.line
  }
}

/// Shorthand to create a [SrcLoc] object that denotes the current
/// call-site's location.
///
/// # Examples
///
/// ```
/// use has::loc::SrcLoc;
/// use has::srcloc;
///
/// let src_loc = srcloc!();
/// assert_ne!(src_loc, srcloc!());
/// assert_eq!(srcloc!(), SrcLoc::new(file!(), line!()));
/// ```
#[doc(alias = "source location")]
#[doc(alias = "source location macro")]
#[doc(alias = "source loc macro")]
#[doc(alias = "source loc")]
#[doc(alias = "src loc")]
#[doc(alias = "src loc macro")]
#[doc(alias = "srcloc macro")]
#[macro_export]
macro_rules! srcloc {
  () => {
    SrcLoc::new(file!(), line!())
  };
}
