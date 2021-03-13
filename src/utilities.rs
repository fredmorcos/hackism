//! Submodules for common structures and routines.
//!
//! Contains helpers and utilities for dealing with buffers,
//! locations, spans and perhaps other things relevant to parsing as
//! well as machine and programming languages.

mod testing;

pub mod location;
pub mod span;

pub use location::Location;
pub use span::Span;
