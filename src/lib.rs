#![warn(clippy::all)]
#![warn(missing_docs)]

//! The `hackism` library.
//!
//! This library provides common and helper utilities like parsers,
//! encoders and decoders for working with the HACK machine language
//! and the JACK programming language.

#[macro_use]
extern crate derive_new;

pub mod hack;
pub mod utilities;
