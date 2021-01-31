#![warn(clippy::all)]

//! **HAS** stands for the **H**ACK **A**pplication **S**uite. It
//! consists of a library and binaries to handle the HACK machine
//! language and the JACK programming language. Currently this crate
//! only contains a HACK assembler and few library utilities. The HACK
//! assembler translates HACK assembly code to HACK machine code.

#[macro_use]
extern crate derive_new;

pub mod asm;
pub mod com;
pub mod dis;
pub mod utils;
