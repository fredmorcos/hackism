#![warn(clippy::all)]
#![warn(missing_docs)]
// #![warn(missing_doc_code_examples)]

//! **HAS** stands for the **H**ACK **A**pplication **S**uite. It
//! consists of a library and binaries to handle the HACK machine
//! language and the JACK programming language. Currently this crate
//! only contains a HACK assembler and few library utilities. The HACK
//! assembler translates HACK assembly code to HACK machine code.

#[macro_use]
extern crate derive_new;

pub mod dis;
pub mod hack;
pub mod utils;

pub use hack::Prog as HackProg;
pub use hack::ProgErr as HackProgErr;
pub use utils::buf::Buf;
pub use utils::buf::Byte;
pub use utils::conv;
pub use utils::loc::Index;
pub use utils::loc::Loc;
pub use utils::parser;
