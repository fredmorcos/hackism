//! Structures for dealing with HACK assembly programs.
//!
//! [Prog] can be used to represent the (flat) parse tree of a HACK
//! assembly program.

use crate::hack::dec;
use crate::hack::dec::Parser;
use crate::Buf;
use derive_more::Display;

/// A HACK assembly program.
///
/// Contains the symbol table for declared labels and the list (flat
/// tree) of A- and C- instructions in the program.
pub struct Prog<'b> {
  /// The original input buffer.
  orig: Buf<'b>,

  /// The list of instructions in the program.
  insts: Vec<dec::Token>,
}

/// Possible errors returned from loading a HACK assembly program.
#[derive(Display, Debug, Clone, PartialEq, Eq)]
#[display(fmt = "Disassembler error: {}")]
pub enum Err {
  /// Parse errors.
  #[display(fmt = "Parser error: {}", _0)]
  Parser(dec::Err),
}

impl<'b> Prog<'b> {
  /// Get the list of instructions in the program.
  pub fn insts(&self) -> &[dec::Token] {
    &self.insts
  }

  /// Create a program from a disassembler parser.
  fn new_parser(
    buf: Buf<'b>,
    parser: &mut dyn Iterator<Item = dec::Res>,
  ) -> Result<Self, Err> {
    let insts = parser.collect::<Result<_, _>>().map_err(Err::Parser)?;
    Ok(Self { orig: buf, insts })
  }

  /// Create a program that will decode a binary input buffer.
  pub fn new(buf: Buf<'b>) -> Result<Self, Err> {
    let mut parser: Parser<dec::BinParser> = Parser::from(buf);
    Prog::new_parser(buf, &mut parser)
  }

  /// Create a program that will decode a bintext input buffer.
  pub fn new_text(buf: Buf<'b>) -> Result<Self, Err> {
    let mut parser: Parser<dec::BinTextParser> = Parser::from(buf);
    Prog::new_parser(buf, &mut parser)
  }

  /// Return the original input buffer associated with this program.
  pub fn orig(&self) -> Buf {
    self.orig
  }

  /// Return the program's decoder.
  pub fn decoder(&mut self) -> dec::Decoder<'_, 'b> {
    dec::Decoder::new(self)
  }
}
