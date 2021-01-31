//! Structures for dealing with HACK assembly programs.
//!
//! [Prog] can be used to represent the (flat) parse tree of a HACK
//! assembly program.

use crate::com::addr;
use crate::com::addr::Addr;
use crate::com::inst;
use crate::com::inst::Inst;
use crate::dis::parser;
use crate::dis::parser::Parser;
use crate::dis::parser::Token;
use crate::utils::buf::Buf;
use crate::utils::loc::Loc;

use std::convert::TryFrom;

use derive_more::Display;

/// A HACK assembly program.
///
/// Contains the symbol table for declared labels and the list (flat
/// tree) of A- and C- instructions in the program.
pub struct Prog<'b> {
  /// The original input buffer.
  orig: Buf<'b>,

  /// The list of instructions in the program.
  instructions: Vec<parser::Token>,
}

/// Possible errors returned from loading a HACK assembly program.
#[derive(Display, Debug, Clone, PartialEq, Eq)]
#[display(fmt = "Disassembler error: {}")]
pub enum Err {
  /// Parse errors.
  #[display(fmt = "Parser error: {}", _0)]
  Parser(parser::Err),
}

/// Shorthand for items returned by the (parser)(Parser)
/// (iterator)[Iterator].
type ParserResult = Result<parser::Token, parser::Err>;

impl<'b> Prog<'b> {
  /// Create a program from a disassembler parser.
  fn new_parser(
    buf: Buf<'b>,
    parser: &mut dyn Iterator<Item = ParserResult>,
  ) -> Result<Self, Err> {
    let insts = parser.collect::<Result<_, _>>().map_err(Err::Parser)?;
    Ok(Self { orig: buf, instructions: insts })
  }

  /// Create a program that will decode a binary input buffer.
  pub fn new(buf: Buf<'b>) -> Result<Self, Err> {
    let mut parser: Parser<parser::BinDecoder> = Parser::from(buf);
    Prog::new_parser(buf, &mut parser)
  }

  /// Create a program that will decode a bintext input buffer.
  pub fn new_text(buf: Buf<'b>) -> Result<Self, Err> {
    let mut parser: Parser<parser::TxtDecoder> = Parser::from(buf);
    Prog::new_parser(buf, &mut parser)
  }

  /// Return the original input buffer associated with this program.
  pub fn orig(&self) -> Buf {
    self.orig
  }
}

/// Errors when decoding programs from their compiled form.
#[derive(Display, Debug, Clone, PartialEq, Eq)]
#[display(fmt = "Disassembler decoding error: {}")]
pub enum DecodeErr {
  /// Invalid instruction.
  #[display(fmt = "Invalid instruction at {}: {}", _0, _1)]
  InvalidInst(Loc, inst::DecodeErr),

  /// Invalid address.
  #[display(fmt = "Invalid address instruction {}: {}", _0, _1)]
  InvalidAddr(Loc, addr::Err),
}

impl DecodeErr {
  /// Create a `DecodeErr::InvalidInst` variant.
  pub fn invalid_inst(dec: &Decoder, tok: &Token, err: inst::DecodeErr) -> Self {
    Self::InvalidInst(Loc::from_index(dec.prog.orig(), tok.index()), err)
  }

  /// Create a `DecodeErr::InvalidAddr` variant.
  pub fn invalid_addr(dec: &Decoder, tok: &Token, err: addr::Err) -> Self {
    Self::InvalidAddr(Loc::from_index(dec.prog.orig(), tok.index()), err)
  }
}

/// HACK program decoder used for disassembly.
pub struct Decoder<'b, 'p> {
  /// The program object to decode from.
  prog: &'p mut Prog<'b>,

  /// The index of the currently decoded instruction.
  index: usize,
}

impl Iterator for Decoder<'_, '_> {
  type Item = Result<String, DecodeErr>;

  fn next(&mut self) -> Option<Self::Item> {
    let token = self.prog.instructions.get(self.index)?;
    let inst = token.value();
    self.index += 1;

    if inst & 0b1000_0000_0000_0000 == 0 {
      // A-instruction
      let inst = inst & 0b0111_1111_1111_1111;
      let decoded = match Addr::try_from(inst) {
        Ok(decoded) => decoded,
        Err(e) => return Some(Err(DecodeErr::invalid_addr(self, token, e))),
      };

      Some(Ok(format!("{}", decoded)))
    } else {
      // C-instruction
      let inst = inst & 0b0001_1111_1111_1111;
      let decoded = match Inst::try_from(inst) {
        Ok(decoded) => decoded,
        Err(e) => return Some(Err(DecodeErr::invalid_inst(self, token, e))),
      };

      Some(Ok(format!("{}", decoded)))
    }
  }
}

impl<'b> Prog<'b> {
  /// Return the program's decoder.
  pub fn decoder(&mut self) -> Decoder<'_, 'b> {
    Decoder { prog: self, index: 0 }
  }
}
