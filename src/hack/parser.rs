//! A parser for `HACK` assembly programs.

use super::Address;
use super::CommentToken;
use super::Instruction;
use super::LabelToken;
use super::Lexer;
use super::LexerError;
use super::NewlinesToken;
use super::Token;
use super::WhitespaceToken;
use derive_more::Display;
use derive_more::From;

/// Parser for `HACK` assembly programs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parser {
  /// Lexer attached to the parser.
  lexer: Lexer,
}

/// Create a new parser to parse a byte buffer.
impl From<Vec<u8>> for Parser {
  fn from(input: Vec<u8>) -> Self {
    Self { lexer: Lexer::from(input) }
  }
}

/// Create a new parser to parse a string's byte buffer.
impl From<String> for Parser {
  fn from(input: String) -> Self {
    Self::from(input.into_bytes())
  }
}

/// Errors returned by the `HACK` lexer.
#[derive(new, From, Display, Debug, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "HACK parsing error: {}")]
pub enum Error {
  /// Lexer errors.
  Lexer(LexerError),

  /// Unexpected token.
  Token(Token),
}

/// Nodes returned by the [Parser] as a parse tree.
#[derive(new, From, Debug, Display, Clone, Copy, PartialEq, Eq)]
pub enum Node {
  /// Spans of whitespace.
  #[display(fmt = "{}", _0)]
  Whitespace(WhitespaceToken),

  /// Spans of newlines.
  #[display(fmt = "{}", _0)]
  Newlines(NewlinesToken),

  /// Comment spans.
  #[display(fmt = "{}", _0)]
  Comment(CommentToken),

  /// Label.
  #[display(fmt = "{}", _0)]
  Label(LabelToken),

  /// Numeric Address.
  #[display(fmt = "{}", _0)]
  Address(Address),

  /// Instruction.
  #[display(fmt = "{}", _0)]
  Instruction(Instruction),
}

// /// Consume [Token]s produced by the lexer, producing a parse tree.
// ///
// /// # Returns
// ///
// /// `None` - end of file has been successfully reached.
// ///
// /// `Some(Err(ParserError))` - a parsing error has occurred.
// ///
// /// `Some(Ok(Node))` - successful parse.
// impl Iterator for Parser {
//   type Item = Result<Node, Error>;

//   fn next(&mut self) -> Option<Self::Item> {
//     macro_rules! next {
//       () => {
//         match self.lexer.next()? {
//           Ok(token) => token,
//           Err(error) => return Some(Err(Error::from(error))),
//         }
//       };
//     }

//     match next!() {
//       /// Not relevant for parsing.
//       Token::Whitespace(token) => Some(Ok(Node::from(token))),
//       Token::Newlines(token) => Some(Ok(Node::from(token))),
//       Token::Comment(token) => Some(Ok(Node::from(token))),
//       Token::Label(token) => Some(Ok(Node::from(token))),

//       /// Addresses.
//       Token::NumericAddress(token) => Some(Ok(Node::from(Address::from(token)))),
//       Token::NamedAddress(token) => Some(Ok(Node::from(Address::from(token)))),
//       Token::PredefinedAddress(token) => Some(Ok(Node::from(Address::from(token)))),

//       /// Error conditions.
//       token @ Token::Jump(_) | token @ Token::Equal(_) | token @ Token::Semicolon(_) => {
//         Some(Err(Error::Token(token)))
//       }

//       /// Found either a full instruction or an assignment.
//       Token::Destination(destination) => todo!(),

//       /// Found a branch.
//       Token::Computation(token) => todo!(),
//     }
//   }
// }
