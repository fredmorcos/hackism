//! Tokens produced by a `HACK` [Lexer].

use super::Computation;
use super::Destination;
use super::Jump;
use super::PredefinedAddress;
use crate::utilities::Span;
use derive_more::Display;

/// Spans of whitespace.
#[derive(new, Debug, Display, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "Whitespace {}", span)]
pub struct WhitespaceToken {
  span: Span,
}

/// Spans of newlines.
#[derive(new, Debug, Display, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "Newlines {}", span)]
pub struct NewlinesToken {
  span: Span,
}

/// Span of a single comment.
#[derive(new, Debug, Display, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "Comment {}", span)]
pub struct CommentToken {
  span: Span,
}

/// Numeric addresses.
#[derive(new, Debug, Display, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "HACK Numeric Address `{}` {}", address, span)]
pub struct NumericAddressToken {
  span: Span,
  address: u16,
}

/// Named addresses.
#[derive(new, Debug, Display, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "HACK Named Address {}", span)]
pub struct NamedAddressToken {
  span: Span,
}

/// Predefined addresses.
#[derive(new, Debug, Display, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "HACK Predefined Address `{}` {}", address, span)]
pub struct PredefinedAddressToken {
  span: Span,
  address: PredefinedAddress,
}

/// Label.
#[derive(new, Debug, Display, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "HACK Label {}", span)]
pub struct LabelToken {
  span: Span,
}

/// Destination.
#[derive(new, Debug, Display, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "HACK Destination `{}` {}", destination, span)]
pub struct DestinationToken {
  span: Span,
  destination: Destination,
}

/// Equal.
#[derive(new, Debug, Display, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "HACK Equal {}", span)]
pub struct EqualToken {
  span: Span,
}

/// Computation.
#[derive(new, Debug, Display, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "HACK Computation `{}` {}", computation, span)]
pub struct ComputationToken {
  span: Span,
  computation: Computation,
}

/// Semicolon.
#[derive(new, Debug, Display, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "HACK Semicolon {}", span)]
pub struct SemicolonToken {
  span: Span,
}

/// Jump.
#[derive(new, Debug, Display, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "HACK Jump `{}` {}", jump, span)]
pub struct JumpToken {
  span: Span,
  jump: Jump,
}

/// Kinds of tokens returned by the `HACK` lexer.
#[derive(new, Debug, Display, Clone, Copy, PartialEq, Eq)]
#[display(fmt = "HACK Token {}")]
pub enum Token {
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
  NumericAddress(NumericAddressToken),

  /// Named Address.
  #[display(fmt = "{}", _0)]
  NamedAddress(NamedAddressToken),

  /// Predefined Address.
  #[display(fmt = "{}", _0)]
  PredefinedAddress(PredefinedAddressToken),

  /// Destination.
  #[display(fmt = "{}", _0)]
  Destination(DestinationToken),

  /// Equal.
  #[display(fmt = "{}", _0)]
  Equal(EqualToken),

  /// Computation.
  #[display(fmt = "{}", _0)]
  Computation(ComputationToken),

  /// Semicolon.
  #[display(fmt = "{}", _0)]
  Semicolon(SemicolonToken),

  /// Jump.
  #[display(fmt = "{}", _0)]
  Jump(JumpToken),
}

impl Token {
  /// Get the span of a token.
  pub fn span(&self) -> Span {
    match self {
      Token::Whitespace(token) => token.span,
      Token::Newlines(token) => token.span,
      Token::Comment(token) => token.span,
      Token::NumericAddress(token) => token.span,
      Token::NamedAddress(token) => token.span,
      Token::PredefinedAddress(token) => token.span,
      Token::Label(token) => token.span,
      Token::Destination(token) => token.span,
      Token::Equal(token) => token.span,
      Token::Computation(token) => token.span,
      Token::Semicolon(token) => token.span,
      Token::Jump(token) => token.span,
    }
  }

  /// Get the sequence of input bytes related to a token.
  pub fn text<'b>(&self, input: &'b [u8]) -> &'b [u8] {
    let span = self.span();
    &input[span.start().index()..span.end().index()]
  }

  /// Create a new whitespace token.
  pub fn whitespace(span: Span) -> Self {
    Self::Whitespace(WhitespaceToken::new(span))
  }

  /// Create a new newlines token.
  pub fn newlines(span: Span) -> Self {
    Self::Newlines(NewlinesToken::new(span))
  }

  /// Create a new comment token.
  pub fn comment(span: Span) -> Self {
    Self::Comment(CommentToken::new(span))
  }

  /// Create a new numeric address token.
  pub fn numeric_address(span: Span, address: u16) -> Self {
    Self::NumericAddress(NumericAddressToken::new(span, address))
  }

  /// Create a new predefined address token.
  pub fn predefined_address(span: Span, address: PredefinedAddress) -> Self {
    Self::PredefinedAddress(PredefinedAddressToken::new(span, address))
  }

  /// Create a new named address token.
  pub fn named_address(span: Span) -> Self {
    Self::NamedAddress(NamedAddressToken::new(span))
  }

  /// Create a new label token.
  pub fn label(span: Span) -> Self {
    Self::Label(LabelToken::new(span))
  }

  /// Create a new equal token.
  pub fn equal(span: Span) -> Self {
    Self::Equal(EqualToken::new(span))
  }

  /// Create a new semicolon token.
  pub fn semicolon(span: Span) -> Self {
    Self::Semicolon(SemicolonToken::new(span))
  }

  /// Create a new destination token.
  pub fn destination(span: Span, destination: Destination) -> Self {
    Self::Destination(DestinationToken::new(span, destination))
  }

  /// Create a new computation token.
  pub fn computation(span: Span, computation: Computation) -> Self {
    Self::Computation(ComputationToken::new(span, computation))
  }

  /// Create a new jump token.
  pub fn jump(span: Span, jump: Jump) -> Self {
    Self::Jump(JumpToken::new(span, jump))
  }
}
