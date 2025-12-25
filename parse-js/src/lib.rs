use ast::node::Node;
use ast::stx::TopLevel;
use error::SyntaxResult;
use lex::Lexer;
use parse::Parser;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Dialect {
  Js,
  Jsx,
  Ts,
  Tsx,
  Dts,
}

impl Dialect {
  pub fn allows_jsx(self) -> bool {
    matches!(self, Dialect::Jsx | Dialect::Tsx)
  }

  pub fn is_typescript(self) -> bool {
    matches!(self, Dialect::Ts | Dialect::Tsx | Dialect::Dts)
  }

  pub fn allows_angle_bracket_type_assertions(self) -> bool {
    matches!(self, Dialect::Ts | Dialect::Dts)
  }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceType {
  Script,
  Module,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ParseOptions {
  pub dialect: Dialect,
  pub source_type: SourceType,
}

impl Default for ParseOptions {
  fn default() -> Self {
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    }
  }
}

pub mod ast;
pub mod char;
pub mod error;
pub mod lex;
pub mod loc;
pub mod num;
pub mod operator;
pub mod parse;
pub mod token;
pub mod util;

/// Parse JavaScript or TypeScript source as UTF-8 and return the top-level AST.
///
/// Spans and diagnostics are expressed in UTF-8 byte offsets. Callers starting
/// from raw bytes should validate/convert to `&str` at the I/O boundary before
/// invoking the parser.
pub fn parse(source: &str) -> SyntaxResult<Node<TopLevel>> {
  parse_with_options(source, ParseOptions::default())
}

/// Parse JavaScript or TypeScript source with explicit [`ParseOptions`].
///
/// The source **must** be valid UTF-8; span math assumes byte offsets into the
/// original string. See [`parse`] for the recommended boundary validation
/// strategy when starting from raw bytes.
pub fn parse_with_options(source: &str, opts: ParseOptions) -> SyntaxResult<Node<TopLevel>> {
  let lexer = Lexer::new(source);
  let mut parser = Parser::new(lexer, opts);
  parser.parse_top_level()
}
