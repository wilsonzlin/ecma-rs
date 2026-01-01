use ast::node::Node;
use ast::stx::TopLevel;
use error::{SyntaxError, SyntaxErrorType, SyntaxResult};
use lex::Lexer;
use parse::Parser;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

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

#[derive(Debug)]
struct ParseCancelled;

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

/// Parse JavaScript or TypeScript source with explicit [`ParseOptions`], allowing
/// cooperative cancellation via `cancel`.
///
/// This is primarily intended for long-running conformance suites where a
/// misbehaving input could otherwise stall the whole runner. Cancellation is
/// best-effort: the parser checks `cancel` during tokenization/parsing and
/// returns [`SyntaxErrorType::Cancelled`] once observed.
pub fn parse_with_options_cancellable(
  source: &str,
  opts: ParseOptions,
  cancel: Arc<AtomicBool>,
) -> SyntaxResult<Node<TopLevel>> {
  let lexer = Lexer::new(source);
  let mut parser = Parser::new_cancellable(lexer, opts, Some(cancel));

  let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| parser.parse_top_level()));
  match result {
    Ok(result) => result,
    Err(payload) => {
      if payload.is::<ParseCancelled>() {
        return Err(SyntaxError::new(
          SyntaxErrorType::Cancelled,
          loc::Loc(source.len(), source.len()),
          None,
        ));
      }
      std::panic::resume_unwind(payload)
    }
  }
}
