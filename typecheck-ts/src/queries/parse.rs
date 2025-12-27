pub use diagnostics::{Diagnostic, FileId, Span, TextRange};
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use std::sync::Arc;

use crate::lib_support::FileKind;

/// Result of parsing a single file.
#[derive(Debug, Clone)]
pub struct ParseResult {
  /// Parsed AST, if the source was syntactically valid.
  pub ast: Option<Arc<Node<TopLevel>>>,
  /// Diagnostics emitted during parsing.
  pub diagnostics: Vec<Diagnostic>,
}

impl PartialEq for ParseResult {
  fn eq(&self, other: &Self) -> bool {
    let ast_equal = match (&self.ast, &other.ast) {
      (Some(left), Some(right)) => Arc::ptr_eq(left, right),
      (None, None) => true,
      _ => false,
    };
    ast_equal && self.diagnostics == other.diagnostics
  }
}

impl Eq for ParseResult {}

impl ParseResult {
  /// Convenience helper for a successful parse with no diagnostics.
  pub fn ok(ast: Node<TopLevel>) -> Self {
    Self {
      ast: Some(Arc::new(ast)),
      diagnostics: Vec::new(),
    }
  }

  /// Convenience helper for a failed parse with a single diagnostic.
  pub fn error(diagnostic: Diagnostic) -> Self {
    Self {
      ast: None,
      diagnostics: vec![diagnostic],
    }
  }
}

/// Parse a file and convert any syntax errors into diagnostics.
///
/// This is the single entry point for turning source text into an AST. Options
/// are derived from the [`FileKind`] to ensure deterministic parsing across the
/// codebase. `source` must be valid UTF-8 because spans are expressed in UTF-8
/// byte offsets.
pub fn parse(file: FileId, kind: FileKind, source: &str) -> ParseResult {
  let dialect = match kind {
    FileKind::Js => Dialect::Js,
    FileKind::Ts => Dialect::Ts,
    FileKind::Tsx => Dialect::Tsx,
    FileKind::Jsx => Dialect::Jsx,
    FileKind::Dts => Dialect::Dts,
  };

  match parse_with_options(
    source,
    ParseOptions {
      dialect,
      source_type: SourceType::Module,
    },
  ) {
    Ok(ast) => ParseResult::ok(ast),
    Err(err) => ParseResult::error(err.to_diagnostic(file)),
  }
}
