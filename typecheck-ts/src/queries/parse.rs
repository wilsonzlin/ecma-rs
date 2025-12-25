pub use diagnostics::{Diagnostic, FileId, Span, TextRange};
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;

/// Result of parsing a single file.
#[derive(Debug)]
pub struct ParseResult {
  /// Parsed AST, if the source was syntactically valid.
  pub ast: Option<Node<TopLevel>>,
  /// Diagnostics emitted during parsing.
  pub diagnostics: Vec<Diagnostic>,
}

impl ParseResult {
  /// Convenience helper for a successful parse with no diagnostics.
  pub fn ok(ast: Node<TopLevel>) -> Self {
    Self {
      ast: Some(ast),
      diagnostics: Vec::new(),
    }
  }
}

/// Parse a file and convert any syntax errors into diagnostics.
///
/// On success, returns the AST with an empty diagnostics list. On failure, the
/// AST is `None` and a single [`Diagnostic`] describing the syntax error is
/// returned. Spans are converted from parse-js [`parse_js::loc::Loc`] into
/// [`Span`] with the provided [`FileId`] and [`TextRange`]. `source` must be
/// valid UTF-8 because spans are expressed in UTF-8 byte offsets.
pub fn parse(file: FileId, source: &str) -> ParseResult {
  match parse_js::parse(source) {
    Ok(ast) => ParseResult::ok(ast),
    Err(err) => ParseResult {
      ast: None,
      diagnostics: vec![err.to_diagnostic(file)],
    },
  }
}
