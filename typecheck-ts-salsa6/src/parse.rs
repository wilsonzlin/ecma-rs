use crate::db::Db;
use crate::host::FileId;
use crate::options::CompilerOptions;
use crate::Diagnostic;
use crate::DiagnosticCode;
use crate::Span;
use crate::TextRange;
use parse_js as parse_js_crate;
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use parse_js::error::SyntaxError;
use std::fmt;
use std::sync::Arc;

/// Result of parsing a file.
#[derive(Clone)]
pub struct ParseOutput {
  /// The parsed syntax tree.
  pub ast: Arc<Node<TopLevel>>,
  /// Diagnostics produced during parsing.
  pub diagnostics: Vec<Diagnostic<FileId>>,
}

impl PartialEq for ParseOutput {
  fn eq(&self, other: &Self) -> bool {
    Arc::ptr_eq(&self.ast, &other.ast) && self.diagnostics == other.diagnostics
  }
}

impl Eq for ParseOutput {}

impl fmt::Debug for ParseOutput {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("ParseOutput")
      .field("diagnostics", &self.diagnostics)
      .finish()
  }
}

fn syntax_error_to_diagnostic(file: FileId, error: SyntaxError) -> Diagnostic<FileId> {
  let loc = error.loc;
  let start = loc.0 as u32;
  let end = loc.1 as u32;
  Diagnostic::error(DiagnosticCode("PARSE"), format!("{error}"))
    .with_primary(Span::new(file, TextRange::new(start, end)))
}

/// Salsa query that parses a file.
pub(crate) fn parse(db: &dyn Db, file: FileId) -> ParseOutput {
  let _opts: CompilerOptions = db.compiler_options();
  let _kind = db.file_kind(file);
  let source = db.file_text(file);

  match parse_js_crate::parse(&source) {
    Ok(ast) => ParseOutput {
      ast: Arc::new(ast),
      diagnostics: Vec::new(),
    },
    Err(error) => ParseOutput {
      ast: Arc::new(Node::new(parse_js_crate::loc::Loc(0, 0), TopLevel {
        body: Vec::new(),
      })),
      diagnostics: vec![syntax_error_to_diagnostic(file, error)],
    },
  }
}
