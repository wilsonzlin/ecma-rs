use hir_js::FileId;
use parse_js::error::SyntaxError;
use parse_js::loc::Loc;

#[derive(Clone, Copy, Debug)]
pub struct Span {
  pub file: FileId,
  pub loc: Loc,
}

impl Span {
  pub fn new(file: FileId, loc: Loc) -> Self {
    Span { file, loc }
  }
}

#[derive(Clone, Debug)]
pub struct Diagnostic {
  pub code: &'static str,
  pub message: String,
  pub span: Option<Span>,
}

impl Diagnostic {
  pub fn new(code: &'static str, message: impl Into<String>, span: Option<Span>) -> Self {
    Diagnostic {
      code,
      message: message.into(),
      span,
    }
  }

  pub fn unsupported(code: &'static str, message: impl Into<String>, span: Span) -> Self {
    Diagnostic::new(code, message, Some(span))
  }

  pub fn missing_annotation(code: &'static str, name: &str, span: Span) -> Self {
    Diagnostic::new(
      code,
      format!("Missing type annotation for `{name}`"),
      Some(span),
    )
  }

  pub fn from_syntax_error(file: FileId, err: &SyntaxError) -> Self {
    Diagnostic::new(
      "TC1999",
      format!("Syntax error: {err}"),
      Some(Span::new(file, err.loc)),
    )
  }
}
