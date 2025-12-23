use hir_js_w8::FileId;
use hir_js_w8::TextRange;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
  pub file: FileId,
  pub range: TextRange,
}

impl Span {
  pub fn new(file: FileId, range: TextRange) -> Self {
    Self { file, range }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label {
  pub span: Span,
  pub message: Option<String>,
}

impl Label {
  pub fn new(span: Span, message: impl Into<String>) -> Self {
    Self {
      span,
      message: Some(message.into()),
    }
  }

  pub fn primary(span: Span) -> Self {
    Self {
      span,
      message: None,
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
  pub code: &'static str,
  pub message: String,
  pub primary: Span,
  pub labels: Vec<Label>,
}

impl Diagnostic {
  pub fn new(code: &'static str, message: impl Into<String>, primary: Span) -> Self {
    Self {
      code,
      message: message.into(),
      primary,
      labels: Vec::new(),
    }
  }

  pub fn with_label(mut self, label: Label) -> Self {
    self.labels.push(label);
    self
  }
}
