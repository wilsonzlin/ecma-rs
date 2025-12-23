use parse_js::loc::Loc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
  pub code: &'static str,
  pub message: String,
  pub span: Loc,
}

impl Diagnostic {
  pub fn new(code: &'static str, message: impl Into<String>, span: Loc) -> Self {
    Self {
      code,
      message: message.into(),
      span,
    }
  }
}
