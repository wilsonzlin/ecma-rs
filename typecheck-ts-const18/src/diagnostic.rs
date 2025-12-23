#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
  pub start: usize,
  pub end: usize,
}

impl Span {
  pub fn new(start: usize, end: usize) -> Self {
    Span { start, end }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiagnosticKind {
  ExcessProperty { property: String },
  ConstAssertionNotLiteral,
  NotAssignable { from: String, to: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
  pub kind: DiagnosticKind,
  pub message: String,
  pub span: Option<Span>,
}

impl Diagnostic {
  pub fn excess_property(name: impl Into<String>, span: Option<Span>) -> Diagnostic {
    let name = name.into();
    Diagnostic {
      message: format!("Property '{}' is not expected in target type", name),
      kind: DiagnosticKind::ExcessProperty { property: name },
      span,
    }
  }

  pub fn const_assertion_not_literal() -> Diagnostic {
    Diagnostic {
      message:
        "A const assertion can only be applied to a literal, array literal, or object literal"
          .to_string(),
      kind: DiagnosticKind::ConstAssertionNotLiteral,
      span: None,
    }
  }

  pub fn not_assignable(from: impl Into<String>, to: impl Into<String>) -> Diagnostic {
    let from = from.into();
    let to = to.into();
    Diagnostic {
      message: format!("Type '{}' is not assignable to type '{}'", from, to),
      kind: DiagnosticKind::NotAssignable { from, to },
      span: None,
    }
  }
}
