use crate::diagnostic::Span;
use crate::types::Type;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
  Number(f64),
  String(String),
  Boolean(bool),
  Object(Vec<ObjectField>),
  Array(Vec<Expr>),
  Identifier(String),
  TypeAssertion { expr: Box<Expr>, typ: Type },
  ConstAssertion(Box<Expr>),
  Satisfies { expr: Box<Expr>, typ: Type },
}

#[derive(Debug, Clone, PartialEq)]
pub struct ObjectField {
  pub name: String,
  pub value: Expr,
  pub span: Option<Span>,
}

impl ObjectField {
  pub fn new(name: impl Into<String>, value: Expr) -> ObjectField {
    ObjectField {
      name: name.into(),
      value,
      span: None,
    }
  }

  pub fn with_span(mut self, span: Span) -> Self {
    self.span = Some(span);
    self
  }
}
