use super::Expr;
use super::IdExpr;
use crate::ast::node::Node;
use derive_visitor::Drive;
use derive_visitor::DriveMut;
use serde::Serialize;

#[derive(Debug, Drive, DriveMut, Serialize)]
pub enum JsxAttrVal {
  Expression(Node<JsxExprContainer>),
  Text(Node<JsxText>),
  Element(Node<JsxElem>),
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub enum JsxAttr {
  Named {
    name: Node<JsxName>,
    value: Option<JsxAttrVal>,
  },
  Spread {
    value: Node<JsxSpreadAttr>,
  },
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub enum JsxElemName {
  Id(Node<IdExpr>),
  Member(Node<JsxMemberExpr>),
  Name(Node<JsxName>),
}

impl PartialEq for JsxElemName {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (JsxElemName::Member(a), JsxElemName::Member(b)) => {
        a.stx.base.stx.name == b.stx.base.stx.name && a.stx.path == b.stx.path
      }
      (JsxElemName::Name(a), JsxElemName::Name(b)) => {
        a.stx.namespace == b.stx.namespace && a.stx.name == b.stx.name
      }
      (JsxElemName::Id(a), JsxElemName::Id(b)) => a.stx.name == b.stx.name,
      _ => false,
    }
  }
}

impl Eq for JsxElemName {}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub enum JsxElemChild {
  Element(Node<JsxElem>),
  Expr(Node<JsxExprContainer>),
  Text(Node<JsxText>),
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct JsxElem {
  // When an element name starts with a lowercase ASCII character, it's a built-in component like '<div>' or '<span>'.
  // For easier differentiation, we use IdentifierExpr for user-defined components as they are references to symbols and built-in components are not.
  // https://reactjs.org/docs/jsx-in-depth.html#user-defined-components-must-be-capitalized
  pub name: Option<JsxElemName>, // None if fragment
  pub attributes: Vec<JsxAttr>,  // Always empty if fragment
  pub children: Vec<JsxElemChild>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct JsxExprContainer {
  #[drive(skip)]
  pub spread: bool,
  pub value: Node<Expr>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct JsxMemberExpr {
  // This is a separate property to indicate it's required and for easier pattern matching.
  pub base: Node<IdExpr>,
  #[drive(skip)]
  pub path: Vec<String>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct JsxName {
  #[drive(skip)]
  pub namespace: Option<String>,
  #[drive(skip)]
  pub name: String,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct JsxSpreadAttr {
  pub value: Node<Expr>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct JsxText {
  #[drive(skip)]
  pub value: String,
}
