use super::Expr;
use super::IdExpr;
use crate::ast::node::Node;
use derive_visitor::Drive;
use derive_visitor::DriveMut;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub enum JsxAttrVal {
  Expression(Node<JsxExprContainer>),
  Text(Node<JsxText>),
  Element(Node<JsxElem>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub enum JsxAttr {
  Named {
    name: Node<JsxName>,
    value: Option<JsxAttrVal>,
  },
  Spread {
    value: Node<JsxSpreadAttr>,
  },
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
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

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub enum JsxElemChild {
  Element(Node<JsxElem>),
  Expr(Node<JsxExprContainer>),
  Text(Node<JsxText>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct JsxElem {
  // JSX distinguishes intrinsic elements (e.g. `<div>`, `<my-tag>`, `<Svg:Path>`) from
  // value-based component references (e.g. `<Foo>`, `<Foo.Bar>`) primarily by capitalization.
  //
  // Additionally, namespaced (`:`) and hyphenated (`-`) tag names are always treated as
  // intrinsic, regardless of capitalization.
  //
  // https://reactjs.org/docs/jsx-in-depth.html#user-defined-components-must-be-capitalized
  pub name: Option<JsxElemName>, // None if fragment
  pub attributes: Vec<JsxAttr>,  // Always empty if fragment
  pub children: Vec<JsxElemChild>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct JsxExprContainer {
  #[drive(skip)]
  pub spread: bool,
  pub value: Node<Expr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct JsxMemberExpr {
  // This is a separate property to indicate it's required and for easier pattern matching.
  pub base: Node<IdExpr>,
  #[drive(skip)]
  pub path: Vec<String>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct JsxName {
  #[drive(skip)]
  pub namespace: Option<String>,
  #[drive(skip)]
  pub name: String,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct JsxSpreadAttr {
  pub value: Node<Expr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct JsxText {
  #[drive(skip)]
  pub value: String,
}
