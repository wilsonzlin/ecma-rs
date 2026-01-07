use super::Expr;
use crate::ast::class_or_object::ObjMember;
use crate::ast::node::Node;
use crate::num::JsNumber;
use derive_visitor::Drive;
use derive_visitor::DriveMut;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub enum LitArrElem {
  Single(Node<Expr>),
  Rest(Node<Expr>),
  Empty,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct LitArrExpr {
  pub elements: Vec<LitArrElem>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct LitBigIntExpr {
  #[drive(skip)]
  /// Canonical decimal representation without the trailing `n`.
  pub value: String,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct LitBoolExpr {
  #[drive(skip)]
  pub value: bool,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct LitNullExpr {}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct LitNumExpr {
  #[drive(skip)]
  pub value: JsNumber,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct LitObjExpr {
  pub members: Vec<Node<ObjMember>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct LitRegexExpr {
  #[drive(skip)]
  pub value: String, // Including delimiter slashes and any flags.
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct LitStrExpr {
  #[drive(skip)]
  pub value: String,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct LitTemplateExpr {
  pub parts: Vec<LitTemplatePart>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub enum LitTemplatePart {
  Substitution(Node<Expr>),
  #[drive(skip)]
  String(String),
}
