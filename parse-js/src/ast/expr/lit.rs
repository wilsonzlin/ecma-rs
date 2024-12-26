use derive_visitor::{Drive, DriveMut};
use serde::Serialize;

use crate::{ast::{class_or_object::ObjMember, node::Node}, num::JsNumber};

use super::Expr;



#[derive(Debug, Drive, DriveMut, Serialize)]
pub enum LitArrElem {
  Single(Node<Expr>),
  Rest(Node<Expr>),
  Empty,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct LitArrExpr {
  pub elements: Vec<LitArrElem>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct LitBigIntExpr {
  #[drive(skip)]
  pub value: String,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct LitBoolExpr {
  #[drive(skip)]
  pub value: bool,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct LitNullExpr {}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct LitNumExpr {
  #[drive(skip)]
  pub value: JsNumber,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct LitObjExpr {
  pub members: Vec<Node<ObjMember>>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct LitRegexExpr {
  #[drive(skip)]
  pub value: String, // Including delimiter slashes and any flags.
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct LitStrExpr {
  #[drive(skip)]
  pub value: String,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct LitTemplateExpr {
  pub parts: Vec<LitTemplatePart>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub enum LitTemplatePart {
  Substitution(Node<Expr>),
  #[drive(skip)]
  String(String),
}
