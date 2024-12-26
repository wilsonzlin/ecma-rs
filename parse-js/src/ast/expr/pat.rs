use derive_more::derive::From;
use derive_visitor::{Drive, DriveMut};
use serde::{Deserialize, Serialize};

use crate::ast::{class_or_object::ClassOrObjKey, node::Node};

use super::Expr;

#[derive(Debug, Drive, DriveMut, From, Serialize)]
#[serde(tag = "$t")]
pub enum Pat {
  Arr(ArrPat),
  Id(IdPat),
  Obj(ObjPat),
}

impl From<Pat> for Expr {
  fn from(value: Pat) -> Self {
    match value {
      Pat::Arr(arr) => Expr::ArrPat(arr),
      Pat::Id(id) => Expr::IdPat(id),
      Pat::Obj(obj) => Expr::ObjPat(obj),
    }
  }
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ArrPatElem {
  pub target: Node<Pat>,
  pub default_value: Option<Node<Expr>>,
}

// `const fn = (a: any, b: any, ...{ length, ...c }: any[]) => void 0` is allowed.
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ArrPat {
  // Unnamed elements can exist.
  pub elements: Vec<Option<ArrPatElem>>,
  pub rest: Option<Node<Pat>>,
}

// Not really a pattern but functions similarly so kept here in pat.rs.
// This exists as a separate AST node type for easy replacement when minifying.
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ClassOrFuncName {
  #[drive(skip)]
  pub name: String,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct IdPat {
  #[drive(skip)]
  pub name: String,
}

// For an object pattern, `...` must be followed by an identifier.
// `const fn = ({ a: { b = c } = d, ...e }: any) => void 0` is possible.
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ObjPat {
  pub properties: Vec<Node<ObjPatProp>>,
  pub rest: Option<Node<IdPat>>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ObjPatProp {
  pub key: ClassOrObjKey,
  // If `shorthand`, `key` is Direct and `target` is IdentifierPattern of same name. This way, there is always an IdentifierPattern that exists and can be visited, instead of also having to consider ClassOrObjectMemberKey::Direct as identifier if shorthand.
  pub target: Node<Pat>,
  #[drive(skip)]
  pub shorthand: bool,
  pub default_value: Option<Node<Expr>>,
}
