pub mod pat;
pub mod lit;
pub mod jsx;

use derive_more::derive::{From, TryInto};
use derive_visitor::{Drive, DriveMut};
use jsx::{JsxElem, JsxExprContainer, JsxMemberExpr, JsxName, JsxSpreadAttr, JsxText};
use lit::{LitArrExpr, LitBigIntExpr, LitBoolExpr, LitNullExpr, LitNumExpr, LitObjExpr, LitRegexExpr, LitStrExpr, LitTemplateExpr, LitTemplatePart};
use pat::{ArrPat, ClassOrFuncName, IdPat, ObjPat};
use serde::{Deserialize, Serialize};

use crate::operator::OperatorName;

use super::{class_or_object::ClassMember, func::Func, node::Node};


#[derive(Debug, Drive, DriveMut, From, Serialize, TryInto)]
#[serde(tag = "$t")]
pub enum Expr {
  ArrowFunc(ArrowFuncExpr),
  Binary(BinaryExpr),
  Call(CallExpr),
  Class(ClassExpr),
  ComputedMember(ComputedMemberExpr),
  Conditional(CondExpr),
  Func(FuncExpr),
  Id(IdExpr),
  Import(ImportExpr),
  ImportMeta(ImportMeta),
  Member(MemberExpr),
  Super(SuperExpr),
  TaggedTemplate(TaggedTemplateExpr),
  This(ThisExpr),
  Unary(UnaryExpr),
  UnaryPostfix(UnaryPostfixExpr),

  // JSX.
  JsxElem(JsxElem),
  JsxExprContainer(JsxExprContainer),
  JsxMember(JsxMemberExpr),
  JsxName(JsxName),
  JsxSpreadAttr(JsxSpreadAttr),
  JsxText(JsxText),

  // Literals.
  LitArr(LitArrExpr),
  LitBigInt(LitBigIntExpr),
  LitBool(LitBoolExpr),
  LitNull(LitNullExpr),
  LitNum(LitNumExpr),
  LitObj(LitObjExpr),
  LitRegex(LitRegexExpr),
  LitStr(LitStrExpr),
  LitTemplate(LitTemplateExpr),

  // Patterns.
  ArrPat(ArrPat),
  IdPat(IdPat),
  ObjPat(ObjPat),
}


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct CallArg {
  #[drive(skip)]
  pub spread: bool,
  pub value: Node<Expr>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ArrowFuncExpr {
  pub func: Node<Func>, // Always Function.
}


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct BinaryExpr {
  #[drive(skip)]
  pub operator: OperatorName,
  pub left: Node<Expr>,
  pub right: Node<Expr>,
}


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct CallExpr {
  #[drive(skip)]
  pub optional_chaining: bool,
  pub callee: Node<Expr>,
  pub arguments: Vec<Node<CallArg>>,
}


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ClassExpr {
  pub name: Option<Node<ClassOrFuncName>>,
  pub extends: Option<Node<Expr>>,
  pub members: Vec<Node<ClassMember>>,
}


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct CondExpr {
  pub test: Node<Expr>,
  pub consequent: Node<Expr>,
  pub alternate: Node<Expr>,
}


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ComputedMemberExpr {
  #[drive(skip)]
  pub optional_chaining: bool,
  pub object: Node<Expr>,
  pub member: Node<Expr>,
}


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct FuncExpr {
  pub name: Option<Node<ClassOrFuncName>>,
  pub func: Node<Func>,
}


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct IdExpr {
  #[drive(skip)]
  pub name: String,
}


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ImportExpr {
  pub module: Node<Expr>,
}


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ImportMeta {
}

// Dedicated special type to easily distinguish when analysing and minifying. Also done to avoid using IdentifierExpr as right, which is incorrect (not a variable usage).

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct MemberExpr {
  #[drive(skip)]
  pub optional_chaining: bool,
  pub left: Node<Expr>,
  #[drive(skip)]
  pub right: String,
}


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct SuperExpr {

}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ThisExpr {

}


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct TaggedTemplateExpr {
  pub function: Node<Expr>,
  pub parts: Vec<LitTemplatePart>,
}


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct UnaryExpr {
  #[drive(skip)]
  pub operator: OperatorName,
  pub argument: Node<Expr>,
}


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct UnaryPostfixExpr {
  #[drive(skip)]
  pub operator: OperatorName,
  pub argument: Node<Expr>,
}
