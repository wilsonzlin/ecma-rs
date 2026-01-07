pub mod jsx;
pub mod lit;
pub mod pat;

use super::class_or_object::ClassMember;
use super::func::Func;
use super::node::Node;
use super::type_expr::TypeExpr;
use crate::operator::OperatorName;
use derive_more::derive::From;
use derive_more::derive::TryInto;
use derive_visitor::Drive;
use derive_visitor::DriveMut;
use jsx::JsxElem;
use jsx::JsxExprContainer;
use jsx::JsxMemberExpr;
use jsx::JsxName;
use jsx::JsxSpreadAttr;
use jsx::JsxText;
use lit::LitArrExpr;
use lit::LitBigIntExpr;
use lit::LitBoolExpr;
use lit::LitNullExpr;
use lit::LitNumExpr;
use lit::LitObjExpr;
use lit::LitRegexExpr;
use lit::LitStrExpr;
use lit::LitTemplateExpr;
use lit::LitTemplatePart;
use pat::ArrPat;
use pat::ClassOrFuncName;
use pat::IdPat;
use pat::ObjPat;

// We must wrap each variant with Node<T> as otherwise we won't be able to visit Node<T> instead of just T.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(tag = "$t"))]
#[derive(Debug, Drive, DriveMut, From, TryInto)]
pub enum Expr {
  ArrowFunc(Node<ArrowFuncExpr>),
  Binary(Node<BinaryExpr>),
  Call(Node<CallExpr>),
  Class(Node<ClassExpr>),
  ComputedMember(Node<ComputedMemberExpr>),
  Cond(Node<CondExpr>),
  Func(Node<FuncExpr>),
  Id(Node<IdExpr>),
  Import(Node<ImportExpr>),
  ImportMeta(Node<ImportMeta>),
  Member(Node<MemberExpr>),
  NewTarget(Node<NewTarget>),
  Super(Node<SuperExpr>),
  TaggedTemplate(Node<TaggedTemplateExpr>),
  This(Node<ThisExpr>),
  Unary(Node<UnaryExpr>),
  UnaryPostfix(Node<UnaryPostfixExpr>),

  // JSX.
  JsxElem(Node<JsxElem>),
  JsxExprContainer(Node<JsxExprContainer>),
  JsxMember(Node<JsxMemberExpr>),
  JsxName(Node<JsxName>),
  JsxSpreadAttr(Node<JsxSpreadAttr>),
  JsxText(Node<JsxText>),

  // Literals.
  LitArr(Node<LitArrExpr>),
  LitBigInt(Node<LitBigIntExpr>),
  LitBool(Node<LitBoolExpr>),
  LitNull(Node<LitNullExpr>),
  LitNum(Node<LitNumExpr>),
  LitObj(Node<LitObjExpr>),
  LitRegex(Node<LitRegexExpr>),
  LitStr(Node<LitStrExpr>),
  LitTemplate(Node<LitTemplateExpr>),

  // Patterns.
  ArrPat(Node<ArrPat>),
  IdPat(Node<IdPat>),
  ObjPat(Node<ObjPat>),

  // TypeScript expressions
  Instantiation(Node<InstantiationExpr>),
  TypeAssertion(Node<TypeAssertionExpr>),
  NonNullAssertion(Node<NonNullAssertionExpr>),
  SatisfiesExpr(Node<SatisfiesExpr>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct CallArg {
  #[drive(skip)]
  pub spread: bool,
  pub value: Node<Expr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ArrowFuncExpr {
  pub func: Node<Func>, // Always Function.
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct BinaryExpr {
  #[drive(skip)]
  pub operator: OperatorName,
  pub left: Node<Expr>,
  pub right: Node<Expr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct CallExpr {
  #[drive(skip)]
  pub optional_chaining: bool,
  pub callee: Node<Expr>,
  pub arguments: Vec<Node<CallArg>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ClassExpr {
  pub decorators: Vec<Node<Decorator>>,
  pub name: Option<Node<ClassOrFuncName>>,
  pub type_parameters: Option<Vec<Node<super::type_expr::TypeParameter>>>,
  pub extends: Option<Node<Expr>>,
  pub implements: Vec<Node<TypeExpr>>,
  pub members: Vec<Node<ClassMember>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct CondExpr {
  pub test: Node<Expr>,
  pub consequent: Node<Expr>,
  pub alternate: Node<Expr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ComputedMemberExpr {
  #[drive(skip)]
  pub optional_chaining: bool,
  pub object: Node<Expr>,
  pub member: Node<Expr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct FuncExpr {
  pub name: Option<Node<ClassOrFuncName>>,
  pub func: Node<Func>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct IdExpr {
  #[drive(skip)]
  pub name: String,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ImportExpr {
  pub module: Node<Expr>,
  pub attributes: Option<Node<Expr>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ImportMeta {}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct NewTarget {}

// Dedicated special type to easily distinguish when analysing and minifying. Also done to avoid using IdentifierExpr as right, which is incorrect (not a variable usage).

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct MemberExpr {
  #[drive(skip)]
  pub optional_chaining: bool,
  pub left: Node<Expr>,
  #[drive(skip)]
  pub right: String,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct SuperExpr {}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ThisExpr {}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TaggedTemplateExpr {
  pub function: Node<Expr>,
  pub parts: Vec<LitTemplatePart>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct UnaryExpr {
  #[drive(skip)]
  pub operator: OperatorName,
  pub argument: Node<Expr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct UnaryPostfixExpr {
  #[drive(skip)]
  pub operator: OperatorName,
  pub argument: Node<Expr>,
}

// TypeScript expressions

/// Instantiation expression: expr<TypeArgs>
/// TypeScript 4.7+ allows this without an immediate call suffix (e.g. `foo<string>`).
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct InstantiationExpr {
  pub expression: Box<Node<Expr>>,
  pub type_arguments: Vec<Node<TypeExpr>>,
}

/// Type assertion: value as Type or value as const
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeAssertionExpr {
  pub expression: Box<Node<Expr>>,
  pub type_annotation: Option<Node<TypeExpr>>, // None for "as const"
  #[drive(skip)]
  pub const_assertion: bool,   // true for "as const"
}

/// Non-null assertion: value!
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct NonNullAssertionExpr {
  pub expression: Box<Node<Expr>>,
}

/// Satisfies expression: value satisfies Type
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct SatisfiesExpr {
  pub expression: Box<Node<Expr>>,
  pub type_annotation: Node<TypeExpr>,
}

/// Decorator: @decorator or @decorator(args)
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct Decorator {
  pub expression: Node<Expr>,
}
