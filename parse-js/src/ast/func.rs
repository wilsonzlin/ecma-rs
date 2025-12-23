use super::expr::Expr;
use super::node::Node;
use super::stmt::decl::ParamDecl;
use super::stmt::Stmt;
use super::type_expr::TypeExpr;
use super::type_expr::TypeParameter;
use derive_more::derive::From;
use derive_visitor::Drive;
use derive_visitor::DriveMut;
use serde::Serialize;

// This common type exists for better downstream usage, as one type is easier to match on and wrangle than many different types (ArrowFunctionExpr, ClassMember::Method, FunctionDecl, etc.).
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct Func {
  #[drive(skip)]
  pub arrow: bool,
  #[drive(skip)]
  pub async_: bool,
  #[drive(skip)]
  pub generator: bool,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub type_parameters: Option<Vec<Node<TypeParameter>>>,
  pub parameters: Vec<Node<ParamDecl>>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub return_type: Option<Node<TypeExpr>>,
  pub body: Option<FuncBody>, // TypeScript: overload signatures have no body
}

// A function body is different from a block statement, as the scopes are different. This doesn't mean much at the parser level, but helps with downstream usages.
#[derive(Debug, Drive, DriveMut, From, Serialize)]
pub enum FuncBody {
  Block(Vec<Node<Stmt>>),
  // If arrow function.
  Expression(Node<Expr>),
}
