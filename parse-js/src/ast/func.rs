use derive_more::derive::From;
use derive_visitor::{Drive, DriveMut};
use serde::{Deserialize, Serialize};

use super::{expr::Expr, node::Node, stmt::{decl::ParamDecl, Stmt}, type_expr::{TypeExpr, TypeParameter}};

  // This common type exists for better downstream usage, as one type is easier to match on and wrangle than many different types (ArrowFunctionExpr, ClassMember::Method, FunctionDecl, etc.).
  #[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct Func {
    #[drive(skip)]
    pub arrow: bool,
    #[drive(skip)]
    pub async_: bool,
    #[drive(skip)]
    pub generator: bool,
    pub type_parameters: Option<Vec<Node<TypeParameter>>>,
    pub parameters: Vec<Node<ParamDecl>>,
    pub return_type: Option<Node<TypeExpr>>,
    pub body: FuncBody,
  }

  // A function body is different from a block statement, as the scopes are different. This doesn't mean much at the parser level, but helps with downstream usages.
  #[derive(Debug, Drive, DriveMut, From, Serialize)]
  pub enum FuncBody {
    Block(Vec<Node<Stmt>>),
    // If arrow function.
    Expression(Node<Expr>),
  }
