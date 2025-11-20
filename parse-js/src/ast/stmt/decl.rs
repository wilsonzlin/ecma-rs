use crate::ast::class_or_object::ClassMember;
use crate::ast::expr::pat::ClassOrFuncName;
use crate::ast::expr::pat::Pat;
use crate::ast::expr::Decorator;
use crate::ast::expr::Expr;
use crate::ast::func::Func;
use crate::ast::node::Node;
use crate::ast::type_expr::TypeExpr;
use crate::ast::type_expr::TypeParameter;
use derive_visitor::Drive;
use derive_visitor::DriveMut;
use serde::Serialize;

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ClassDecl {
  pub decorators: Vec<Node<Decorator>>,
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub export_default: bool,
  #[drive(skip)]
  pub declare: bool,
  #[drive(skip)]
  pub abstract_: bool,
  pub name: Option<Node<ClassOrFuncName>>, // Name can only be omitted in a default export, although a default export class can still have a name.
  pub type_parameters: Option<Vec<Node<TypeParameter>>>,
  pub extends: Option<Node<Expr>>,
  pub implements: Vec<Node<Expr>>, // Changed from TypeExpr to Expr to support optional chaining (A?.B)
  pub members: Vec<Node<ClassMember>>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct FuncDecl {
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub export_default: bool,
  pub name: Option<Node<ClassOrFuncName>>, // Name can only be omitted in a default export, although a default export function can still have a name.
  pub function: Node<Func>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ParamDecl {
  pub decorators: Vec<Node<Decorator>>,
  #[drive(skip)]
  pub rest: bool,
  #[drive(skip)]
  pub optional: bool,
  pub accessibility: Option<Accessibility>,
  #[drive(skip)]
  pub readonly: bool,
  pub pattern: Node<PatDecl>,
  pub type_annotation: Option<Node<TypeExpr>>,
  pub default_value: Option<Node<Expr>>,
}

#[derive(Debug, Copy, Clone, Serialize, Drive, DriveMut)]
pub enum Accessibility {
  Public,
  Private,
  Protected,
}

// Since a pattern can also be in an expression (e.g. assignment), have a specific unified type for declarations (e.g. imports, function params, var/let/const, catch binding) only, useful for downstream tasks. This contains only the pattern; it shouldn't contain any expressions (e.g. initializer) as that itself could contain patterns (e.g. assignment), defeating the purpose.
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct PatDecl {
  pub pat: Node<Pat>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct VarDecl {
  #[drive(skip)]
  pub export: bool,
  pub mode: VarDeclMode,
  pub declarators: Vec<VarDeclarator>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct VarDeclarator {
  pub pattern: Node<PatDecl>,
  #[drive(skip)]
  pub definite_assignment: bool,
  pub type_annotation: Option<Node<TypeExpr>>,
  pub initializer: Option<Node<Expr>>,
}

#[derive(Eq, PartialEq, Clone, Copy, Debug, Serialize, Drive, DriveMut)]
pub enum VarDeclMode {
  Const,
  Let,
  Var,
  Using,
  AwaitUsing,
}
