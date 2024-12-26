use derive_visitor::{Drive, DriveMut};
use serde::{Deserialize, Serialize};

use crate::ast::{class_or_object::ClassMember, expr::{pat::{ClassOrFuncName, Pat}, Expr}, func::Func, node::Node};


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ClassDecl {
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub export_default: bool,
  pub name: Option<Node<ClassOrFuncName>>, // Name can only be omitted in a default export, although a default export class can still have a name.
  pub extends: Option<Node<Expr>>,
  pub members: Vec<Node<ClassMember>>
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
  #[drive(skip)]
  pub rest: bool,
  pub pattern: Node<PatDecl>,
  pub default_value: Option<Node<Expr>>,
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
  pub initializer: Option<Node<Expr>>,
}


#[derive(Eq, PartialEq, Clone, Copy, Debug, Serialize, Drive, DriveMut)]
pub enum VarDeclMode {
  Const,
  Let,
  Var,
}
