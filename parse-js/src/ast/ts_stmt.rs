use super::expr::Expr;
use super::node::Node;
use super::stmt::Stmt;
use super::type_expr::TypeExpr;
use super::type_expr::TypeMember;
use super::type_expr::TypeParameter;
use derive_visitor::Drive;
use derive_visitor::DriveMut;
use serde::Serialize;

/// Interface declaration: interface Foo<T> extends Bar { }
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct InterfaceDecl {
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub declare: bool,
  #[drive(skip)]
  pub name: String,
  pub type_parameters: Option<Vec<Node<TypeParameter>>>,
  pub extends: Vec<Node<TypeExpr>>,
  pub members: Vec<Node<TypeMember>>,
}

/// Type alias declaration: type Foo<T> = Bar<T>
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct TypeAliasDecl {
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub declare: bool,
  #[drive(skip)]
  pub name: String,
  pub type_parameters: Option<Vec<Node<TypeParameter>>>,
  pub type_expr: Node<TypeExpr>,
}

/// Enum declaration: enum Color { Red, Green, Blue }
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct EnumDecl {
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub declare: bool,
  #[drive(skip)]
  pub const_: bool,
  #[drive(skip)]
  pub name: String,
  pub members: Vec<Node<EnumMember>>,
}

/// Enum member: Red = 1, Green = "green"
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct EnumMember {
  #[drive(skip)]
  pub name: String,
  pub initializer: Option<Node<Expr>>,
}

/// Namespace declaration: namespace Foo { }
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct NamespaceDecl {
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub declare: bool,
  #[drive(skip)]
  pub name: String,
  pub body: NamespaceBody,
}

/// Namespace body - either a block of statements or nested namespace
#[derive(Debug, Drive, DriveMut, Serialize)]
#[serde(tag = "$t", content = "v")]
pub enum NamespaceBody {
  Block(Vec<Node<Stmt>>),
  Namespace(Box<Node<NamespaceDecl>>),
}

/// Module declaration: module "foo" { }, declare module "foo" { }
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ModuleDecl {
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub declare: bool,
  pub name: ModuleName,
  pub body: Option<Vec<Node<Stmt>>>,
}

/// Module name - either identifier or string literal
#[derive(Debug, Drive, DriveMut, Serialize)]
#[serde(tag = "$t", content = "v")]
pub enum ModuleName {
  Identifier(#[drive(skip)] String),
  String(#[drive(skip)] String),
}

/// Global augmentation: declare global { }
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct GlobalDecl {
  pub body: Vec<Node<Stmt>>,
}

/// Ambient variable declaration: declare var foo: Type
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct AmbientVarDecl {
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub name: String,
  pub type_annotation: Option<Node<TypeExpr>>,
}

/// Ambient function declaration: declare function foo<T>(x: T): void
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct AmbientFunctionDecl {
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub name: String,
  pub type_parameters: Option<Vec<Node<TypeParameter>>>,
  pub parameters: Vec<Node<AmbientFunctionParameter>>,
  pub return_type: Option<Node<TypeExpr>>,
}

/// Ambient function parameter
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct AmbientFunctionParameter {
  #[drive(skip)]
  pub name: String,
  #[drive(skip)]
  pub optional: bool,
  #[drive(skip)]
  pub rest: bool,
  pub type_annotation: Option<Node<TypeExpr>>,
}

/// Ambient class declaration: declare class Foo<T> { }
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct AmbientClassDecl {
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub abstract_: bool,
  #[drive(skip)]
  pub name: String,
  pub type_parameters: Option<Vec<Node<TypeParameter>>>,
  pub extends: Option<Node<TypeExpr>>,
  pub implements: Vec<Node<TypeExpr>>,
  pub members: Vec<Node<TypeMember>>,
}

/// Import type-only: import type { Foo } from "bar"
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ImportTypeDecl {
  pub names: Vec<ImportTypeName>,
  #[drive(skip)]
  pub module: String,
}

/// Import type name
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ImportTypeName {
  #[drive(skip)]
  pub imported: String,
  #[drive(skip)]
  pub local: Option<String>,
}

/// Export type-only: export type { Foo }
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ExportTypeDecl {
  pub names: Vec<ExportTypeName>,
  #[drive(skip)]
  pub module: Option<String>,
}

/// Export type name
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ExportTypeName {
  #[drive(skip)]
  pub local: String,
  #[drive(skip)]
  pub exported: Option<String>,
}

/// Import equals declaration: import id = require("module") or import id = Namespace.Sub
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ImportEqualsDecl {
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub name: String,
  pub rhs: ImportEqualsRhs,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
#[serde(tag = "$t")]
pub enum ImportEqualsRhs {
  Require {
    #[drive(skip)]
    module: String,
  },
  EntityName {
    #[drive(skip)]
    path: Vec<String>,
  },
}

/// Export assignment: export = expression
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ExportAssignmentDecl {
  pub expression: Node<Expr>,
}

/// `export as namespace Foo;`
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ExportAsNamespaceDecl {
  #[drive(skip)]
  pub name: String,
}
