use super::expr::Expr;
use super::node::Node;
use super::stmt::Stmt;
use super::type_expr::TypeExpr;
use super::type_expr::TypeMember;
use super::type_expr::TypeParameter;
use derive_visitor::Drive;
use derive_visitor::DriveMut;

/// Interface declaration: interface Foo<T> extends Bar { }
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
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
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
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
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
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
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct EnumMember {
  #[drive(skip)]
  pub name: String,
  pub initializer: Option<Node<Expr>>,
}

/// Namespace declaration: namespace Foo { }
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
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
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(tag = "$t", content = "v"))]
#[derive(Debug, Drive, DriveMut)]
pub enum NamespaceBody {
  Block(Vec<Node<Stmt>>),
  Namespace(Box<Node<NamespaceDecl>>),
}

/// Module declaration: module "foo" { }, declare module "foo" { }
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ModuleDecl {
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub declare: bool,
  #[drive(skip)]
  #[cfg_attr(feature = "serde", serde(skip_serializing, skip_deserializing))]
  pub name_loc: crate::loc::Loc,
  pub name: ModuleName,
  pub body: Option<Vec<Node<Stmt>>>,
}

/// Module name - either identifier or string literal
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(tag = "$t", content = "v"))]
#[derive(Debug, Drive, DriveMut)]
pub enum ModuleName {
  Identifier(#[drive(skip)] String),
  String(#[drive(skip)] String),
}

/// Global augmentation: declare global { }
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct GlobalDecl {
  pub body: Vec<Node<Stmt>>,
}

/// Ambient variable declaration: declare var foo: Type
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct AmbientVarDecl {
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub name: String,
  pub type_annotation: Option<Node<TypeExpr>>,
}

/// Ambient function declaration: declare function foo<T>(x: T): void
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
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
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
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
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
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
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ImportTypeDecl {
  pub names: Vec<ImportTypeName>,
  #[drive(skip)]
  pub module: String,
}

/// Import type name
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ImportTypeName {
  #[drive(skip)]
  pub imported: String,
  #[drive(skip)]
  pub local: Option<String>,
}

/// Export type-only: export type { Foo }
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ExportTypeDecl {
  pub names: Vec<ExportTypeName>,
  #[drive(skip)]
  pub module: Option<String>,
}

/// Export type name
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ExportTypeName {
  #[drive(skip)]
  pub local: String,
  #[drive(skip)]
  pub exported: Option<String>,
}

/// Import equals declaration: import id = require("module") or import id = Namespace.Sub
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ImportEqualsDecl {
  #[drive(skip)]
  pub export: bool,
  #[drive(skip)]
  pub type_only: bool,
  #[drive(skip)]
  pub name: String,
  pub rhs: ImportEqualsRhs,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(tag = "$t"))]
#[derive(Debug, Drive, DriveMut)]
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
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ExportAssignmentDecl {
  pub expression: Node<Expr>,
}

/// `export as namespace Foo;`
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ExportAsNamespaceDecl {
  #[drive(skip)]
  pub name: String,
}
