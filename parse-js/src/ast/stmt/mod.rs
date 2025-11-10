pub mod decl;

use decl::{ClassDecl, FuncDecl, PatDecl, VarDecl, VarDeclMode};
use derive_more::derive::{From, TryInto};
use derive_visitor::{Drive, DriveMut};
use serde::{Deserialize, Serialize};

use super::{expr::{pat::Pat, Expr}, import_export::{ExportNames, ImportNames}, node::Node, stx::TopLevel, ts_stmt::*, type_expr::TypeExpr};

// We must wrap each variant with Node<T> as otherwise we won't be able to visit Node<T> instead of just T.
#[derive(Debug, Drive, DriveMut, From, Serialize, TryInto)]
#[serde(tag = "$t")]
pub enum Stmt {
  Block(Node<BlockStmt>),
  Break(Node<BreakStmt>),
  Continue(Node<ContinueStmt>),
  Debugger(Node<DebuggerStmt>),
  DoWhile(Node<DoWhileStmt>),
  Empty(Node<EmptyStmt>),
  ExportDefaultExpr(Node<ExportDefaultExprStmt>),
  ExportList(Node<ExportListStmt>),
  Expr(Node<ExprStmt>),
  ForIn(Node<ForInStmt>),
  ForOf(Node<ForOfStmt>),
  ForTriple(Node<ForTripleStmt>),
  If(Node<IfStmt>),
  Import(Node<ImportStmt>),
  Label(Node<LabelStmt>),
  Return(Node<ReturnStmt>),
  Switch(Node<SwitchStmt>),
  Throw(Node<ThrowStmt>),
  Try(Node<TryStmt>),
  While(Node<WhileStmt>),
  With(Node<WithStmt>),

  ClassDecl(Node<ClassDecl>),
  FunctionDecl(Node<FuncDecl>),
  VarDecl(Node<VarDecl>),

  // TypeScript statements
  InterfaceDecl(Node<InterfaceDecl>),
  TypeAliasDecl(Node<TypeAliasDecl>),
  EnumDecl(Node<EnumDecl>),
  NamespaceDecl(Node<NamespaceDecl>),
  ModuleDecl(Node<ModuleDecl>),
  GlobalDecl(Node<GlobalDecl>),
  AmbientVarDecl(Node<AmbientVarDecl>),
  AmbientFunctionDecl(Node<AmbientFunctionDecl>),
  AmbientClassDecl(Node<AmbientClassDecl>),
  ImportTypeDecl(Node<ImportTypeDecl>),
  ExportTypeDecl(Node<ExportTypeDecl>),
  ImportEqualsDecl(Node<ImportEqualsDecl>),
}




#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct CatchBlock {
  pub parameter: Option<Node<PatDecl>>,
  pub body: Vec<Node<Stmt>>, // We don't want to use BlockStmt as the new block scope starts with the parameter, not the braces. This differentiation ensures BlockStmt specifically means a new scope, helpful for downstream usages. See also: FunctionBody.
}

// Similar purpose to CatchBlock and FunctionBody. (The scope for a `for` statement starts before the braces, so don't mix with BlockStmt.)
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ForBody {
  pub body: Vec<Node<Stmt>>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct SwitchBranch {
  // If None, it's `default`.
  pub case: Option<Node<Expr>>,
  pub body: Vec<Node<Stmt>>,
}

  // Statements.

#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct BlockStmt {
   pub body: Vec<Node<Stmt>>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct BreakStmt {
    #[drive(skip)]
    pub label: Option<String>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct ContinueStmt {
    #[drive(skip)]
    pub label: Option<String>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct DebuggerStmt {}


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct DoWhileStmt {
    pub condition: Node<Expr>,
    pub body: Node<Stmt>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct EmptyStmt {}


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct ExportDefaultExprStmt {
    pub expression: Node<Expr>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct ExportListStmt {
    #[drive(skip)]
    pub type_only: bool, // TypeScript: export type
    pub names: ExportNames,
    #[drive(skip)]
    pub from: Option<String>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct ExprStmt {
    pub expr: Node<Expr>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct IfStmt {
    pub test: Node<Expr>,
    pub consequent: Node<Stmt>,
    pub alternate: Option<Node<Stmt>>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct ImportStmt {
    #[drive(skip)]
    pub type_only: bool, // TypeScript: import type
    // PatDecl always contains IdPat.
    pub default: Option<Node<PatDecl>>,
    pub names: Option<ImportNames>,
    #[drive(skip)]
    pub module: String,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ForTripleStmt {
  pub init: ForTripleStmtInit,
  pub cond: Option<Node<Expr>>,
  pub post: Option<Node<Expr>>,
  pub body: Node<ForBody>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub enum ForTripleStmtInit {
  None,
  Expr(Node<Expr>),
  Decl(Node<VarDecl>),
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub enum ForInOfLhs {
  // Assignment target.
  Assign(Node<Pat>),
  // Scoped variable declaration.
  Decl((VarDeclMode, Node<PatDecl>)),
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ForInStmt {
  pub lhs: ForInOfLhs,
  pub rhs: Node<Expr>,
  pub body: Node<ForBody>,
}


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct ForOfStmt {
    #[drive(skip)]
    pub await_: bool,
    pub lhs: ForInOfLhs,
    pub rhs: Node<Expr>,
    pub body: Node<ForBody>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct LabelStmt {
    #[drive(skip)]
    pub name: String,
    pub statement: Node<Stmt>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct ReturnStmt {
    pub value: Option<Node<Expr>>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct SwitchStmt {
    pub test: Node<Expr>,
    pub branches: Vec<Node<SwitchBranch>>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct ThrowStmt {
    pub value: Node<Expr>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct TryStmt {
    pub wrapped: Node<BlockStmt>,
    // One of these must be present.
    pub catch: Option<Node<CatchBlock>>,
    pub finally: Option<Node<BlockStmt>>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct WhileStmt {
    pub condition: Node<Expr>,
    pub body: Node<Stmt>,
  }


#[derive(Debug, Drive, DriveMut, Serialize)]
  pub struct WithStmt {
    pub object: Node<Expr>,
    pub body: Node<Stmt>,
  }
