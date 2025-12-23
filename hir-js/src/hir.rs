use crate::ids::BodyId;
use crate::ids::DefId;
use crate::ids::DefPath;
use crate::ids::ExprId;
use crate::ids::NameId;
use crate::ids::PatId;
use crate::ids::StmtId;
use crate::intern::NameInterner;
use crate::span_map::SpanMap;
use diagnostics::FileId;
use diagnostics::TextRange;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq)]
pub struct HirFile {
  pub file: FileId,
  pub items: Vec<DefId>,
  pub bodies: Vec<BodyId>,
  pub span_map: SpanMap,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DefData {
  pub id: DefId,
  pub path: DefPath,
  pub span: TextRange,
  pub body: Option<BodyId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LowerResult {
  pub hir: Arc<HirFile>,
  pub defs: Vec<DefData>,
  pub bodies: Vec<Arc<Body>>, // BodyId indexes into this vec.
  pub names: Arc<NameInterner>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Body {
  pub owner: DefId,
  pub kind: BodyKind,
  pub exprs: Vec<Expr>,
  pub stmts: Vec<Stmt>,
  pub pats: Vec<Pat>,
  /// Reserved for the checker; filled in by later phases.
  pub expr_types: Option<Vec<()>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BodyKind {
  TopLevel,
  Function,
  Class,
  Initializer,
  Unknown,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
  pub span: TextRange,
  pub kind: ExprKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
  Missing,
  Ident(NameId),
  Literal,
  Binary {
    left: ExprId,
    right: ExprId,
  },
  Call {
    callee: ExprId,
    args: Vec<ExprId>,
    optional: bool,
  },
  Member {
    object: ExprId,
    property: NameId,
    optional: bool,
  },
  Conditional {
    test: ExprId,
    consequent: ExprId,
    alternate: ExprId,
  },
  Assignment {
    target: PatId,
    value: ExprId,
  },
  FunctionExpr {
    body: BodyId,
  },
  ClassExpr {
    body: BodyId,
    name: Option<NameId>,
  },
  This,
  Super,
  Await {
    expr: ExprId,
  },
  Object,
  Array,
  Other,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pat {
  pub span: TextRange,
  pub kind: PatKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PatKind {
  Ident(NameId),
  Rest(Box<PatId>),
  Destructure(Vec<PatId>),
  AssignTarget(ExprId),
  Unknown,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Stmt {
  pub span: TextRange,
  pub kind: StmtKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StmtKind {
  Expr(ExprId),
  Decl(DefId),
  Return(Option<ExprId>),
  Block(Vec<StmtId>),
  Empty,
  Other,
}

impl HirFile {
  pub fn new(file: FileId, items: Vec<DefId>, bodies: Vec<BodyId>, span_map: SpanMap) -> Self {
    Self {
      file,
      items,
      bodies,
      span_map,
    }
  }
}
