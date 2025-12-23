use crate::ids::BodyId;
use crate::ids::ExprId;
use crate::ids::PatId;
use crate::ids::StmtId;
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;
use symbol_js::symbol::Symbol;

#[derive(Debug, Clone)]
pub struct HirProgram {
  pub top_level_body: BodyId,
  pub bodies: Vec<Body>,
  pub exprs: Vec<Expr>,
  pub stmts: Vec<Stmt>,
  pub pats: Vec<Pat>,
}

impl HirProgram {
  pub fn top_level_body(&self) -> BodyId {
    self.top_level_body
  }

  pub fn body(&self, id: BodyId) -> &Body {
    self.bodies.get(id.index()).expect("BodyId did not exist")
  }

  pub fn expr(&self, id: ExprId) -> &Expr {
    self.exprs.get(id.index()).expect("ExprId did not exist")
  }

  pub fn stmt(&self, id: StmtId) -> &Stmt {
    self.stmts.get(id.index()).expect("StmtId did not exist")
  }

  pub fn pat(&self, id: PatId) -> &Pat {
    self.pats.get(id.index()).expect("PatId did not exist")
  }

  pub fn loc_body(&self, id: BodyId) -> Loc {
    self.body(id).loc
  }

  pub fn loc_expr(&self, id: ExprId) -> Loc {
    self.expr(id).loc
  }

  pub fn loc_stmt(&self, id: StmtId) -> Loc {
    self.stmt(id).loc
  }

  pub fn loc_pat(&self, id: PatId) -> Loc {
    self.pat(id).loc
  }
}

#[derive(Debug, Clone)]
pub struct Body {
  pub loc: Loc,
  pub root: BodyRoot,
}

#[derive(Debug, Clone)]
pub enum BodyRoot {
  Block(Vec<StmtId>),
  Expr(ExprId),
}

#[derive(Debug, Clone)]
pub struct Expr {
  pub loc: Loc,
  pub kind: ExprKind,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
  ArrowFunc(FuncExpr),
  Binary {
    op: OperatorName,
    left: ExprId,
    right: ExprId,
  },
  Call {
    optional_chaining: bool,
    callee: ExprId,
    args: Vec<ExprId>,
  },
  Member {
    optional_chaining: bool,
    object: ExprId,
    property: String,
  },
  ComputedMember {
    optional_chaining: bool,
    object: ExprId,
    member: ExprId,
  },
  Cond {
    test: ExprId,
    consequent: ExprId,
    alternate: ExprId,
  },
  Unary {
    op: OperatorName,
    arg: ExprId,
  },
  UnaryPostfix {
    op: OperatorName,
    arg: ExprId,
  },
  Id(Ident),
  LitBool(bool),
  LitNum(JsNumber),
  LitStr(String),
}

#[derive(Debug, Clone)]
pub struct FuncExpr {
  pub params: Vec<Param>,
  pub body: BodyId,
  pub async_: bool,
  pub generator: bool,
}

#[derive(Debug, Clone)]
pub struct Param {
  pub loc: Loc,
  pub pat: PatId,
  pub default: Option<ExprId>,
  pub rest: bool,
}

#[derive(Debug, Clone)]
pub struct Stmt {
  pub loc: Loc,
  pub kind: StmtKind,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
  Block(Vec<StmtId>),
  Break {
    label: Option<String>,
  },
  Expr {
    expr: ExprId,
  },
  ForTriple {
    init: ForInit,
    cond: Option<ExprId>,
    post: Option<ExprId>,
    body: Vec<StmtId>,
  },
  If {
    test: ExprId,
    consequent: StmtId,
    alternate: Option<StmtId>,
  },
  VarDecl(VarDecl),
  While {
    cond: ExprId,
    body: StmtId,
  },
}

#[derive(Debug, Clone)]
pub enum ForInit {
  None,
  Expr(ExprId),
  VarDecl(StmtId),
}

#[derive(Debug, Clone)]
pub struct VarDecl {
  pub export: bool,
  pub mode: VarDeclMode,
  pub declarators: Vec<VarDeclarator>,
}

#[derive(Debug, Clone)]
pub struct VarDeclarator {
  pub pat: PatId,
  pub init: Option<ExprId>,
  pub has_type_annotation: bool,
}

#[derive(Debug, Clone)]
pub struct Pat {
  pub loc: Loc,
  pub kind: PatKind,
}

#[derive(Debug, Clone)]
pub enum PatKind {
  Id(Ident),
  Arr {
    elements: Vec<Option<ArrPatElem>>,
    rest: Option<PatId>,
  },
  Obj {
    properties: Vec<ObjPatProp>,
    rest: Option<PatId>,
  },
  AssignTarget(ExprId),
}

#[derive(Debug, Clone)]
pub struct ArrPatElem {
  pub target: PatId,
  pub default_value: Option<ExprId>,
}

#[derive(Debug, Clone)]
pub struct ObjPatProp {
  pub key: ObjPatKey,
  pub target: PatId,
  pub shorthand: bool,
  pub default_value: Option<ExprId>,
}

#[derive(Debug, Clone)]
pub enum ObjPatKey {
  Direct(String),
  Computed(ExprId),
}

#[derive(Debug, Clone)]
pub struct Ident {
  pub name: String,
  pub symbol: Option<Symbol>,
}
