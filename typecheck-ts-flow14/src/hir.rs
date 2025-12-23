use crate::types::Type;
use std::fmt;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExprId(pub usize);

impl ExprId {
  pub fn idx(self) -> usize {
    self.0
  }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StmtId(pub usize);

impl StmtId {
  pub fn idx(self) -> usize {
    self.0
  }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VarId(pub usize);

impl VarId {
  pub fn idx(self) -> usize {
    self.0
  }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunctionId(pub usize);

impl FunctionId {
  pub fn idx(self) -> usize {
    self.0
  }
}

#[derive(Clone, Debug)]
pub struct VarInfo {
  pub name: String,
  pub declared_type: Type,
}

#[derive(Clone, Debug)]
pub struct FunctionInfo {
  pub name: String,
  pub param: VarId,
  pub ret: FunctionReturn,
}

#[derive(Clone, Debug)]
pub enum FunctionReturn {
  /// Regular return type.
  Value(Type),
  /// Returns a boolean type guard.
  TypeGuard { narrows: VarId, to: Type },
  /// Assertion functions with `asserts x is Foo` style predicates.
  Asserts { narrows: VarId, to: Type },
  /// Assertion without predicate; narrows to truthy.
  AssertsTruthy { narrows: VarId },
}

#[derive(Clone, Debug)]
pub struct Body {
  pub vars: Vec<VarInfo>,
  pub exprs: Vec<Expr>,
  pub stmts: Vec<Stmt>,
  pub root: Vec<StmtId>,
  pub functions: Vec<FunctionInfo>,
}

impl Body {
  pub fn new() -> Self {
    Self {
      vars: Vec::new(),
      exprs: Vec::new(),
      stmts: Vec::new(),
      root: Vec::new(),
      functions: Vec::new(),
    }
  }

  pub fn add_var(&mut self, name: impl Into<String>, ty: Type) -> VarId {
    let id = VarId(self.vars.len());
    self.vars.push(VarInfo {
      name: name.into(),
      declared_type: ty,
    });
    id
  }

  pub fn add_function(
    &mut self,
    name: impl Into<String>,
    param: VarId,
    ret: FunctionReturn,
  ) -> FunctionId {
    let id = FunctionId(self.functions.len());
    self.functions.push(FunctionInfo {
      name: name.into(),
      param,
      ret,
    });
    id
  }

  pub fn alloc_expr(&mut self, expr: Expr) -> ExprId {
    let id = ExprId(self.exprs.len());
    self.exprs.push(expr);
    id
  }

  pub fn alloc_stmt(&mut self, stmt: StmtKind) -> StmtId {
    let id = StmtId(self.stmts.len());
    self.stmts.push(Stmt { id, kind: stmt });
    id
  }

  pub fn push_root(&mut self, stmt: StmtId) {
    self.root.push(stmt);
  }
}

#[derive(Clone, Debug)]
pub struct Stmt {
  pub id: StmtId,
  pub kind: StmtKind,
}

#[derive(Clone, Debug)]
pub enum StmtKind {
  Var {
    id: VarId,
    init: Option<ExprId>,
  },
  Expr(ExprId),
  Block(Vec<StmtId>),
  If {
    cond: ExprId,
    then_branch: Vec<StmtId>,
    else_branch: Vec<StmtId>,
  },
  While {
    cond: ExprId,
    body: Vec<StmtId>,
  },
  Return(Option<ExprId>),
  Try {
    try_block: Vec<StmtId>,
    catch: Option<CatchBlock>,
    finally_block: Vec<StmtId>,
  },
}

#[derive(Clone, Debug)]
pub struct CatchBlock {
  pub param: Option<VarId>,
  pub body: Vec<StmtId>,
}

#[derive(Clone, Debug)]
pub enum Expr {
  Var(VarId),
  Literal(Literal),
  Unary(UnaryOp, ExprId),
  Binary(BinaryOp, ExprId, ExprId),
  Logical(LogicalOp, ExprId, ExprId),
  Conditional {
    cond: ExprId,
    when_true: ExprId,
    when_false: ExprId,
  },
  Call {
    callee: FunctionId,
    args: Vec<ExprId>,
  },
  Property {
    obj: ExprId,
    name: String,
  },
  In {
    property: String,
    obj: ExprId,
  },
}

#[derive(Clone, Debug)]
pub enum Literal {
  Boolean(bool),
  Number(i64),
  String(String),
  Null,
  Undefined,
}

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub enum UnaryOp {
  Not,
  Typeof,
}

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub enum BinaryOp {
  Equals,
  StrictEquals,
  InstanceOf,
}

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub enum LogicalOp {
  And,
  Or,
}

impl fmt::Display for ExprId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "%{}", self.0)
  }
}
