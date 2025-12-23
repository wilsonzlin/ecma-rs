#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct FileId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DefId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExprId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BodyId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TopLevelMode {
  Global,
  Module,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TextRange {
  pub start: u32,
  pub end: u32,
}

impl TextRange {
  pub fn new(start: u32, end: u32) -> Self {
    Self { start, end }
  }

  pub fn contains(&self, offset: u32) -> bool {
    self.start <= offset && offset < self.end
  }

  pub fn len(&self) -> u32 {
    self.end.saturating_sub(self.start)
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
  pub id: DefId,
  pub name: String,
  pub range: TextRange,
}

impl Binding {
  pub fn new(id: DefId, name: impl Into<String>, range: TextRange) -> Self {
    Self {
      id,
      name: name.into(),
      range,
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VarDeclKind {
  Var,
  Let,
  Const,
  Using,
  AwaitUsing,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VarDecl {
  pub decls: Vec<Binding>,
  pub kind: VarDeclKind,
  pub range: TextRange,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionDecl {
  pub id: DefId,
  pub name: String,
  pub params: Vec<Binding>,
  pub body: BodyId,
  pub is_arrow: bool,
  pub range: TextRange,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionExpr {
  pub name: Option<Binding>,
  pub params: Vec<Binding>,
  pub body: BodyId,
  pub is_arrow: bool,
  pub range: TextRange,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassDecl {
  pub id: DefId,
  pub name: Option<String>,
  pub body: BodyId,
  pub range: TextRange,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassExpr {
  pub name: Option<Binding>,
  pub body: BodyId,
  pub range: TextRange,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportDecl {
  pub bindings: Vec<Binding>,
  pub range: TextRange,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CatchBlock {
  pub param: Option<Binding>,
  pub body: Vec<Stmt>,
  pub range: TextRange,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stmt {
  pub range: TextRange,
  pub kind: StmtKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StmtKind {
  Block(Vec<Stmt>),
  Var(VarDecl),
  Function(FunctionDecl),
  Class(ClassDecl),
  Expr(ExprId),
  Import(ImportDecl),
  Catch(CatchBlock),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
  pub statements: Vec<Stmt>,
}

impl Body {
  pub fn new(statements: Vec<Stmt>) -> Self {
    Self { statements }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
  pub range: TextRange,
  pub kind: ExprKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
  Name(String),
  Function(FunctionExpr),
  Class(ClassExpr),
  Call { callee: ExprId, args: Vec<ExprId> },
  Block(Vec<Stmt>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirFile {
  pub file: FileId,
  pub root_body: BodyId,
  pub top_level: TopLevelMode,
  pub expr_ranges: Vec<TextRange>,
}

impl HirFile {
  pub fn new(
    file: FileId,
    top_level: TopLevelMode,
    root_body: BodyId,
    expr_ranges: Vec<TextRange>,
  ) -> Self {
    Self {
      file,
      root_body,
      top_level,
      expr_ranges,
    }
  }

  pub fn expr_range(&self, id: ExprId) -> Option<TextRange> {
    self.expr_ranges.get(id.0 as usize).copied()
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BodyStore {
  bodies: Vec<Body>,
  exprs: Vec<Expr>,
}

impl BodyStore {
  pub fn new() -> Self {
    Self {
      bodies: Vec::new(),
      exprs: Vec::new(),
    }
  }

  pub fn alloc_body(&mut self, body: Body) -> BodyId {
    let id = BodyId(self.bodies.len() as u32);
    self.bodies.push(body);
    id
  }

  pub fn alloc_expr(&mut self, expr: Expr) -> ExprId {
    let id = ExprId(self.exprs.len() as u32);
    self.exprs.push(expr);
    id
  }

  pub fn body(&self, id: BodyId) -> &Body {
    &self.bodies[id.0 as usize]
  }

  pub fn expr(&self, id: ExprId) -> &Expr {
    &self.exprs[id.0 as usize]
  }

  pub fn expr_ranges(&self) -> Vec<TextRange> {
    self.exprs.iter().map(|e| e.range).collect()
  }
}

impl Default for BodyStore {
  fn default() -> Self {
    Self::new()
  }
}
