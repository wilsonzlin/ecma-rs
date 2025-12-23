use derive_visitor::Drive;
use derive_visitor::DriveMut;
use derive_visitor::VisitorMut;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::ArrowFuncExpr;
use parse_js::ast::expr::Expr;
use parse_js::ast::func::Func;
use parse_js::ast::func::FuncBody;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use std::collections::HashMap;
use std::fmt;

/// Identifier for a lowered statement.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct StmtId(pub u32);

impl StmtId {
  pub fn index(self) -> usize {
    self.0 as usize
  }
}

/// Identifier for a lowered expression.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExprId(pub u32);

impl ExprId {
  pub fn index(self) -> usize {
    self.0 as usize
  }
}

/// Identifier for a lowered pattern.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PatId(pub u32);

impl PatId {
  pub fn index(self) -> usize {
    self.0 as usize
  }
}

/// Identifier for a lowered function/arrow body.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BodyId(pub u32);

impl BodyId {
  pub fn index(self) -> usize {
    self.0 as usize
  }
}

#[derive(Debug, Default)]
pub struct HirProgram {
  /// Top-level statements in source order.
  pub top_level: Vec<StmtId>,
  pub stmts: Vec<HirStmt>,
  pub exprs: Vec<HirExpr>,
  pub pats: Vec<HirPat>,
  pub bodies: Vec<HirBody>,
}

#[derive(Debug)]
pub struct HirStmt {
  pub span: Loc,
}

#[derive(Debug)]
pub struct HirExpr {
  pub span: Loc,
}

#[derive(Debug)]
pub struct HirPat {
  pub span: Loc,
}

#[derive(Debug)]
pub struct HirBody {
  pub span: Loc,
  pub arrow: bool,
  pub async_: bool,
  pub generator: bool,
  pub kind: HirBodyKind,
}

#[derive(Debug)]
pub enum HirBodyKind {
  Block { statements: Vec<StmtId> },
  Expr { expr: ExprId },
}

/// Errors that can occur while lowering the AST into HIR.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LowerError {
  MissingStmtId { loc: Loc },
  MissingExprId { loc: Loc },
  MissingPatId { loc: Loc },
}

impl fmt::Display for LowerError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      LowerError::MissingStmtId { .. } => write!(f, "missing statement id during lowering"),
      LowerError::MissingExprId { .. } => write!(f, "missing expression id during lowering"),
      LowerError::MissingPatId { .. } => write!(f, "missing pattern id during lowering"),
    }
  }
}

impl std::error::Error for LowerError {}

/// Lower the provided AST into HIR without mutating `NodeAssocData`.
pub fn lower_top_level(top: &mut Node<TopLevel>) -> Result<HirProgram, LowerError> {
  lower_top_level_internal(top, false)
}

/// Lower the provided AST into HIR while attaching the produced IDs back onto each lowered node.
///
/// Existing associated data entries for these IDs are overwritten on repeated lowering, so callers
/// can deterministically re-run lowering on the same AST without manually clearing `NodeAssocData`.
pub fn lower_top_level_and_attach_ids(top: &mut Node<TopLevel>) -> Result<HirProgram, LowerError> {
  lower_top_level_internal(top, true)
}

fn lower_top_level_internal(
  top: &mut Node<TopLevel>,
  attach_ids: bool,
) -> Result<HirProgram, LowerError> {
  let mut visitor = LowerVisitor::new(attach_ids);
  top.drive_mut(&mut visitor);
  visitor.finish(top)
}

type StmtNode = Node<Stmt>;
type ExprNode = Node<Expr>;
type PatNode = Node<Pat>;
type FuncNode = Node<Func>;
type ArrowFuncExprNode = Node<ArrowFuncExpr>;

#[derive(VisitorMut)]
#[visitor(
  StmtNode(enter),
  ExprNode(enter),
  PatNode(enter),
  FuncNode(exit),
  ArrowFuncExprNode(exit)
)]
struct LowerVisitor {
  attach_ids: bool,
  program: HirProgram,
  stmt_lookup: HashMap<usize, StmtId>,
  expr_lookup: HashMap<usize, ExprId>,
  pat_lookup: HashMap<usize, PatId>,
  func_body_lookup: HashMap<usize, BodyId>,
  error: Option<LowerError>,
}

impl LowerVisitor {
  fn new(attach_ids: bool) -> Self {
    Self {
      attach_ids,
      program: HirProgram::default(),
      stmt_lookup: HashMap::new(),
      expr_lookup: HashMap::new(),
      pat_lookup: HashMap::new(),
      func_body_lookup: HashMap::new(),
      error: None,
    }
  }

  fn finish(mut self, top: &Node<TopLevel>) -> Result<HirProgram, LowerError> {
    if let Some(err) = self.error {
      return Err(err);
    }

    self.program.top_level = top
      .stx
      .body
      .iter()
      .map(|stmt| self.get_stmt_id(stmt))
      .collect::<Result<_, _>>()?;

    Ok(self.program)
  }

  #[inline]
  fn ptr<T: Drive + DriveMut>(node: &Node<T>) -> usize {
    node as *const Node<T> as usize
  }

  fn record_stmt(&mut self, node: &mut StmtNode) {
    if self.error.is_some() {
      return;
    }
    let id = StmtId(self.program.stmts.len() as u32);
    self.program.stmts.push(HirStmt { span: node.loc });
    self.stmt_lookup.insert(Self::ptr(node), id);
    if self.attach_ids {
      node.assoc.set(id);
    }
  }

  fn record_expr(&mut self, node: &mut ExprNode) {
    if self.error.is_some() {
      return;
    }
    let id = ExprId(self.program.exprs.len() as u32);
    self.program.exprs.push(HirExpr { span: node.loc });
    self.expr_lookup.insert(Self::ptr(node), id);
    if self.attach_ids {
      node.assoc.set(id);
    }
  }

  fn record_pat(&mut self, node: &mut PatNode) {
    if self.error.is_some() {
      return;
    }
    let id = PatId(self.program.pats.len() as u32);
    self.program.pats.push(HirPat { span: node.loc });
    self.pat_lookup.insert(Self::ptr(node), id);
    if self.attach_ids {
      node.assoc.set(id);
    }
  }

  fn get_stmt_id(&self, node: &StmtNode) -> Result<StmtId, LowerError> {
    self
      .stmt_lookup
      .get(&Self::ptr(node))
      .copied()
      .ok_or(LowerError::MissingStmtId { loc: node.loc })
  }

  fn get_expr_id(&self, node: &ExprNode) -> Result<ExprId, LowerError> {
    self
      .expr_lookup
      .get(&Self::ptr(node))
      .copied()
      .ok_or(LowerError::MissingExprId { loc: node.loc })
  }

  fn lower_func_body(&mut self, func: &mut FuncNode) {
    if self.error.is_some() {
      return;
    }

    let Some(body) = &func.stx.body else {
      return;
    };

    let body_id = BodyId(self.program.bodies.len() as u32);
    let kind = match body {
      FuncBody::Block(stmts) => {
        let mut stmt_ids = Vec::with_capacity(stmts.len());
        for stmt in stmts.iter() {
          match self.get_stmt_id(stmt) {
            Ok(id) => stmt_ids.push(id),
            Err(err) => {
              self.error = Some(err);
              return;
            }
          }
        }
        HirBodyKind::Block {
          statements: stmt_ids,
        }
      }
      FuncBody::Expression(expr) => match self.get_expr_id(expr) {
        Ok(id) => HirBodyKind::Expr { expr: id },
        Err(err) => {
          self.error = Some(err);
          return;
        }
      },
    };

    self.program.bodies.push(HirBody {
      span: func.loc,
      arrow: func.stx.arrow,
      async_: func.stx.async_,
      generator: func.stx.generator,
      kind,
    });
    self.func_body_lookup.insert(Self::ptr(func), body_id);

    if self.attach_ids {
      func.assoc.set(body_id);
    }
  }
}

impl LowerVisitor {
  fn attach_arrow_body_id(&mut self, node: &mut ArrowFuncExprNode) {
    if !self.attach_ids {
      return;
    }

    if let Some(body_id) = self.func_body_lookup.get(&Self::ptr(&node.stx.func)) {
      node.assoc.set(*body_id);
    }
  }
}

impl LowerVisitor {
  fn enter_stmt_node(&mut self, node: &mut StmtNode) {
    self.record_stmt(node);
  }

  fn enter_expr_node(&mut self, node: &mut ExprNode) {
    self.record_expr(node);
  }

  fn enter_pat_node(&mut self, node: &mut PatNode) {
    self.record_pat(node);
  }

  fn exit_func_node(&mut self, node: &mut FuncNode) {
    self.lower_func_body(node);
  }

  fn exit_arrow_func_expr_node(&mut self, node: &mut ArrowFuncExprNode) {
    self.attach_arrow_body_id(node);
  }
}
