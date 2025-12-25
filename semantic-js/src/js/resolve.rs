use super::{JsSemantics, ScopeId, SymbolId};
use crate::assoc::js::{declared_symbol, scope_id, ResolvedSymbol};
use derive_visitor::{DriveMut, VisitorMut};
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::{ClassExpr, FuncExpr, IdExpr};
use parse_js::ast::func::Func;
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::stmt::decl::{ClassDecl, VarDecl, VarDeclMode, VarDeclarator};
use parse_js::ast::stmt::{BlockStmt, CatchBlock, ForBody, ForInOfLhs};
use parse_js::ast::stx::TopLevel;
use std::collections::HashSet;

#[derive(Debug, Default)]
pub struct JsResolution {
  pub resolved: usize,
  pub unresolved: usize,
}

pub fn resolve(top_level: &mut Node<TopLevel>, sem: &JsSemantics) -> JsResolution {
  let mut visitor = ResolveVisitor::new(sem);
  top_level.drive_mut(&mut visitor);
  JsResolution {
    resolved: visitor.resolved,
    unresolved: visitor.unresolved,
  }
}

type BlockStmtNode = Node<BlockStmt>;
type CatchBlockNode = Node<CatchBlock>;
type ClassDeclNode = Node<ClassDecl>;
type ClassExprNode = Node<ClassExpr>;
type ForBodyNode = Node<ForBody>;
type FuncExprNode = Node<FuncExpr>;
type FuncNode = Node<Func>;
type IdExprNode = Node<IdExpr>;
type IdPatNode = Node<IdPat>;
type VarDeclNode = Node<VarDecl>;
type VarDeclaratorNode = VarDeclarator;

struct TdzFrame {
  scope: ScopeId,
  uninitialized: HashSet<SymbolId>,
}

impl TdzFrame {
  fn new(scope: ScopeId, sem: &JsSemantics) -> Self {
    Self {
      scope,
      uninitialized: sem.scope(scope).tdz_bindings.iter().copied().collect(),
    }
  }

  fn mark_initialized(&mut self, symbol: SymbolId) {
    self.uninitialized.remove(&symbol);
  }

  fn in_tdz(&self, symbol: SymbolId) -> bool {
    self.uninitialized.contains(&symbol)
  }
}

#[derive(VisitorMut)]
#[visitor(
  BlockStmtNode(enter, exit),
  CatchBlockNode(enter, exit),
  ClassDeclNode(enter, exit),
  ClassExprNode(enter, exit),
  ForBodyNode(enter, exit),
  ForInOfLhs(enter, exit),
  FuncExprNode(enter, exit),
  FuncNode(enter, exit),
  IdExprNode(enter),
  IdPatNode(enter),
  VarDeclNode(enter, exit),
  VarDeclaratorNode(enter, exit)
)]
struct ResolveVisitor<'a> {
  sem: &'a JsSemantics,
  resolved: usize,
  unresolved: usize,
  scope_stack: Vec<ScopeId>,
  tdz_stack: Vec<TdzFrame>,
  var_decl_mode_stack: Vec<VarDeclMode>,
  pending_active: Vec<bool>,
  pending_symbols: Vec<Vec<SymbolId>>,
}

impl ResolveVisitor<'_> {
  fn new(sem: &JsSemantics) -> ResolveVisitor<'_> {
    let top_scope = sem.top_scope();
    ResolveVisitor {
      sem,
      resolved: 0,
      unresolved: 0,
      scope_stack: vec![top_scope],
      tdz_stack: vec![TdzFrame::new(top_scope, sem)],
      var_decl_mode_stack: Vec::new(),
      pending_active: Vec::new(),
      pending_symbols: Vec::new(),
    }
  }

  fn push_scope_from_assoc(&mut self, assoc: &NodeAssocData) {
    if let Some(scope) = scope_id(assoc) {
      if Some(scope) != self.scope_stack.last().copied() {
        self.scope_stack.push(scope);
        self.tdz_stack.push(TdzFrame::new(scope, self.sem));
      }
    }
  }

  fn pop_scope_from_assoc(&mut self, assoc: &NodeAssocData) {
    if let Some(scope) = scope_id(assoc) {
      if Some(scope) == self.scope_stack.last().copied() {
        self.scope_stack.pop();
        self.tdz_stack.pop();
      }
    }
  }

  fn symbol_in_tdz(&self, symbol: SymbolId) -> bool {
    let decl_scope = self.sem.symbol(symbol).decl_scope;
    self
      .tdz_stack
      .iter()
      .rev()
      .find(|frame| frame.scope == decl_scope)
      .map_or(false, |frame| frame.in_tdz(symbol))
  }

  fn mark_initialized(&mut self, symbol: SymbolId) {
    let decl_scope = self.sem.symbol(symbol).decl_scope;
    for frame in self.tdz_stack.iter_mut().rev() {
      if frame.scope == decl_scope {
        frame.mark_initialized(symbol);
        break;
      }
    }
  }

  fn is_lexical_symbol(&self, symbol: SymbolId) -> bool {
    let decl_scope = self.sem.symbol(symbol).decl_scope;
    self.sem.scope(decl_scope).tdz_bindings.contains(&symbol)
  }

  fn push_pending(&mut self, active: bool) {
    self.pending_active.push(active);
    if active {
      self.pending_symbols.push(Vec::new());
    }
  }

  fn record_pending(&mut self, symbol: SymbolId) {
    if let Some(true) = self.pending_active.last().copied() {
      if let Some(symbols) = self.pending_symbols.last_mut() {
        symbols.push(symbol);
      }
    }
  }

  fn pop_pending(&mut self) {
    if let Some(active) = self.pending_active.pop() {
      if active {
        if let Some(symbols) = self.pending_symbols.pop() {
          for symbol in symbols {
            self.mark_initialized(symbol);
          }
        }
      }
    }
  }

  fn mark(&mut self, assoc: &mut NodeAssocData, symbol: Option<SymbolId>, in_tdz: bool) {
    assoc.set(ResolvedSymbol { symbol, in_tdz });
    if symbol.is_some() {
      self.resolved += 1;
    } else {
      self.unresolved += 1;
    }
  }

  fn resolve_use(&mut self, assoc: &mut NodeAssocData, name: &str) {
    if let Some(scope) = scope_id(assoc) {
      let symbol = self.sem.resolve_name_in_scope(scope, name);
      let in_tdz = symbol.map_or(false, |sym| self.symbol_in_tdz(sym));
      self.mark(assoc, symbol, in_tdz);
    } else {
      self.mark(assoc, None, false);
    }
  }
}

impl ResolveVisitor<'_> {
  fn enter_block_stmt_node(&mut self, node: &mut BlockStmtNode) {
    self.push_scope_from_assoc(&node.assoc);
  }

  fn exit_block_stmt_node(&mut self, node: &mut BlockStmtNode) {
    self.pop_scope_from_assoc(&node.assoc);
  }

  fn enter_catch_block_node(&mut self, node: &mut CatchBlockNode) {
    self.push_scope_from_assoc(&node.assoc);
  }

  fn exit_catch_block_node(&mut self, node: &mut CatchBlockNode) {
    self.pop_scope_from_assoc(&node.assoc);
  }

  fn enter_class_decl_node(&mut self, node: &mut ClassDeclNode) {
    let has_lexical_name = node
      .stx
      .name
      .as_ref()
      .and_then(|name| declared_symbol(&name.assoc))
      .map(|sym| self.is_lexical_symbol(sym));
    let active = has_lexical_name.unwrap_or(false);
    self.push_pending(active);
    if active {
      if let Some(name) = &mut node.stx.name {
        if let Some(sym) = declared_symbol(&name.assoc) {
          self.record_pending(sym);
        }
      }
    }
    self.push_scope_from_assoc(&node.assoc);
  }

  fn exit_class_decl_node(&mut self, node: &mut ClassDeclNode) {
    self.pop_scope_from_assoc(&node.assoc);
    self.pop_pending();
  }

  fn enter_class_expr_node(&mut self, node: &mut ClassExprNode) {
    self.push_scope_from_assoc(&node.assoc);
  }

  fn exit_class_expr_node(&mut self, node: &mut ClassExprNode) {
    self.pop_scope_from_assoc(&node.assoc);
  }

  fn enter_for_body_node(&mut self, node: &mut ForBodyNode) {
    self.push_scope_from_assoc(&node.assoc);
  }

  fn exit_for_body_node(&mut self, node: &mut ForBodyNode) {
    self.pop_scope_from_assoc(&node.assoc);
  }

  fn enter_for_in_of_lhs(&mut self, node: &mut ForInOfLhs) {
    let active = match node {
      ForInOfLhs::Decl((mode, _)) => matches!(
        mode,
        VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
      ),
      ForInOfLhs::Assign(_) => false,
    };
    self.push_pending(active);
  }

  fn exit_for_in_of_lhs(&mut self, _node: &mut ForInOfLhs) {
    self.pop_pending();
  }

  fn enter_func_expr_node(&mut self, node: &mut FuncExprNode) {
    self.push_scope_from_assoc(&node.assoc);
  }

  fn exit_func_expr_node(&mut self, node: &mut FuncExprNode) {
    self.pop_scope_from_assoc(&node.assoc);
  }

  fn enter_func_node(&mut self, node: &mut FuncNode) {
    self.push_scope_from_assoc(&node.assoc);
  }

  fn exit_func_node(&mut self, node: &mut FuncNode) {
    self.pop_scope_from_assoc(&node.assoc);
  }

  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    self.resolve_use(&mut node.assoc, &node.stx.name);
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    if let Some(declared) = declared_symbol(&node.assoc) {
      let in_tdz = self.symbol_in_tdz(declared);
      self.mark(&mut node.assoc, Some(declared), in_tdz);
      if self.is_lexical_symbol(declared) {
        self.record_pending(declared);
      }
    } else {
      self.resolve_use(&mut node.assoc, &node.stx.name);
    }
  }

  fn enter_var_decl_node(&mut self, node: &mut VarDeclNode) {
    self.var_decl_mode_stack.push(node.stx.mode);
  }

  fn exit_var_decl_node(&mut self, _node: &mut VarDeclNode) {
    self.var_decl_mode_stack.pop();
  }

  fn enter_var_declarator_node(&mut self, _node: &mut VarDeclaratorNode) {
    let active = self
      .var_decl_mode_stack
      .last()
      .copied()
      .map(|mode| {
        matches!(
          mode,
          VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
        )
      })
      .unwrap_or(false);
    self.push_pending(active);
  }

  fn exit_var_declarator_node(&mut self, _node: &mut VarDeclaratorNode) {
    self.pop_pending();
  }
}
