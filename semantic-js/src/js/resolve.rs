use super::{JsSemantics, ScopeId, SymbolId};
use crate::assoc::js::{declared_symbol, scope_id, ResolvedSymbol};
use derive_visitor::{DriveMut, VisitorMut};
use diagnostics::{Diagnostic, FileId, Span, TextRange};
use parse_js::ast::class_or_object::ClassMember;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::{ClassExpr, FuncExpr, IdExpr};
use parse_js::ast::func::{Func, FuncBody};
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
  let mut visitor = ResolveVisitor::new(sem, None);
  top_level.drive_mut(&mut visitor);
  JsResolution {
    resolved: visitor.resolved,
    unresolved: visitor.unresolved,
  }
}

pub(crate) fn resolve_with_diagnostics(
  top_level: &mut Node<TopLevel>,
  sem: &JsSemantics,
  file: FileId,
) -> (JsResolution, Vec<Diagnostic>) {
  let mut visitor = ResolveVisitor::new(sem, Some(file));
  top_level.drive_mut(&mut visitor);
  (
    JsResolution {
      resolved: visitor.resolved,
      unresolved: visitor.unresolved,
    },
    visitor.diagnostics,
  )
}

type BlockStmtNode = Node<BlockStmt>;
type CatchBlockNode = Node<CatchBlock>;
type ClassMemberNode = Node<ClassMember>;
type ClassDeclNode = Node<ClassDecl>;
type ClassExprNode = Node<ClassExpr>;
type ForBodyNode = Node<ForBody>;
type FuncExprNode = Node<FuncExpr>;
type FuncNode = Node<Func>;
type FuncBodyNode = FuncBody;
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
  ClassMemberNode(enter),
  ForBodyNode(enter, exit),
  ForInOfLhs(enter, exit),
  FuncExprNode(enter, exit),
  FuncBodyNode(enter),
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
  file: Option<FileId>,
  diagnostics: Vec<Diagnostic>,
  scope_stack: Vec<ScopeId>,
  tdz_stack: Vec<TdzFrame>,
  var_decl_mode_stack: Vec<VarDeclMode>,
  pending_active: Vec<bool>,
  pending_symbols: Vec<Vec<SymbolId>>,
  class_name_stack: Vec<Option<SymbolId>>,
  in_param_list: Vec<bool>,
  func_scope_stack: Vec<ScopeId>,
}

impl ResolveVisitor<'_> {
  fn new(sem: &JsSemantics, file: Option<FileId>) -> ResolveVisitor<'_> {
    let top_scope = sem.top_scope();
    ResolveVisitor {
      sem,
      resolved: 0,
      unresolved: 0,
      file,
      diagnostics: Vec::new(),
      scope_stack: vec![top_scope],
      tdz_stack: vec![TdzFrame::new(top_scope, sem)],
      var_decl_mode_stack: Vec::new(),
      pending_active: Vec::new(),
      pending_symbols: Vec::new(),
      class_name_stack: Vec::new(),
      in_param_list: Vec::new(),
      func_scope_stack: Vec::new(),
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

  fn resolve_use(&mut self, assoc: &mut NodeAssocData, name: &str, range: TextRange) {
    if let Some(scope) = scope_id(assoc) {
      let symbol = self.resolve_name_for_use(scope, name);
      let in_tdz = symbol.map_or(false, |sym| self.symbol_in_tdz(sym));
      let should_report_tdz = self.file.is_some() && in_tdz && symbol.is_some();
      self.mark(assoc, symbol, in_tdz);
      if should_report_tdz {
        let file = self.file.expect("file id present when reporting diagnostics");
        self.diagnostics.push(Diagnostic::error(
          "BIND0003",
          format!("Cannot access `{name}` before initialization"),
          Span::new(file, range),
        ));
      }
    } else {
      self.mark(assoc, None, false);
    }
  }

  fn resolve_name_for_use(&self, scope: ScopeId, name: &str) -> Option<SymbolId> {
    if !self.in_param_list.last().copied().unwrap_or(false) {
      return self.sem.resolve_name_in_scope(scope, name);
    }

    let Some(name_id) = self.sem.name_id(name) else {
      return None;
    };
    let func_scope = self.func_scope_stack.last().copied().unwrap_or(scope);

    let mut current = Some(scope);
    while let Some(scope_id) = current {
      let scope_data = self.sem.scope(scope_id);
      if let Some(symbol) = scope_data.get(name_id) {
        // Function parameter initializer expressions are evaluated before the
        // function body's lexical declarations become visible. If name
        // resolution finds a lexical binding in the function scope, skip it and
        // continue searching outer scopes instead.
        if scope_id == func_scope && self.is_lexical_symbol(symbol) {
          current = scope_data.parent;
          continue;
        }
        return Some(symbol);
      }
      current = scope_data.parent;
    }

    None
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
    let symbol = node
      .stx
      .name
      .as_ref()
      .and_then(|name| declared_symbol(&name.assoc));
    let active = symbol.map(|sym| self.is_lexical_symbol(sym)).unwrap_or(false);
    self.push_pending(active);
    if active {
      if let Some(name) = &mut node.stx.name {
        if let Some(sym) = declared_symbol(&name.assoc) {
          self.record_pending(sym);
        }
      }
    }
    self.class_name_stack.push(if active { symbol } else { None });
    self.push_scope_from_assoc(&node.assoc);
  }

  fn exit_class_decl_node(&mut self, node: &mut ClassDeclNode) {
    self.pop_scope_from_assoc(&node.assoc);
    self.pop_pending();
    self.class_name_stack.pop();
  }

  fn enter_class_expr_node(&mut self, node: &mut ClassExprNode) {
    let symbol = node
      .stx
      .name
      .as_ref()
      .and_then(|name| declared_symbol(&name.assoc));
    let active = symbol.map(|sym| self.is_lexical_symbol(sym)).unwrap_or(false);
    self.push_pending(active);
    if active {
      if let Some(name) = &mut node.stx.name {
        if let Some(sym) = declared_symbol(&name.assoc) {
          self.record_pending(sym);
        }
      }
    }
    self.class_name_stack.push(if active { symbol } else { None });
    self.push_scope_from_assoc(&node.assoc);
  }

  fn exit_class_expr_node(&mut self, node: &mut ClassExprNode) {
    self.pop_scope_from_assoc(&node.assoc);
    self.pop_pending();
    self.class_name_stack.pop();
  }

  fn enter_class_member_node(&mut self, _node: &mut ClassMemberNode) {
    let symbol = self
      .class_name_stack
      .last_mut()
      .and_then(|entry| entry.take());
    if let Some(symbol) = symbol {
      // Class bindings are in TDZ during the `extends` clause, but initialized
      // before evaluating class body elements such as static fields/blocks.
      self.mark_initialized(symbol);
    }
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
    if let Some(scope) = scope_id(&node.assoc) {
      self.func_scope_stack.push(scope);
    }
    self.in_param_list.push(true);
    self.push_scope_from_assoc(&node.assoc);
  }

  fn exit_func_node(&mut self, node: &mut FuncNode) {
    self.pop_scope_from_assoc(&node.assoc);
    self.in_param_list.pop();
    self.func_scope_stack.pop();
  }

  fn enter_func_body_node(&mut self, _node: &mut FuncBodyNode) {
    if let Some(flag) = self.in_param_list.last_mut() {
      *flag = false;
    }
  }

  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    let start = node.loc.start_u32();
    let end = start.saturating_add(node.stx.name.len() as u32);
    self.resolve_use(
      &mut node.assoc,
      &node.stx.name,
      TextRange::new(start, end),
    );
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    if let Some(declared) = declared_symbol(&node.assoc) {
      let in_tdz = self.symbol_in_tdz(declared);
      self.mark(&mut node.assoc, Some(declared), in_tdz);
      if self.is_lexical_symbol(declared) {
        self.record_pending(declared);
      }
    } else {
      let start = node.loc.start_u32();
      let end = start.saturating_add(node.stx.name.len() as u32);
      self.resolve_use(
        &mut node.assoc,
        &node.stx.name,
        TextRange::new(start, end),
      );
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
