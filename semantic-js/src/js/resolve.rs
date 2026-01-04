use super::{JsSemantics, ScopeId, SymbolId};
use crate::assoc::js::{declared_symbol, scope_id, ResolvedSymbol};
use derive_visitor::{DriveMut, VisitorMut};
use diagnostics::{Diagnostic, FileId, Span, TextRange};
use parse_js::ast::class_or_object::ClassStaticBlock;
use parse_js::ast::class_or_object::{ClassMember, ClassOrObjKey, ClassOrObjVal};
use parse_js::ast::expr::pat::{ArrPatElem, IdPat, ObjPatProp};
use parse_js::ast::expr::{ClassExpr, FuncExpr, IdExpr};
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::stmt::decl::{ClassDecl, VarDecl, VarDeclMode, VarDeclarator};
use parse_js::ast::stmt::{
  BlockStmt, CatchBlock, ForBody, ForInOfLhs, ForInStmt, ForOfStmt, ForTripleStmt, SwitchBranch,
  SwitchStmt,
};
use parse_js::ast::stx::TopLevel;
use std::collections::{HashMap, HashSet};

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
type ArrPatElemNode = ArrPatElem;
type ClassMemberNode = Node<ClassMember>;
type ClassStaticBlockNode = Node<ClassStaticBlock>;
type ClassDeclNode = Node<ClassDecl>;
type ClassExprNode = Node<ClassExpr>;
type ForBodyNode = Node<ForBody>;
type FuncExprNode = Node<FuncExpr>;
type FuncNode = Node<Func>;
type FuncBodyNode = FuncBody;
type IdExprNode = Node<IdExpr>;
type IdPatNode = Node<IdPat>;
type ObjPatPropNode = Node<ObjPatProp>;
type VarDeclNode = Node<VarDecl>;
type VarDeclaratorNode = VarDeclarator;
type SwitchBranchNode = Node<SwitchBranch>;
type SwitchStmtNode = Node<SwitchStmt>;
type ForInStmtNode = Node<ForInStmt>;
type ForOfStmtNode = Node<ForOfStmt>;
type ForTripleStmtNode = Node<ForTripleStmt>;

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

#[derive(Debug, Clone, Copy)]
struct ForInOfResolveContext {
  loop_scope: Option<ScopeId>,
  lhs_active: bool,
}

#[derive(VisitorMut)]
#[visitor(
  ArrPatElemNode(enter, exit),
  BlockStmtNode(enter, exit),
  CatchBlockNode(enter, exit),
  ClassDeclNode(enter, exit),
  ClassMemberNode(enter, exit),
  ClassStaticBlockNode(enter, exit),
  ClassExprNode(enter, exit),
  ClassOrObjKey(enter, exit),
  ClassOrObjVal(enter, exit),
  ForBodyNode(enter, exit),
  ForInStmtNode(enter, exit),
  ForInOfLhs(enter, exit),
  ForOfStmtNode(enter, exit),
  ForTripleStmtNode(enter, exit),
  FuncExprNode(enter, exit),
  FuncBodyNode(enter),
  FuncNode(enter, exit),
  IdExprNode(enter),
  IdPatNode(enter),
  ObjPatPropNode(enter, exit),
  SwitchStmtNode(enter, exit),
  SwitchBranchNode(enter),
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
  class_member_depth: usize,
  class_or_obj_key_depth: usize,
  tdz_overrides: Vec<SymbolId>,
  val_override_stack: Vec<Option<SymbolId>>,
  var_decl_mode_stack: Vec<VarDeclMode>,
  pending_active: Vec<bool>,
  pending_symbols: Vec<Vec<SymbolId>>,
  class_name_stack: Vec<Option<SymbolId>>,
  in_param_list: Vec<bool>,
  func_scope_stack: Vec<ScopeId>,
  closure_cache: HashMap<ScopeId, ScopeId>,
  switch_scope_stack: Vec<(Option<ScopeId>, bool)>,
  for_in_of_stack: Vec<ForInOfResolveContext>,
  for_triple_scope_stack: Vec<Option<ScopeId>>,
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
      class_member_depth: 0,
      class_or_obj_key_depth: 0,
      tdz_overrides: Vec::new(),
      val_override_stack: Vec::new(),
      var_decl_mode_stack: Vec::new(),
      pending_active: Vec::new(),
      pending_symbols: Vec::new(),
      class_name_stack: Vec::new(),
      in_param_list: Vec::new(),
      func_scope_stack: Vec::new(),
      closure_cache: HashMap::new(),
      switch_scope_stack: Vec::new(),
      for_in_of_stack: Vec::new(),
      for_triple_scope_stack: Vec::new(),
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

  fn closure_of(&mut self, scope: ScopeId) -> ScopeId {
    if let Some(cached) = self.closure_cache.get(&scope).copied() {
      return cached;
    }

    let mut current = Some(scope);
    let mut last = scope;
    while let Some(scope_id) = current {
      let scope_data = self.sem.scope(scope_id);
      last = scope_id;
      if scope_data.kind.is_closure() || scope_data.parent.is_none() {
        break;
      }
      current = scope_data.parent;
    }

    self.closure_cache.insert(scope, last);
    last
  }

  fn symbol_in_tdz(&mut self, use_scope: ScopeId, symbol: SymbolId) -> bool {
    if self.tdz_overrides.iter().any(|sym| *sym == symbol) {
      return false;
    }
    let decl_scope = self.sem.symbol(symbol).decl_scope;

    // Uses inside a nested function can execute after the outer scope is fully
    // initialized, so we only consider TDZ within the same closure.
    if self.closure_of(use_scope) != self.closure_of(decl_scope) {
      return false;
    }

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
      let in_tdz = symbol.map_or(false, |sym| self.symbol_in_tdz(scope, sym));
      let should_report_tdz = self.file.is_some() && in_tdz && symbol.is_some();
      self.mark(assoc, symbol, in_tdz);
      if should_report_tdz {
        let file = self
          .file
          .expect("file id present when reporting diagnostics");
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

  fn enter_arr_pat_elem_node(&mut self, _node: &mut ArrPatElemNode) {
    let active = self.pending_active.last().copied().unwrap_or(false);
    self.push_pending(active);
  }

  fn exit_arr_pat_elem_node(&mut self, _node: &mut ArrPatElemNode) {
    self.pop_pending();
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
    let active = symbol
      .map(|sym| self.is_lexical_symbol(sym))
      .unwrap_or(false);
    self.push_pending(active);
    if active {
      if let Some(name) = &mut node.stx.name {
        if let Some(sym) = declared_symbol(&name.assoc) {
          self.record_pending(sym);
        }
      }
    }
    self
      .class_name_stack
      .push(if active { symbol } else { None });
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
    let active = symbol
      .map(|sym| self.is_lexical_symbol(sym))
      .unwrap_or(false);
    self.push_pending(active);
    if active {
      if let Some(name) = &mut node.stx.name {
        if let Some(sym) = declared_symbol(&name.assoc) {
          self.record_pending(sym);
        }
      }
    }
    self
      .class_name_stack
      .push(if active { symbol } else { None });
    self.push_scope_from_assoc(&node.assoc);
  }

  fn exit_class_expr_node(&mut self, node: &mut ClassExprNode) {
    self.pop_scope_from_assoc(&node.assoc);
    self.pop_pending();
    self.class_name_stack.pop();
  }

  fn enter_class_static_block_node(&mut self, node: &mut ClassStaticBlockNode) {
    self.push_scope_from_assoc(&node.assoc);
  }

  fn exit_class_static_block_node(&mut self, node: &mut ClassStaticBlockNode) {
    self.pop_scope_from_assoc(&node.assoc);
  }

  fn enter_class_member_node(&mut self, _node: &mut ClassMemberNode) {
    self.class_member_depth += 1;
  }

  fn exit_class_member_node(&mut self, _node: &mut ClassMemberNode) {
    self.class_member_depth = self.class_member_depth.saturating_sub(1);
  }

  fn enter_class_or_obj_key(&mut self, _node: &mut ClassOrObjKey) {
    self.class_or_obj_key_depth += 1;
  }

  fn exit_class_or_obj_key(&mut self, _node: &mut ClassOrObjKey) {
    self.class_or_obj_key_depth = self.class_or_obj_key_depth.saturating_sub(1);
  }

  fn enter_class_or_obj_val(&mut self, _node: &mut ClassOrObjVal) {
    let class_symbol = self.class_name_stack.last().copied().flatten();
    let should_override =
      class_symbol.is_some() && self.class_member_depth > 0 && self.class_or_obj_key_depth == 0;
    let pushed = if should_override {
      let sym = class_symbol.expect("class symbol must exist when overriding");
      self.tdz_overrides.push(sym);
      Some(sym)
    } else {
      None
    };
    self.val_override_stack.push(pushed);
  }

  fn exit_class_or_obj_val(&mut self, _node: &mut ClassOrObjVal) {
    let pushed = self
      .val_override_stack
      .pop()
      .expect("val override stack should match traversal");
    if let Some(sym) = pushed {
      let popped = self.tdz_overrides.pop();
      debug_assert_eq!(popped, Some(sym));
    }
  }

  fn enter_for_body_node(&mut self, node: &mut ForBodyNode) {
    self.push_scope_from_assoc(&node.assoc);
  }

  fn exit_for_body_node(&mut self, node: &mut ForBodyNode) {
    self.pop_scope_from_assoc(&node.assoc);
  }

  fn enter_for_in_stmt_node(&mut self, node: &mut ForInStmtNode) {
    let Some(outer) = scope_id(&node.assoc) else {
      self.for_in_of_stack.push(ForInOfResolveContext {
        loop_scope: None,
        lhs_active: false,
      });
      return;
    };

    let loop_scope = scope_id(&node.stx.body.assoc)
      .and_then(|body_scope| self.sem.scope(body_scope).parent)
      .filter(|parent| *parent != outer);

    self.for_in_of_stack.push(ForInOfResolveContext {
      loop_scope,
      lhs_active: false,
    });
  }

  fn exit_for_in_stmt_node(&mut self, _node: &mut ForInStmtNode) {
    self.for_in_of_stack.pop();
  }

  fn enter_for_in_of_lhs(&mut self, node: &mut ForInOfLhs) {
    if let Some(ctx) = self.for_in_of_stack.last_mut() {
      if let Some(loop_scope) = ctx.loop_scope {
        self.scope_stack.push(loop_scope);
        self.tdz_stack.push(TdzFrame::new(loop_scope, self.sem));
        ctx.lhs_active = true;
      }
    }

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
    if let Some(ctx) = self.for_in_of_stack.last_mut() {
      if ctx.lhs_active {
        ctx.lhs_active = false;
        self.scope_stack.pop();
        self.tdz_stack.pop();
      }
    }
  }

  fn enter_for_of_stmt_node(&mut self, node: &mut ForOfStmtNode) {
    let Some(outer) = scope_id(&node.assoc) else {
      self.for_in_of_stack.push(ForInOfResolveContext {
        loop_scope: None,
        lhs_active: false,
      });
      return;
    };

    let loop_scope = scope_id(&node.stx.body.assoc)
      .and_then(|body_scope| self.sem.scope(body_scope).parent)
      .filter(|parent| *parent != outer);

    self.for_in_of_stack.push(ForInOfResolveContext {
      loop_scope,
      lhs_active: false,
    });
  }

  fn exit_for_of_stmt_node(&mut self, _node: &mut ForOfStmtNode) {
    self.for_in_of_stack.pop();
  }

  fn enter_for_triple_stmt_node(&mut self, node: &mut ForTripleStmtNode) {
    let current = self.scope_stack.last().copied();
    let scope = scope_id(&node.assoc).filter(|scope| Some(*scope) != current);
    self.for_triple_scope_stack.push(scope);
    if let Some(scope) = scope {
      self.scope_stack.push(scope);
      self.tdz_stack.push(TdzFrame::new(scope, self.sem));
    }
  }

  fn exit_for_triple_stmt_node(&mut self, _node: &mut ForTripleStmtNode) {
    let Some(scope) = self.for_triple_scope_stack.pop().flatten() else {
      return;
    };
    let popped = self.scope_stack.pop();
    self.tdz_stack.pop();
    debug_assert_eq!(popped, Some(scope));
  }

  fn enter_switch_stmt_node(&mut self, node: &mut SwitchStmtNode) {
    let current = self.scope_stack.last().copied();
    let scope = scope_id(&node.assoc).filter(|scope| Some(*scope) != current);
    self.switch_scope_stack.push((scope, false));
  }

  fn enter_switch_branch_node(&mut self, _node: &mut SwitchBranchNode) {
    let Some((scope, active)) = self.switch_scope_stack.last_mut() else {
      return;
    };
    if *active {
      return;
    }
    let Some(scope) = *scope else {
      return;
    };
    self.scope_stack.push(scope);
    self.tdz_stack.push(TdzFrame::new(scope, self.sem));
    *active = true;
  }

  fn exit_switch_stmt_node(&mut self, _node: &mut SwitchStmtNode) {
    let Some((scope, active)) = self.switch_scope_stack.pop() else {
      return;
    };
    if !active {
      return;
    }
    let Some(scope) = scope else {
      return;
    };
    let popped = self.scope_stack.pop();
    self.tdz_stack.pop();
    debug_assert_eq!(popped, Some(scope));
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
    self.resolve_use(&mut node.assoc, &node.stx.name, TextRange::new(start, end));
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    if let Some(declared) = declared_symbol(&node.assoc) {
      let scope = scope_id(&node.assoc).unwrap_or_else(|| self.sem.symbol(declared).decl_scope);
      let in_tdz = self.symbol_in_tdz(scope, declared);
      self.mark(&mut node.assoc, Some(declared), in_tdz);
      if self.is_lexical_symbol(declared) {
        self.record_pending(declared);
      }
    } else {
      let start = node.loc.start_u32();
      let end = start.saturating_add(node.stx.name.len() as u32);
      self.resolve_use(&mut node.assoc, &node.stx.name, TextRange::new(start, end));
    }
  }

  fn enter_obj_pat_prop_node(&mut self, _node: &mut ObjPatPropNode) {
    let active = self.pending_active.last().copied().unwrap_or(false);
    self.push_pending(active);
  }

  fn exit_obj_pat_prop_node(&mut self, _node: &mut ObjPatPropNode) {
    self.pop_pending();
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
