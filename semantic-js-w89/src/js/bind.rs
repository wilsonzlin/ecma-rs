use super::semantics::JsSemantics;
use super::semantics::ScopeId;
use super::semantics::ScopeKind;
use super::semantics::SymbolId;
use super::JsMode;
use crate::assoc::DeclaredSymbol;
use derive_visitor::DriveMut;
use derive_visitor::VisitorMut;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::ClassExpr;
use parse_js::ast::expr::FuncExpr;
use parse_js::ast::func::Func;
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::stmt::decl::ClassDecl;
use parse_js::ast::stmt::decl::FuncDecl;
use parse_js::ast::stmt::decl::PatDecl;
use parse_js::ast::stmt::decl::VarDecl;
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::BlockStmt;
use parse_js::ast::stmt::CatchBlock;
use parse_js::ast::stmt::ForBody;
use parse_js::ast::stmt::ForInOfLhs;
use parse_js::ast::stmt::ForInStmt;
use parse_js::ast::stmt::ForOfStmt;
use parse_js::ast::stmt::ImportStmt;
use parse_js::ast::stx::TopLevel;

pub fn bind(top_level: &mut Node<TopLevel>, mode: JsMode) -> JsSemantics {
  let mut sem = JsSemantics::new(mode);
  let root_scope = sem.root_scope();
  let mut visitor = DeclVisitor::new(&mut sem, root_scope);
  top_level.drive_mut(&mut visitor);
  sem
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum AddToScope {
  IfNotGlobal,
  NearestClosure,
}

type BlockStmtNode = Node<BlockStmt>;
type CatchBlockNode = Node<CatchBlock>;
type ClassDeclNode = Node<ClassDecl>;
type ClassExprNode = Node<ClassExpr>;
type ForBodyNode = Node<ForBody>;
type ForInStmtNode = Node<ForInStmt>;
type ForOfStmtNode = Node<ForOfStmt>;
type FuncNode = Node<Func>;
type FuncDeclNode = Node<FuncDecl>;
type FuncExprNode = Node<FuncExpr>;
type IdPatNode = Node<IdPat>;
type ImportStmtNode = Node<ImportStmt>;
type PatDeclNode = Node<PatDecl>;
type VarDeclNode = Node<VarDecl>;

#[derive(VisitorMut)]
#[visitor(
  BlockStmtNode,
  CatchBlockNode,
  ClassDeclNode,
  ClassExprNode,
  ForBodyNode,
  ForInStmtNode,
  ForOfStmtNode,
  FuncNode,
  FuncDeclNode(enter),
  FuncExprNode,
  IdPatNode(enter),
  ImportStmtNode,
  PatDeclNode,
  VarDeclNode,
  NodeAssocData(enter)
)]
struct DeclVisitor<'a> {
  sem: &'a mut JsSemantics,
  scope_stack: Vec<ScopeId>,
  pattern_action_stack: Vec<AddToScope>,
  in_pattern_decl: Vec<bool>,
  for_pattern_actions: Vec<bool>,
}

impl<'a> DeclVisitor<'a> {
  fn new(sem: &'a mut JsSemantics, root_scope: ScopeId) -> Self {
    Self {
      sem,
      scope_stack: vec![root_scope],
      pattern_action_stack: Vec::new(),
      in_pattern_decl: vec![false],
      for_pattern_actions: Vec::new(),
    }
  }

  fn scope(&self) -> ScopeId {
    *self.scope_stack.last().expect("scope stack is never empty")
  }

  fn new_scope(&mut self, kind: ScopeKind) {
    let parent = self.scope();
    let child = self.sem.push_scope(parent, kind);
    self.scope_stack.push(child);
  }

  fn restore_scope(&mut self) {
    self.scope_stack.pop().expect("scope stack underflow");
  }

  fn new_pattern_action(&mut self, action: AddToScope) {
    self.pattern_action_stack.push(action);
  }

  fn restore_pattern_action(&mut self) {
    self
      .pattern_action_stack
      .pop()
      .expect("pattern action stack underflow");
  }

  fn is_in_pattern_decl(&self) -> bool {
    *self
      .in_pattern_decl
      .last()
      .expect("pattern decl stack empty")
  }

  fn enter_pattern_decl(&mut self) {
    self.in_pattern_decl.push(true);
  }

  fn exit_pattern_decl(&mut self) {
    self
      .in_pattern_decl
      .pop()
      .expect("pattern decl stack underflow");
  }

  fn pattern_action(&self) -> AddToScope {
    *self
      .pattern_action_stack
      .last()
      .expect("pattern action requested outside declaration")
  }

  fn nearest_closure(&self) -> Option<ScopeId> {
    self
      .scope_stack
      .iter()
      .rev()
      .copied()
      .find(|id| self.sem.scope(*id).kind.is_closure())
  }

  fn declare(&mut self, name: String, assoc: &mut NodeAssocData, action: AddToScope) -> SymbolId {
    let current_scope = self.scope();
    let target_scope = match action {
      AddToScope::IfNotGlobal => {
        let kind = self.sem.scope(current_scope).kind;
        if kind == ScopeKind::Global {
          None
        } else {
          Some(current_scope)
        }
      }
      AddToScope::NearestClosure => self.nearest_closure(),
    };

    let declared_at = target_scope.unwrap_or(current_scope);
    let symbol_id = if let Some(target_scope) = target_scope {
      if let Some(existing) = self.sem.scope(target_scope).symbols.get(&name) {
        *existing
      } else {
        let id = self.sem.allocate_symbol(declared_at, name.clone());
        self
          .sem
          .scope_mut(target_scope)
          .symbols
          .insert(name.clone(), id);
        id
      }
    } else {
      self.sem.allocate_symbol(declared_at, name.clone())
    };
    assoc.set(DeclaredSymbol(symbol_id));
    symbol_id
  }
}

fn pattern_action_for_mode(mode: VarDeclMode) -> AddToScope {
  match mode {
    VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing => {
      AddToScope::IfNotGlobal
    }
    VarDeclMode::Var => AddToScope::NearestClosure,
  }
}

impl DeclVisitor<'_> {
  fn enter_block_stmt_node(&mut self, _node: &mut BlockStmtNode) {
    self.new_scope(ScopeKind::Block);
  }

  fn exit_block_stmt_node(&mut self, _node: &mut BlockStmtNode) {
    self.restore_scope();
  }

  fn enter_catch_block_node(&mut self, _node: &mut CatchBlockNode) {
    self.new_scope(ScopeKind::Block);
    self.new_pattern_action(AddToScope::IfNotGlobal);
  }

  fn exit_catch_block_node(&mut self, _node: &mut CatchBlockNode) {
    self.restore_scope();
    self.restore_pattern_action();
  }

  fn enter_class_decl_node(&mut self, node: &mut ClassDeclNode) {
    if let Some(name) = &mut node.stx.name {
      self.declare(
        name.stx.name.clone(),
        &mut name.assoc,
        AddToScope::IfNotGlobal,
      );
    }
    self.new_scope(ScopeKind::Class);
  }

  fn exit_class_decl_node(&mut self, _node: &mut ClassDeclNode) {
    self.restore_scope();
  }

  fn enter_class_expr_node(&mut self, node: &mut ClassExprNode) {
    self.new_scope(ScopeKind::Class);
    if let Some(name) = &mut node.stx.name {
      self.declare(
        name.stx.name.clone(),
        &mut name.assoc,
        AddToScope::IfNotGlobal,
      );
    }
  }

  fn exit_class_expr_node(&mut self, _node: &mut ClassExprNode) {
    self.restore_scope();
  }

  fn enter_for_body_node(&mut self, _node: &mut ForBodyNode) {
    self.new_scope(ScopeKind::Block);
  }

  fn exit_for_body_node(&mut self, _node: &mut ForBodyNode) {
    self.restore_scope();
  }

  fn enter_for_in_stmt_node(&mut self, node: &mut ForInStmtNode) {
    let pushed = match &node.stx.lhs {
      ForInOfLhs::Decl((mode, _)) => {
        self.new_pattern_action(pattern_action_for_mode(*mode));
        true
      }
      _ => false,
    };
    self.for_pattern_actions.push(pushed);
  }

  fn exit_for_in_stmt_node(&mut self, _node: &mut ForInStmtNode) {
    if self.for_pattern_actions.pop().unwrap_or(false) {
      self.restore_pattern_action();
    }
  }

  fn enter_for_of_stmt_node(&mut self, node: &mut ForOfStmtNode) {
    let pushed = match &node.stx.lhs {
      ForInOfLhs::Decl((mode, _)) => {
        self.new_pattern_action(pattern_action_for_mode(*mode));
        true
      }
      _ => false,
    };
    self.for_pattern_actions.push(pushed);
  }

  fn exit_for_of_stmt_node(&mut self, _node: &mut ForOfStmtNode) {
    if self.for_pattern_actions.pop().unwrap_or(false) {
      self.restore_pattern_action();
    }
  }

  fn enter_func_node(&mut self, node: &mut FuncNode) {
    if node.stx.arrow {
      self.new_scope(ScopeKind::ArrowFunction);
    } else {
      self.new_scope(ScopeKind::NonArrowFunction);
    }
    self.new_pattern_action(AddToScope::NearestClosure);
  }

  fn exit_func_node(&mut self, _node: &mut FuncNode) {
    self.restore_scope();
    self.restore_pattern_action();
  }

  fn enter_func_decl_node(&mut self, node: &mut FuncDeclNode) {
    if let Some(name) = &mut node.stx.name {
      self.declare(
        name.stx.name.clone(),
        &mut name.assoc,
        AddToScope::NearestClosure,
      );
    }
  }

  fn enter_func_expr_node(&mut self, node: &mut FuncExprNode) {
    self.new_scope(ScopeKind::NonArrowFunction);
    if let Some(name) = &mut node.stx.name {
      self.declare(
        name.stx.name.clone(),
        &mut name.assoc,
        AddToScope::IfNotGlobal,
      );
    }
  }

  fn exit_func_expr_node(&mut self, _node: &mut FuncExprNode) {
    self.restore_scope();
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    if self.is_in_pattern_decl() {
      let action = self.pattern_action();
      self.declare(node.stx.name.clone(), &mut node.assoc, action);
    }
  }

  fn enter_import_stmt_node(&mut self, _node: &mut ImportStmtNode) {
    self.new_pattern_action(AddToScope::IfNotGlobal);
  }

  fn exit_import_stmt_node(&mut self, _node: &mut ImportStmtNode) {
    self.restore_pattern_action();
  }

  fn enter_pat_decl_node(&mut self, _node: &mut PatDeclNode) {
    self.enter_pattern_decl();
  }

  fn exit_pat_decl_node(&mut self, _node: &mut PatDeclNode) {
    self.exit_pattern_decl();
  }

  fn enter_var_decl_node(&mut self, node: &mut VarDeclNode) {
    self.new_pattern_action(pattern_action_for_mode(node.stx.mode));
  }

  fn exit_var_decl_node(&mut self, _node: &mut VarDeclNode) {
    self.restore_pattern_action();
  }

  fn enter_node_assoc_data(&mut self, assoc: &mut NodeAssocData) {
    assoc.set(self.scope());
  }
}
