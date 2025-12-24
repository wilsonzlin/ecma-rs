use super::JsSemantics;
use super::NameId;
use super::ScopeData;
use super::ScopeId;
use super::ScopeKind;
use super::SymbolData;
use super::SymbolId;
use super::TopLevelMode;
use crate::assoc::js::DeclaredSymbol;
use ahash::HashMap;
use derive_visitor::DriveMut;
use derive_visitor::VisitorMut;
use parse_js::ast::expr::pat::ClassOrFuncName;
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
use parse_js::ast::stmt::ImportStmt;
use parse_js::ast::stx::TopLevel;

type BlockStmtNode = Node<BlockStmt>;
type CatchBlockNode = Node<CatchBlock>;
type ClassDeclNode = Node<ClassDecl>;
type ClassExprNode = Node<ClassExpr>;
type FuncDeclNode = Node<FuncDecl>;
type FuncExprNode = Node<FuncExpr>;
type FuncNode = Node<Func>;
type ForBodyNode = Node<ForBody>;
type IdPatNode = Node<IdPat>;
type ImportStmtNode = Node<ImportStmt>;
type PatDeclNode = Node<PatDecl>;
type VarDeclNode = Node<VarDecl>;

pub fn declare(top_level: &mut Node<TopLevel>, mode: TopLevelMode) -> JsSemantics {
  let mut visitor = DeclareVisitor::new(mode);
  top_level.drive_mut(&mut visitor);
  visitor.finish()
}

struct SemanticsBuilder {
  names: Vec<String>,
  name_lookup: HashMap<String, NameId>,
  scopes: Vec<ScopeData>,
  symbols: Vec<SymbolData>,
  top_scope: ScopeId,
}

impl SemanticsBuilder {
  fn new(mode: TopLevelMode) -> Self {
    let kind = match mode {
      TopLevelMode::Global => ScopeKind::Global,
      TopLevelMode::Module => ScopeKind::Module,
    };
    let mut scopes = Vec::new();
    scopes.push(ScopeData {
      parent: None,
      kind,
      children: Vec::new(),
      symbols: HashMap::default(),
    });
    Self {
      names: Vec::new(),
      name_lookup: HashMap::default(),
      scopes,
      symbols: Vec::new(),
      top_scope: ScopeId(0),
    }
  }

  fn scope_kind(&self, id: ScopeId) -> ScopeKind {
    self.scopes[id.index()].kind
  }

  fn new_scope(&mut self, parent: ScopeId, kind: ScopeKind) -> ScopeId {
    let id = ScopeId(self.scopes.len() as u32);
    self.scopes.push(ScopeData {
      parent: Some(parent),
      kind,
      children: Vec::new(),
      symbols: HashMap::default(),
    });
    self.scopes[parent.index()].children.push(id);
    id
  }

  fn intern_name(&mut self, name: &str) -> NameId {
    if let Some(id) = self.name_lookup.get(name) {
      *id
    } else {
      let id = NameId(self.names.len() as u32);
      self.names.push(name.to_string());
      self.name_lookup.insert(name.to_string(), id);
      id
    }
  }

  fn declare_in_scope(&mut self, scope: ScopeId, name: &str) -> SymbolId {
    let name_id = self.intern_name(name);
    if let Some(existing) = self.scopes[scope.index()].symbols.get(&name_id) {
      return *existing;
    }
    let id = SymbolId(self.symbols.len() as u32);
    self.scopes[scope.index()].symbols.insert(name_id, id);
    self.symbols.push(SymbolData {
      name: name_id,
      decl_scope: scope,
    });
    id
  }

  fn finish(self) -> JsSemantics {
    JsSemantics {
      names: self.names,
      name_lookup: self.name_lookup,
      scopes: self.scopes,
      symbols: self.symbols,
      top_scope: self.top_scope,
    }
  }
}

#[derive(Clone, Copy)]
enum DeclTarget {
  IfNotGlobal,
  NearestClosure,
}

#[derive(VisitorMut)]
#[visitor(
  BlockStmtNode,
  CatchBlockNode,
  ClassDeclNode,
  ClassExprNode,
  ForBodyNode,
  ForInOfLhs,
  FuncDeclNode(enter),
  FuncExprNode,
  FuncNode,
  IdPatNode(enter),
  ImportStmtNode,
  PatDeclNode,
  VarDeclNode,
  NodeAssocData(enter)
)]
struct DeclareVisitor {
  builder: SemanticsBuilder,
  scope_stack: Vec<ScopeId>,
  decl_target_stack: Vec<DeclTarget>,
  in_pattern_decl: Vec<bool>,
}

impl DeclareVisitor {
  fn new(mode: TopLevelMode) -> Self {
    let builder = SemanticsBuilder::new(mode);
    let top_scope = builder.top_scope;
    Self {
      builder,
      scope_stack: vec![top_scope],
      decl_target_stack: Vec::new(),
      in_pattern_decl: vec![false],
    }
  }

  fn finish(self) -> JsSemantics {
    self.builder.finish()
  }

  fn current_scope(&self) -> ScopeId {
    *self.scope_stack.last().unwrap()
  }

  fn push_scope(&mut self, kind: ScopeKind) {
    let parent = self.current_scope();
    let id = self.builder.new_scope(parent, kind);
    self.scope_stack.push(id);
  }

  fn pop_scope(&mut self) {
    self.scope_stack.pop();
  }

  fn push_decl_target(&mut self, target: DeclTarget) {
    self.decl_target_stack.push(target);
  }

  fn pop_decl_target(&mut self) {
    self.decl_target_stack.pop();
  }

  fn in_pattern_decl(&self) -> bool {
    *self.in_pattern_decl.last().unwrap()
  }

  fn enter_pattern_decl(&mut self) {
    self.in_pattern_decl.push(true);
  }

  fn exit_pattern_decl(&mut self) {
    self.in_pattern_decl.pop();
  }

  fn nearest_closure(&self) -> Option<ScopeId> {
    self
      .scope_stack
      .iter()
      .rev()
      .copied()
      .find(|id| self.builder.scope_kind(*id).is_closure())
  }

  fn declare_with_target(&mut self, name: &str, target: DeclTarget) -> Option<SymbolId> {
    match target {
      DeclTarget::IfNotGlobal => {
        let scope = self.current_scope();
        if self.builder.scope_kind(scope) == ScopeKind::Global {
          None
        } else {
          Some(self.builder.declare_in_scope(scope, name))
        }
      }
      DeclTarget::NearestClosure => {
        let scope = self.nearest_closure()?;
        Some(self.builder.declare_in_scope(scope, name))
      }
    }
  }

  fn declare_class_or_func_name(&mut self, node: &mut Node<ClassOrFuncName>, target: DeclTarget) {
    if let Some(symbol) = self.declare_with_target(&node.stx.name, target) {
      node.assoc.set(DeclaredSymbol(symbol));
    }
  }

  fn enter_node_assoc_data(&mut self, assoc: &mut NodeAssocData) {
    assoc.set(self.current_scope());
  }
}

impl DeclareVisitor {
  fn enter_block_stmt_node(&mut self, _node: &mut BlockStmtNode) {
    self.push_scope(ScopeKind::Block);
  }

  fn exit_block_stmt_node(&mut self, _node: &mut BlockStmtNode) {
    self.pop_scope();
  }

  fn enter_catch_block_node(&mut self, _node: &mut CatchBlockNode) {
    self.push_scope(ScopeKind::Block);
    self.push_decl_target(DeclTarget::IfNotGlobal);
  }

  fn exit_catch_block_node(&mut self, _node: &mut CatchBlockNode) {
    self.pop_scope();
    self.pop_decl_target();
  }

  fn enter_class_decl_node(&mut self, node: &mut ClassDeclNode) {
    if let Some(name) = &mut node.stx.name {
      self.declare_class_or_func_name(name, DeclTarget::IfNotGlobal);
    }
    self.push_scope(ScopeKind::Class);
  }

  fn exit_class_decl_node(&mut self, _node: &mut ClassDeclNode) {
    self.pop_scope();
  }

  fn enter_class_expr_node(&mut self, node: &mut ClassExprNode) {
    self.push_scope(ScopeKind::Class);
    if let Some(name) = &mut node.stx.name {
      self.declare_class_or_func_name(name, DeclTarget::IfNotGlobal);
    }
  }

  fn exit_class_expr_node(&mut self, _node: &mut ClassExprNode) {
    self.pop_scope();
  }

  fn enter_for_body_node(&mut self, _node: &mut ForBodyNode) {
    self.push_scope(ScopeKind::Block);
  }

  fn exit_for_body_node(&mut self, _node: &mut ForBodyNode) {
    self.pop_scope();
  }

  fn enter_for_in_of_lhs(&mut self, node: &mut ForInOfLhs) {
    if let ForInOfLhs::Decl((mode, _)) = node {
      let target = match mode {
        VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing => {
          DeclTarget::IfNotGlobal
        }
        VarDeclMode::Var => DeclTarget::NearestClosure,
      };
      self.push_decl_target(target);
    }
  }

  fn exit_for_in_of_lhs(&mut self, node: &mut ForInOfLhs) {
    if matches!(node, ForInOfLhs::Decl(_)) {
      self.pop_decl_target();
    }
  }

  fn enter_func_decl_node(&mut self, node: &mut FuncDeclNode) {
    if let Some(name) = &mut node.stx.name {
      self.declare_class_or_func_name(name, DeclTarget::NearestClosure);
    }
  }

  fn enter_func_expr_node(&mut self, node: &mut FuncExprNode) {
    self.push_scope(ScopeKind::FunctionExpressionName);
    if let Some(name) = &mut node.stx.name {
      self.declare_class_or_func_name(name, DeclTarget::IfNotGlobal);
    }
  }

  fn exit_func_expr_node(&mut self, _node: &mut FuncExprNode) {
    self.pop_scope();
  }

  fn enter_func_node(&mut self, node: &mut FuncNode) {
    let kind = if node.stx.arrow {
      ScopeKind::ArrowFunction
    } else {
      ScopeKind::NonArrowFunction
    };
    self.push_scope(kind);
    self.push_decl_target(DeclTarget::NearestClosure);
  }

  fn exit_func_node(&mut self, _node: &mut FuncNode) {
    self.pop_scope();
    self.pop_decl_target();
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    if self.in_pattern_decl() {
      if let Some(target) = self.decl_target_stack.last().copied() {
        if let Some(symbol) = self.declare_with_target(&node.stx.name, target) {
          node.assoc.set(DeclaredSymbol(symbol));
        }
      }
    }
  }

  fn enter_import_stmt_node(&mut self, _node: &mut ImportStmtNode) {
    self.push_decl_target(DeclTarget::IfNotGlobal);
  }

  fn exit_import_stmt_node(&mut self, _node: &mut ImportStmtNode) {
    self.pop_decl_target();
  }

  fn enter_pat_decl_node(&mut self, _node: &mut PatDeclNode) {
    self.enter_pattern_decl();
  }

  fn exit_pat_decl_node(&mut self, _node: &mut PatDeclNode) {
    self.exit_pattern_decl();
  }

  fn enter_var_decl_node(&mut self, node: &mut VarDeclNode) {
    let target = match node.stx.mode {
      VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing => {
        DeclTarget::IfNotGlobal
      }
      VarDeclMode::Var => DeclTarget::NearestClosure,
    };
    self.push_decl_target(target);
  }

  fn exit_var_decl_node(&mut self, _node: &mut VarDeclNode) {
    self.pop_decl_target();
  }
}

#[cfg(test)]
mod tests {
  use super::declare;
  use crate::assoc::js::scope_id;
  use crate::js::{ScopeId, ScopeKind, TopLevelMode};
  use derive_visitor::Drive;
  use derive_visitor::Visitor;
  use parse_js::ast::expr::IdExpr;
  use parse_js::ast::node::Node;
  use parse_js::loc::Loc;
  use parse_js::parse;

  type IdExprNode = Node<IdExpr>;

  #[derive(Default, Visitor)]
  #[visitor(IdExprNode(enter))]
  struct IdCollector {
    seen: Vec<(String, ScopeId, Loc)>,
  }

  impl IdCollector {
    fn enter_id_expr_node(&mut self, node: &IdExprNode) {
      let scope = scope_id(&node.assoc).expect("expected scope id");
      self.seen.push((node.stx.name.clone(), scope, node.loc));
    }
  }

  #[test]
  fn builds_scope_tree() {
    let mut top = parse(
      "function outer(a) { let x; { const y = 1; } function inner(b) { var c; const d = () => { let e; }; } }",
    )
    .unwrap();
    let semantics = declare(&mut top, TopLevelMode::Module);
    let root = semantics.top_scope();
    assert_eq!(semantics.scope(root).kind, ScopeKind::Module);

    let outer = semantics.scope(root).children[0];
    assert_eq!(semantics.scope(outer).kind, ScopeKind::NonArrowFunction);

    let outer_children = &semantics.scope(outer).children;
    assert_eq!(outer_children.len(), 2);
    assert_eq!(semantics.scope(outer_children[0]).kind, ScopeKind::Block);
    assert_eq!(
      semantics.scope(outer_children[1]).kind,
      ScopeKind::NonArrowFunction
    );

    let inner = outer_children[1];
    let inner_children = &semantics.scope(inner).children;
    assert_eq!(inner_children.len(), 1);
    assert_eq!(
      semantics.scope(inner_children[0]).kind,
      ScopeKind::ArrowFunction
    );
  }

  #[test]
  fn for_in_of_declares_symbols() {
    let mut top = parse("for (let x of y) {} for (var z in y) {}").unwrap();
    let semantics = declare(&mut top, TopLevelMode::Module);
    let root = semantics.top_scope();
    let root_scope = semantics.scope(root);
    let x = semantics.name_id("x").unwrap();
    let z = semantics.name_id("z").unwrap();
    assert!(root_scope.symbols.get(&x).is_some());
    assert!(root_scope.symbols.get(&z).is_some());
  }

  #[test]
  fn global_mode_skips_top_level_symbols() {
    let mut top = parse("var a = 1; let b = 2; function f(c) { let d; } class C {}").unwrap();
    let semantics = declare(&mut top, TopLevelMode::Global);
    let root = semantics.top_scope();
    let root_scope = semantics.scope(root);
    assert!(root_scope.symbols.is_empty());

    let func_scope = semantics.scope(root).children[0];
    assert_eq!(
      semantics.scope(func_scope).kind,
      ScopeKind::NonArrowFunction
    );

    let c = semantics.name_id("c").unwrap();
    let d = semantics.name_id("d").unwrap();
    let func_scope = semantics.scope(func_scope);
    assert!(func_scope.symbols.get(&c).is_some());
    assert!(func_scope.symbols.get(&d).is_some());
  }

  #[test]
  fn attaches_scope_ids_per_node() {
    let mut parsed = parse(
      r#"
      let value = 0;
      function wrap() {
        {
          value;
        }
      }
      value;
    "#,
    )
    .unwrap();

    let semantics = declare(&mut parsed, TopLevelMode::Global);
    let mut collector = IdCollector::default();
    parsed.drive(&mut collector);

    collector.seen.sort_by_key(|(_, _, loc)| loc.0);
    assert_eq!(collector.seen.len(), 2);
    assert_eq!(collector.seen[0].0, "value");
    assert_eq!(collector.seen[1].0, "value");
    assert_ne!(collector.seen[0].1, collector.seen[1].1);
    assert_eq!(semantics.scope(collector.seen[1].1).kind, ScopeKind::Global);
  }
}
