use crate::symbol::Scope;
use crate::symbol::ScopeType;
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
use parse_js::ast::stmt::ImportStmt;

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
  FuncNode,
  FuncDeclNode(enter),
  FuncExprNode,
  IdPatNode(enter),
  ImportStmtNode,
  PatDeclNode,
  VarDeclNode,
  NodeAssocData(enter),
)]
pub(crate) struct DeclVisitor {
  scope_stack: Vec<Scope>,
  pattern_action_stack: Vec<AddToScope>,
  in_pattern_decl: Vec<bool>,
}

impl DeclVisitor {
  pub fn new(top_level_scope: Scope) -> DeclVisitor {
    Self {
      scope_stack: vec![top_level_scope],
      pattern_action_stack: Vec::new(),
      in_pattern_decl: vec![false],
    }
  }

  fn scope(&self) -> &Scope {
    self.scope_stack.last().unwrap()
  }

  fn add_to_scope(&mut self, name: String, action: AddToScope) {
    match action {
      AddToScope::IfNotGlobal => {
        self.scope().data_mut().add_symbol_if_not_global(name);
      }
      AddToScope::NearestClosure => {
        if let Some(closure) = self.scope().find_nearest_scope(|t| t.is_closure()) {
          closure.data_mut().add_symbol(name);
        };
      }
    };
  }

  fn new_scope(&mut self, new_scope_type: ScopeType) {
    self.scope_stack.push(self.scope().create_child_scope(new_scope_type));
  }

  fn restore_scope(&mut self) {
    self.scope_stack.pop().unwrap();
  }

  fn pattern_action(&self) -> AddToScope {
    *self.pattern_action_stack.last().unwrap()
  }

  fn new_pattern_action(&mut self, new_pattern_action: AddToScope) {
    self.pattern_action_stack.push(new_pattern_action);
  }

  fn restore_pattern_action(&mut self) {
    self.pattern_action_stack.pop().unwrap();
  }

  fn is_in_pattern_decl(&self) -> bool {
    *self.in_pattern_decl.last().unwrap()
  }

  fn enter_pattern_decl(&mut self) {
    self.in_pattern_decl.push(true);
  }

  fn exit_pattern_decl(&mut self) {
    self.in_pattern_decl.pop().unwrap();
  }
}

impl DeclVisitor {
  fn enter_block_stmt_node(&mut self, _node: &mut BlockStmtNode) {
    self.new_scope(ScopeType::Block);
  }

  fn exit_block_stmt_node(&mut self, _node: &mut BlockStmtNode) {
    self.restore_scope();
  }

  fn enter_catch_block_node(&mut self, _node: &mut CatchBlockNode) {
    self.new_scope(ScopeType::Block);
    // For the parameter.
    self.new_pattern_action(AddToScope::IfNotGlobal);
  }

  fn exit_catch_block_node(&mut self, _node: &mut CatchBlockNode) {
    self.restore_scope();
    self.restore_pattern_action();
  }

  fn enter_class_decl_node(&mut self, node: &mut ClassDeclNode) {
    if let Some(name) = &node.stx.name {
      let ClassOrFuncName { name } = name.stx.as_ref();
      self.add_to_scope(name.clone(), AddToScope::IfNotGlobal);
    };
    self.new_scope(ScopeType::Class);
  }

  fn exit_class_decl_node(&mut self, _node: &mut ClassDeclNode) {
    self.restore_scope();
  }

  fn enter_class_expr_node(&mut self, node: &mut ClassExprNode) {
    // The name belongs to the new Class scope (unlike a ClassDecl).
    self.new_scope(ScopeType::Class);
    if let Some(name) = &node.stx.name {
      let ClassOrFuncName { name } = name.stx.as_ref();
      self.add_to_scope(name.clone(), AddToScope::IfNotGlobal);
    };
  }

  fn exit_class_expr_node(&mut self, _node: &mut ClassExprNode) {
    self.restore_scope();
  }

  fn enter_for_body_node(&mut self, _node: &mut ForBodyNode) {
    self.new_scope(ScopeType::Block);
  }

  fn exit_for_body_node(&mut self, _node: &mut ForBodyNode) {
    self.restore_scope();
  }

  fn enter_func_node(&mut self, node: &mut FuncNode) {
    if node.stx.arrow {
      self.new_scope(ScopeType::ArrowFunction);
    } else {
      self.new_scope(ScopeType::NonArrowFunction);
    }
    // For the parameters.
    self.new_pattern_action(AddToScope::NearestClosure);
  }

  fn exit_func_node(&mut self, _node: &mut FuncNode) {
    self.restore_scope();
    self.restore_pattern_action();
  }

  fn enter_func_decl_node(&mut self, node: &mut FuncDeclNode) {
    // WARNING: The name belongs in the containing scope, not the function's scope.
    // See examples/function.js.
    if let Some(name) = &node.stx.name {
      let ClassOrFuncName { name } = name.stx.as_ref();
      self.add_to_scope(name.clone(), AddToScope::NearestClosure);
    };
  }

  fn enter_func_expr_node(&mut self, node: &mut FuncExprNode) {
    // We need to create a new scope just for the name itself. Unlike function declarations, function expressions are not declared within their current closure or block. However, their names cannot be assigned to within the function (it has no effect in non-strict mode) and they can be "redeclared" e.g. `(function a() { let a = 1; })()`. See examples/function.js.
    // TODO Is NonArrowFunction the best choice?
    self.new_scope(ScopeType::NonArrowFunction);
    if let Some(name) = &node.stx.name {
      let ClassOrFuncName { name } = name.stx.as_ref();
      self.add_to_scope(name.clone(), AddToScope::IfNotGlobal);
    };
  }

  fn exit_func_expr_node(&mut self, _node: &mut FuncExprNode) {
    self.restore_scope();
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    // An identifier pattern doesn't always mean declaration e.g. simple assignment, assignment to global. This is why we need in_param_decl; an assignment is an expression that could appear almost anywhere (e.g. function parameter default value expression).
    if self.is_in_pattern_decl() {
      self.add_to_scope(node.stx.name.clone(), self.pattern_action());
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
    self.new_pattern_action(match node.stx.mode {
      VarDeclMode::Const => AddToScope::IfNotGlobal,
      VarDeclMode::Let => AddToScope::IfNotGlobal,
      VarDeclMode::Var => AddToScope::NearestClosure,
    });
  }

  fn exit_var_decl_node(&mut self, _node: &mut VarDeclNode) {
    self.restore_pattern_action();
  }

  // We want to associate every node with a scope. We do this by visiting every node and associating it with the current (i.e. top-of-stack) scope.
  // Since Node is a generic type, to avoid walking every Node<T> type, we visit NodeAssocData instead which is present on every node.
  // Some nodes create new scopes (see previous enter_* methods in this DeclVisitor), and it's ambiguous whether the new scope should be associated with it or not (i.e. start new scope at itself or its children). It doesn't really matter e.g. a new BlockStmt block scope must be assoc. with its `let` decls, but whether it is attached to the BlockStmt node itself doesn't affect anything.
  // Since it doesn't really matter, we arbitrarily choose to start at children, as otherwise we can't use this simple NodeAssocData visit trick since we'd have to set assoc data after processing a node's stx but before recursing into stx.
  fn enter_node_assoc_data(&mut self, assoc: &mut NodeAssocData) {
    assoc.set(self.scope().clone());
  }
}
