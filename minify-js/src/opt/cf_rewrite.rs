use super::traverse::apply_to_function_like_bodies;
use super::{OptCtx, Pass};
use ahash::HashSet;
use derive_visitor::{Drive, Visitor};
use parse_js::ast::expr::pat::{ClassOrFuncName, IdPat, Pat};
use parse_js::ast::node::{Node, NodeAssocData};
use parse_js::ast::stmt::decl::{PatDecl, VarDecl, VarDeclMode, VarDeclarator};
use parse_js::ast::stmt::{CatchBlock, ForBody, Stmt, SwitchBranch, TryStmt};
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use semantic_js::assoc::js::{declared_symbol, scope_id};
use semantic_js::js::{ScopeId, ScopeKind, SymbolId};

pub(super) struct ControlFlowRewritePass;

impl Pass for ControlFlowRewritePass {
  fn name(&self) -> &'static str {
    "cf-rewrite"
  }

  fn run(&mut self, cx: &mut OptCtx, top: &mut Node<TopLevel>) -> bool {
    apply_to_function_like_bodies(top, |stmts, changed| {
      rewrite_stmts(stmts, cx, changed, true)
    })
  }
}

fn new_node<T>(loc: Loc, assoc: NodeAssocData, stx: T) -> Node<T>
where
  T: derive_visitor::Drive + derive_visitor::DriveMut,
{
  Node {
    loc,
    assoc,
    stx: Box::new(stx),
  }
}

fn is_var_scope_kind(kind: ScopeKind) -> bool {
  matches!(
    kind,
    ScopeKind::Module
      | ScopeKind::NonArrowFunction
      | ScopeKind::ArrowFunction
      | ScopeKind::StaticBlock
  )
}

fn nearest_var_scope(sem: &semantic_js::js::JsSemantics, scope: ScopeId) -> Option<ScopeId> {
  let mut current = Some(scope);
  while let Some(scope_id) = current {
    let scope_data = sem.scope(scope_id);
    if is_var_scope_kind(scope_data.kind) {
      return Some(scope_id);
    }
    current = scope_data.parent;
  }
  None
}

fn is_unconditional_terminator(stmt: &Node<Stmt>) -> bool {
  match stmt.stx.as_ref() {
    Stmt::Return(_) | Stmt::Throw(_) | Stmt::Break(_) | Stmt::Continue(_) => true,
    Stmt::Block(block) => block
      .stx
      .body
      .last()
      .is_some_and(|last| is_unconditional_terminator(last)),
    _ => false,
  }
}

fn is_braced_for_body(body: &Node<ForBody>) -> bool {
  let Some(first) = body.stx.body.first() else {
    return true;
  };
  body.loc.0 < first.loc.0
}

#[derive(Default)]
struct DeclSymbols {
  declared: HashSet<SymbolId>,
  func_decls: HashSet<SymbolId>,
}

fn collect_decl_symbols(stmt: &Node<Stmt>) -> DeclSymbols {
  type IdPatNode = Node<IdPat>;
  type ClassOrFuncNameNode = Node<ClassOrFuncName>;
  type FuncDeclNode = Node<parse_js::ast::stmt::decl::FuncDecl>;

  #[derive(Default, Visitor)]
  #[visitor(IdPatNode(enter), ClassOrFuncNameNode(enter), FuncDeclNode(enter))]
  struct Collector {
    out: DeclSymbols,
  }

  impl Collector {
    fn enter_id_pat_node(&mut self, node: &IdPatNode) {
      if let Some(sym) = declared_symbol(&node.assoc) {
        self.out.declared.insert(sym);
      }
    }

    fn enter_class_or_func_name_node(&mut self, node: &ClassOrFuncNameNode) {
      if let Some(sym) = declared_symbol(&node.assoc) {
        self.out.declared.insert(sym);
      }
    }

    fn enter_func_decl_node(&mut self, node: &FuncDeclNode) {
      let Some(name) = node.stx.name.as_ref() else {
        return;
      };
      if let Some(sym) = declared_symbol(&name.assoc) {
        self.out.func_decls.insert(sym);
      }
    }
  }

  let mut collector = Collector::default();
  stmt.drive(&mut collector);
  collector.out
}

enum UnreachableAction {
  Drop,
  Keep,
  StubVar(Vec<SymbolId>),
}

fn analyze_unreachable_stmt(
  stmt: &Node<Stmt>,
  cx: &OptCtx,
  list_scope: ScopeId,
  var_scope: ScopeId,
) -> UnreachableAction {
  let sem = cx.sem();

  let DeclSymbols {
    declared,
    func_decls,
  } = collect_decl_symbols(stmt);

  let mut effective = declared.clone();
  for sym in declared.iter().copied() {
    if let Some(var_sym) = sem.annex_b_function_decls.get(&sym).copied() {
      effective.insert(var_sym);
    }
  }

  let mut relevant = HashSet::default();
  let mut relevant_in_list_scope = HashSet::default();
  let mut has_tdz = false;

  for sym in effective.iter().copied() {
    let data = sem.symbol(sym);
    if data.decl_scope != list_scope && data.decl_scope != var_scope {
      continue;
    }
    relevant.insert(sym);
    if data.decl_scope == list_scope {
      relevant_in_list_scope.insert(sym);
    }
    if data.flags.tdz {
      has_tdz = true;
    }
  }

  if relevant.is_empty() {
    return UnreachableAction::Drop;
  }

  if has_tdz {
    return UnreachableAction::Keep;
  }

  let mut has_function_like = false;
  for sym in func_decls.iter().copied() {
    let data = sem.symbol(sym);
    if data.decl_scope == list_scope || data.decl_scope == var_scope {
      has_function_like = true;
      break;
    }
  }
  if has_function_like {
    return UnreachableAction::Keep;
  }

  // `var` can only preserve bindings declared in the nearest variable scope. If
  // the statement introduces bindings in the current block scope, we have to
  // keep it verbatim.
  if list_scope != var_scope && !relevant_in_list_scope.is_empty() {
    return UnreachableAction::Keep;
  }

  let mut stub_symbols = Vec::new();
  for sym in relevant.iter().copied() {
    let data = sem.symbol(sym);
    if data.decl_scope != var_scope {
      continue;
    }
    if !data.flags.hoisted || data.flags.tdz {
      return UnreachableAction::Keep;
    }
    if func_decls.contains(&sym) {
      return UnreachableAction::Keep;
    }
    stub_symbols.push(sym);
  }

  if stub_symbols.is_empty() {
    return UnreachableAction::Keep;
  }
  stub_symbols.sort_by_key(|sym| sym.raw());
  stub_symbols.dedup();
  UnreachableAction::StubVar(stub_symbols)
}

fn build_var_stub(
  loc: Loc,
  sem: &semantic_js::js::JsSemantics,
  symbols: &[SymbolId],
) -> Node<Stmt> {
  let mut names: Vec<String> = symbols
    .iter()
    .map(|sym| sem.name(sem.symbol(*sym).name).to_string())
    .collect();
  names.sort();
  names.dedup();

  let declarators: Vec<VarDeclarator> = names
    .into_iter()
    .map(|name| VarDeclarator {
      pattern: Node::new(
        loc,
        PatDecl {
          pat: Node::new(loc, Pat::Id(Node::new(loc, IdPat { name }))),
        },
      ),
      definite_assignment: false,
      type_annotation: None,
      initializer: None,
    })
    .collect();

  Node::new(
    loc,
    Stmt::VarDecl(Node::new(
      loc,
      VarDecl {
        export: false,
        mode: VarDeclMode::Var,
        declarators,
      },
    )),
  )
}

fn rewrite_stmts(
  stmts: Vec<Node<Stmt>>,
  cx: &OptCtx,
  changed: &mut bool,
  in_list: bool,
) -> Vec<Node<Stmt>> {
  let Some(list_scope) = stmts.first().and_then(|stmt| scope_id(&stmt.assoc)) else {
    return stmts;
  };
  let sem = cx.sem();
  let var_scope = nearest_var_scope(sem, list_scope);

  let disabled = cx.disabled_scopes.contains(&list_scope)
    || var_scope.is_some_and(|scope| cx.disabled_scopes.contains(&scope));

  let mut stmts = stmts;
  if !disabled && in_list {
    stmts = drop_terminating_else(stmts, changed);
  }

  if !disabled {
    if let Some(var_scope) = var_scope {
      stmts = trim_unreachable_after_terminator(stmts, cx, list_scope, var_scope, changed);
    }
  }

  stmts
    .into_iter()
    .map(|stmt| rewrite_stmt(stmt, cx, changed))
    .collect()
}

fn drop_terminating_else(stmts: Vec<Node<Stmt>>, changed: &mut bool) -> Vec<Node<Stmt>> {
  let mut out = Vec::with_capacity(stmts.len());
  for stmt in stmts {
    let Node { loc, assoc, stx } = stmt;
    match *stx {
      Stmt::If(mut if_stmt) => {
        let Some(alt) = if_stmt.stx.alternate.take() else {
          out.push(new_node(loc, assoc, Stmt::If(if_stmt)));
          continue;
        };
        if !is_unconditional_terminator(&if_stmt.stx.consequent)
          || matches!(alt.stx.as_ref(), Stmt::FunctionDecl(_))
        {
          if_stmt.stx.alternate = Some(alt);
          out.push(new_node(loc, assoc, Stmt::If(if_stmt)));
          continue;
        }

        *changed = true;
        out.push(new_node(loc, assoc, Stmt::If(if_stmt)));
        out.push(alt);
      }
      other => out.push(new_node(loc, assoc, other)),
    }
  }
  out
}

fn trim_unreachable_after_terminator(
  stmts: Vec<Node<Stmt>>,
  cx: &OptCtx,
  list_scope: ScopeId,
  var_scope: ScopeId,
  changed: &mut bool,
) -> Vec<Node<Stmt>> {
  let mut out = Vec::with_capacity(stmts.len());
  let mut terminated = false;

  for stmt in stmts {
    if !terminated {
      terminated = is_unconditional_terminator(&stmt);
      out.push(stmt);
      continue;
    }

    match analyze_unreachable_stmt(&stmt, cx, list_scope, var_scope) {
      UnreachableAction::Drop => {
        *changed = true;
      }
      UnreachableAction::Keep => out.push(stmt),
      UnreachableAction::StubVar(symbols) => {
        *changed = true;
        out.push(build_var_stub(stmt.loc, cx.sem(), &symbols));
      }
    }
  }

  out
}

fn rewrite_stmt(stmt: Node<Stmt>, cx: &OptCtx, changed: &mut bool) -> Node<Stmt> {
  let Node { loc, assoc, stx } = stmt;
  match *stx {
    Stmt::Block(mut block) => {
      let body = std::mem::take(&mut block.stx.body);
      block.stx.body = rewrite_stmts(body, cx, changed, true);
      new_node(loc, assoc, Stmt::Block(block))
    }
    Stmt::If(mut if_stmt) => {
      if_stmt.stx.consequent = rewrite_stmt(if_stmt.stx.consequent, cx, changed);
      if let Some(alt) = if_stmt.stx.alternate.take() {
        if_stmt.stx.alternate = Some(rewrite_stmt(alt, cx, changed));
      }
      new_node(loc, assoc, Stmt::If(if_stmt))
    }
    Stmt::While(mut while_stmt) => {
      while_stmt.stx.body = rewrite_stmt(while_stmt.stx.body, cx, changed);
      new_node(loc, assoc, Stmt::While(while_stmt))
    }
    Stmt::DoWhile(mut do_stmt) => {
      do_stmt.stx.body = rewrite_stmt(do_stmt.stx.body, cx, changed);
      new_node(loc, assoc, Stmt::DoWhile(do_stmt))
    }
    Stmt::ForTriple(mut for_stmt) => {
      for_stmt.stx.body = rewrite_for_body(for_stmt.stx.body, cx, changed);
      new_node(loc, assoc, Stmt::ForTriple(for_stmt))
    }
    Stmt::ForIn(mut for_stmt) => {
      for_stmt.stx.body = rewrite_for_body(for_stmt.stx.body, cx, changed);
      new_node(loc, assoc, Stmt::ForIn(for_stmt))
    }
    Stmt::ForOf(mut for_stmt) => {
      for_stmt.stx.body = rewrite_for_body(for_stmt.stx.body, cx, changed);
      new_node(loc, assoc, Stmt::ForOf(for_stmt))
    }
    Stmt::Switch(mut switch_stmt) => {
      let branches = std::mem::take(&mut switch_stmt.stx.branches);
      switch_stmt.stx.branches = branches
        .into_iter()
        .map(|branch| rewrite_switch_branch(branch, cx, changed))
        .collect();
      new_node(loc, assoc, Stmt::Switch(switch_stmt))
    }
    Stmt::Try(mut try_stmt) => {
      rewrite_try_stmt(&mut try_stmt, cx, changed);
      new_node(loc, assoc, Stmt::Try(try_stmt))
    }
    Stmt::With(mut with_stmt) => {
      with_stmt.stx.body = rewrite_stmt(with_stmt.stx.body, cx, changed);
      new_node(loc, assoc, Stmt::With(with_stmt))
    }
    Stmt::Label(mut label_stmt) => {
      label_stmt.stx.statement = rewrite_stmt(label_stmt.stx.statement, cx, changed);
      new_node(loc, assoc, Stmt::Label(label_stmt))
    }
    other => new_node(loc, assoc, other),
  }
}

fn rewrite_for_body(mut body: Node<ForBody>, cx: &OptCtx, changed: &mut bool) -> Node<ForBody> {
  let in_list = is_braced_for_body(&body);
  let stmts = std::mem::take(&mut body.stx.body);
  body.stx.body = rewrite_stmts(stmts, cx, changed, in_list);
  body
}

fn rewrite_switch_branch(
  mut branch: Node<SwitchBranch>,
  cx: &OptCtx,
  changed: &mut bool,
) -> Node<SwitchBranch> {
  let stmts = std::mem::take(&mut branch.stx.body);
  branch.stx.body = rewrite_stmts(stmts, cx, changed, true);
  branch
}

fn rewrite_try_stmt(try_stmt: &mut Node<TryStmt>, cx: &OptCtx, changed: &mut bool) {
  let wrapped = std::mem::take(&mut try_stmt.stx.wrapped.stx.body);
  try_stmt.stx.wrapped.stx.body = rewrite_stmts(wrapped, cx, changed, true);

  if let Some(catch) = try_stmt.stx.catch.as_mut() {
    rewrite_catch_block(catch, cx, changed);
  }

  if let Some(finally) = try_stmt.stx.finally.as_mut() {
    let body = std::mem::take(&mut finally.stx.body);
    finally.stx.body = rewrite_stmts(body, cx, changed, true);
  }
}

fn rewrite_catch_block(catch: &mut Node<CatchBlock>, cx: &OptCtx, changed: &mut bool) {
  let body = std::mem::take(&mut catch.stx.body);
  catch.stx.body = rewrite_stmts(body, cx, changed, true);
}
