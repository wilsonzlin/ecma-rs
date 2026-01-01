use super::side_effects::is_side_effect_free_expr;
use super::{OptCtx, Pass};
use ahash::HashSet;
use derive_visitor::{Drive, Visitor};
use parse_js::ast::class_or_object::{ClassMember, ClassOrObjVal};
use parse_js::ast::expr::pat::{IdPat, Pat};
use parse_js::ast::expr::IdExpr;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::{Node, NodeAssocData};
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::{ForBody, SwitchBranch, TryStmt};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use semantic_js::assoc::js::{declared_symbol, resolved_symbol};
use semantic_js::js::SymbolId;

pub(super) struct DcePass;

impl Pass for DcePass {
  fn name(&self) -> &'static str {
    "dce"
  }

  fn run(&mut self, cx: &mut OptCtx, top: &mut Node<TopLevel>) -> bool {
    let mut used = collect_used_symbols(top);
    // Exported symbols are always considered used.
    used.extend(cx.usage().exported.iter().copied());

    let mut changed = false;
    let body = std::mem::take(&mut top.stx.body);
    top.stx.body = dce_stmts(body, cx, &used, &mut changed);
    changed
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

fn collect_used_symbols(top: &Node<TopLevel>) -> HashSet<SymbolId> {
  type IdExprNode = Node<IdExpr>;
  type IdPatNode = Node<IdPat>;

  #[derive(Default, Visitor)]
  #[visitor(IdExprNode(enter), IdPatNode(enter))]
  struct UseCollector {
    used: HashSet<SymbolId>,
  }

  impl UseCollector {
    fn enter_id_expr_node(&mut self, node: &IdExprNode) {
      if let Some(sym) = resolved_symbol(&node.assoc) {
        self.used.insert(sym);
      }
    }

    fn enter_id_pat_node(&mut self, node: &IdPatNode) {
      if declared_symbol(&node.assoc).is_some() {
        return;
      }
      if let Some(sym) = resolved_symbol(&node.assoc) {
        self.used.insert(sym);
      }
    }
  }

  let mut collector = UseCollector::default();
  top.drive(&mut collector);
  collector.used
}

fn dce_stmts(
  stmts: Vec<Node<Stmt>>,
  cx: &OptCtx,
  used: &HashSet<SymbolId>,
  changed: &mut bool,
) -> Vec<Node<Stmt>> {
  stmts
    .into_iter()
    .map(|stmt| dce_stmt(stmt, cx, used, changed))
    .collect()
}

fn dce_stmt(stmt: Node<Stmt>, cx: &OptCtx, used: &HashSet<SymbolId>, changed: &mut bool) -> Node<Stmt> {
  let Node { loc, assoc, stx } = stmt;
  match *stx {
    Stmt::Block(mut block) => {
      let body = std::mem::take(&mut block.stx.body);
      block.stx.body = dce_stmts(body, cx, used, changed);
      new_node(loc, assoc, Stmt::Block(block))
    }
    Stmt::If(mut if_stmt) => {
      if_stmt.stx.consequent = dce_stmt(if_stmt.stx.consequent, cx, used, changed);
      if let Some(alt) = if_stmt.stx.alternate.take() {
        if_stmt.stx.alternate = Some(dce_stmt(alt, cx, used, changed));
      }
      new_node(loc, assoc, Stmt::If(if_stmt))
    }
    Stmt::While(mut while_stmt) => {
      while_stmt.stx.body = dce_stmt(while_stmt.stx.body, cx, used, changed);
      new_node(loc, assoc, Stmt::While(while_stmt))
    }
    Stmt::DoWhile(mut do_stmt) => {
      do_stmt.stx.body = dce_stmt(do_stmt.stx.body, cx, used, changed);
      new_node(loc, assoc, Stmt::DoWhile(do_stmt))
    }
    Stmt::ForTriple(mut for_stmt) => {
      for_stmt.stx.body = dce_for_body(for_stmt.stx.body, cx, used, changed);
      new_node(loc, assoc, Stmt::ForTriple(for_stmt))
    }
    Stmt::ForIn(mut for_stmt) => {
      for_stmt.stx.body = dce_for_body(for_stmt.stx.body, cx, used, changed);
      new_node(loc, assoc, Stmt::ForIn(for_stmt))
    }
    Stmt::ForOf(mut for_stmt) => {
      for_stmt.stx.body = dce_for_body(for_stmt.stx.body, cx, used, changed);
      new_node(loc, assoc, Stmt::ForOf(for_stmt))
    }
    Stmt::Switch(mut switch_stmt) => {
      let branches = std::mem::take(&mut switch_stmt.stx.branches);
      switch_stmt.stx.branches = branches
        .into_iter()
        .map(|branch| dce_switch_branch(branch, cx, used, changed))
        .collect();
      new_node(loc, assoc, Stmt::Switch(switch_stmt))
    }
    Stmt::Try(mut try_stmt) => {
      dce_try_stmt(&mut try_stmt, cx, used, changed);
      new_node(loc, assoc, Stmt::Try(try_stmt))
    }
    Stmt::With(mut with_stmt) => {
      with_stmt.stx.body = dce_stmt(with_stmt.stx.body, cx, used, changed);
      new_node(loc, assoc, Stmt::With(with_stmt))
    }
    Stmt::Label(mut label_stmt) => {
      label_stmt.stx.statement = dce_stmt(label_stmt.stx.statement, cx, used, changed);
      new_node(loc, assoc, Stmt::Label(label_stmt))
    }
    Stmt::FunctionDecl(mut decl) => {
      dce_func(&mut decl.stx.function, cx, used, changed);
      new_node(loc, assoc, Stmt::FunctionDecl(decl))
    }
    Stmt::ClassDecl(mut decl) => {
      for member in decl.stx.members.iter_mut() {
        dce_class_member(member, cx, used, changed);
      }
      new_node(loc, assoc, Stmt::ClassDecl(decl))
    }
    Stmt::VarDecl(mut decl) => {
      if decl.stx.export || matches!(decl.stx.mode, VarDeclMode::Using | VarDeclMode::AwaitUsing)
      {
        return new_node(loc, assoc, Stmt::VarDecl(decl));
      }
      let mut kept = Vec::with_capacity(decl.stx.declarators.len());
      for declarator in decl.stx.declarators.into_iter() {
        if should_keep_declarator(&declarator.pattern.stx.pat, declarator.initializer.as_ref(), cx, used) {
          kept.push(declarator);
        } else {
          *changed = true;
        }
      }
      decl.stx.declarators = kept;
      new_node(loc, assoc, Stmt::VarDecl(decl))
    }
    other => new_node(loc, assoc, other),
  }
}

fn should_keep_declarator(
  pat: &Node<Pat>,
  initializer: Option<&Node<parse_js::ast::expr::Expr>>,
  cx: &OptCtx,
  used: &HashSet<SymbolId>,
) -> bool {
  let Pat::Id(id) = pat.stx.as_ref() else {
    return true;
  };
  let Some(sym) = declared_symbol(&id.assoc) else {
    return true;
  };
  if used.contains(&sym) {
    return true;
  }
  if cx.disabled_scopes.contains(&cx.sem().symbol(sym).decl_scope) {
    return true;
  }
  match initializer {
    None => false,
    Some(expr) => !is_side_effect_free_expr(expr),
  }
}

fn dce_for_body(
  mut body: Node<ForBody>,
  cx: &OptCtx,
  used: &HashSet<SymbolId>,
  changed: &mut bool,
) -> Node<ForBody> {
  let stmts = std::mem::take(&mut body.stx.body);
  body.stx.body = dce_stmts(stmts, cx, used, changed);
  body
}

fn dce_switch_branch(
  mut branch: Node<SwitchBranch>,
  cx: &OptCtx,
  used: &HashSet<SymbolId>,
  changed: &mut bool,
) -> Node<SwitchBranch> {
  let stmts = std::mem::take(&mut branch.stx.body);
  branch.stx.body = dce_stmts(stmts, cx, used, changed);
  branch
}

fn dce_try_stmt(try_stmt: &mut Node<TryStmt>, cx: &OptCtx, used: &HashSet<SymbolId>, changed: &mut bool) {
  let wrapped = std::mem::take(&mut try_stmt.stx.wrapped.stx.body);
  try_stmt.stx.wrapped.stx.body = dce_stmts(wrapped, cx, used, changed);

  if let Some(catch) = try_stmt.stx.catch.as_mut() {
    let body = std::mem::take(&mut catch.stx.body);
    catch.stx.body = dce_stmts(body, cx, used, changed);
  }

  if let Some(finally) = try_stmt.stx.finally.as_mut() {
    let body = std::mem::take(&mut finally.stx.body);
    finally.stx.body = dce_stmts(body, cx, used, changed);
  }
}

fn dce_func(func: &mut Node<Func>, cx: &OptCtx, used: &HashSet<SymbolId>, changed: &mut bool) {
  if let Some(body) = func.stx.body.take() {
    func.stx.body = Some(match body {
      FuncBody::Block(stmts) => FuncBody::Block(dce_stmts(stmts, cx, used, changed)),
      other => other,
    });
  }
}

fn dce_class_member(member: &mut Node<ClassMember>, cx: &OptCtx, used: &HashSet<SymbolId>, changed: &mut bool) {
  match &mut member.stx.val {
    ClassOrObjVal::Getter(get) => dce_func(&mut get.stx.func, cx, used, changed),
    ClassOrObjVal::Setter(set) => dce_func(&mut set.stx.func, cx, used, changed),
    ClassOrObjVal::Method(method) => dce_func(&mut method.stx.func, cx, used, changed),
    ClassOrObjVal::StaticBlock(block) => {
      let body = std::mem::take(&mut block.stx.body);
      block.stx.body = dce_stmts(body, cx, used, changed);
    }
    _ => {}
  }
}
