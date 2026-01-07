use super::traverse::apply_to_function_like_bodies;
use super::{OptCtx, Pass};
use parse_js::ast::node::{Node, NodeAssocData};
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stmt::{ForBody, SwitchBranch, TryStmt};
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;

pub(super) struct DeclCombinePass;

impl Pass for DeclCombinePass {
  fn name(&self) -> &'static str {
    "decl-combine"
  }

  fn run(&mut self, _cx: &mut OptCtx, top: &mut Node<TopLevel>) -> bool {
    apply_to_function_like_bodies(top, combine_stmts)
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

fn combine_stmts(stmts: Vec<Node<Stmt>>, changed: &mut bool) -> Vec<Node<Stmt>> {
  let mut out = Vec::with_capacity(stmts.len());
  for stmt in stmts {
    let mut stmt = combine_stmt(stmt, changed);
    if let Some(prev) = out.last_mut() {
      if merge_adjacent_var_decls(prev, &mut stmt) {
        *changed = true;
        continue;
      }
    }
    out.push(stmt);
  }
  out
}

fn merge_adjacent_var_decls(prev: &mut Node<Stmt>, curr: &mut Node<Stmt>) -> bool {
  let (Stmt::VarDecl(prev_decl), Stmt::VarDecl(curr_decl)) = (prev.stx.as_mut(), curr.stx.as_mut())
  else {
    return false;
  };

  if prev_decl.stx.export != curr_decl.stx.export {
    return false;
  }

  if prev_decl.stx.mode != curr_decl.stx.mode {
    return false;
  }

  if matches!(
    prev_decl.stx.mode,
    VarDeclMode::Using | VarDeclMode::AwaitUsing
  ) {
    return false;
  }

  if prev_decl.stx.declarators.is_empty() || curr_decl.stx.declarators.is_empty() {
    return false;
  }

  prev_decl
    .stx
    .declarators
    .append(&mut curr_decl.stx.declarators);
  true
}

fn combine_stmt(stmt: Node<Stmt>, changed: &mut bool) -> Node<Stmt> {
  let Node { loc, assoc, stx } = stmt;
  match *stx {
    Stmt::Block(mut block) => {
      let body = std::mem::take(&mut block.stx.body);
      block.stx.body = combine_stmts(body, changed);
      new_node(loc, assoc, Stmt::Block(block))
    }
    Stmt::If(mut if_stmt) => {
      if_stmt.stx.consequent = combine_single_stmt(if_stmt.stx.consequent, changed);
      if let Some(alt) = if_stmt.stx.alternate.take() {
        if_stmt.stx.alternate = Some(combine_single_stmt(alt, changed));
      }
      new_node(loc, assoc, Stmt::If(if_stmt))
    }
    Stmt::While(mut while_stmt) => {
      while_stmt.stx.body = combine_single_stmt(while_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::While(while_stmt))
    }
    Stmt::DoWhile(mut do_stmt) => {
      do_stmt.stx.body = combine_single_stmt(do_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::DoWhile(do_stmt))
    }
    Stmt::ForTriple(mut for_stmt) => {
      for_stmt.stx.body = combine_for_body(for_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::ForTriple(for_stmt))
    }
    Stmt::ForIn(mut for_stmt) => {
      for_stmt.stx.body = combine_for_body(for_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::ForIn(for_stmt))
    }
    Stmt::ForOf(mut for_stmt) => {
      for_stmt.stx.body = combine_for_body(for_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::ForOf(for_stmt))
    }
    Stmt::Switch(mut switch_stmt) => {
      let branches = std::mem::take(&mut switch_stmt.stx.branches);
      switch_stmt.stx.branches = branches
        .into_iter()
        .map(|branch| combine_switch_branch(branch, changed))
        .collect();
      new_node(loc, assoc, Stmt::Switch(switch_stmt))
    }
    Stmt::Try(mut try_stmt) => {
      combine_try_stmt(&mut try_stmt, changed);
      new_node(loc, assoc, Stmt::Try(try_stmt))
    }
    Stmt::With(mut with_stmt) => {
      with_stmt.stx.body = combine_single_stmt(with_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::With(with_stmt))
    }
    Stmt::Label(mut label_stmt) => {
      label_stmt.stx.statement = combine_single_stmt(label_stmt.stx.statement, changed);
      new_node(loc, assoc, Stmt::Label(label_stmt))
    }
    Stmt::FunctionDecl(decl) => new_node(loc, assoc, Stmt::FunctionDecl(decl)),
    Stmt::ClassDecl(decl) => new_node(loc, assoc, Stmt::ClassDecl(decl)),
    Stmt::VarDecl(decl) => new_node(loc, assoc, Stmt::VarDecl(decl)),
    other => new_node(loc, assoc, other),
  }
}

fn combine_single_stmt(stmt: Node<Stmt>, changed: &mut bool) -> Node<Stmt> {
  combine_stmt(stmt, changed)
}

fn combine_for_body(mut body: Node<ForBody>, changed: &mut bool) -> Node<ForBody> {
  let stmts = std::mem::take(&mut body.stx.body);
  body.stx.body = combine_stmts(stmts, changed);
  body
}

fn combine_switch_branch(mut branch: Node<SwitchBranch>, changed: &mut bool) -> Node<SwitchBranch> {
  let body = std::mem::take(&mut branch.stx.body);
  branch.stx.body = combine_stmts(body, changed);
  branch
}

fn combine_try_stmt(try_stmt: &mut Node<TryStmt>, changed: &mut bool) {
  let wrapped = std::mem::take(&mut try_stmt.stx.wrapped.stx.body);
  try_stmt.stx.wrapped.stx.body = combine_stmts(wrapped, changed);

  if let Some(catch) = try_stmt.stx.catch.as_mut() {
    let body = std::mem::take(&mut catch.stx.body);
    catch.stx.body = combine_stmts(body, changed);
  }

  if let Some(finally) = try_stmt.stx.finally.as_mut() {
    let body = std::mem::take(&mut finally.stx.body);
    finally.stx.body = combine_stmts(body, changed);
  }
}
