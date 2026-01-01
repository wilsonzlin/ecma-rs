use super::{OptCtx, Pass};
use parse_js::ast::class_or_object::{ClassMember, ClassOrObjVal};
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::{Node, NodeAssocData};
use parse_js::ast::stmt::{ForBody, SwitchBranch, TryStmt};
use parse_js::ast::stmt::{Stmt};
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;

pub(super) struct CleanupPass;

impl Pass for CleanupPass {
  fn name(&self) -> &'static str {
    "cleanup"
  }

  fn run(&mut self, _cx: &mut OptCtx, top: &mut Node<TopLevel>) -> bool {
    let mut changed = false;
    let body = std::mem::take(&mut top.stx.body);
    top.stx.body = clean_stmts(body, &mut changed);
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

fn clean_stmts(stmts: Vec<Node<Stmt>>, changed: &mut bool) -> Vec<Node<Stmt>> {
  let mut out = Vec::with_capacity(stmts.len());
  for stmt in stmts {
    if let Some(stmt) = clean_stmt_in_list(stmt, changed) {
      out.push(stmt);
    }
  }
  out
}

fn clean_stmt_in_list(stmt: Node<Stmt>, changed: &mut bool) -> Option<Node<Stmt>> {
  let stmt = clean_stmt(stmt, changed);
  match stmt.stx.as_ref() {
    Stmt::Empty(_) => {
      *changed = true;
      None
    }
    Stmt::Block(block) if block.stx.body.is_empty() => {
      *changed = true;
      None
    }
    Stmt::VarDecl(decl) if decl.stx.declarators.is_empty() => {
      *changed = true;
      None
    }
    _ => Some(stmt),
  }
}

fn clean_single_stmt(stmt: Node<Stmt>, changed: &mut bool) -> Node<Stmt> {
  let stmt = clean_stmt(stmt, changed);
  match stmt.stx.as_ref() {
    Stmt::Block(block) if block.stx.body.is_empty() => {
      *changed = true;
      empty_stmt()
    }
    Stmt::VarDecl(decl) if decl.stx.declarators.is_empty() => {
      *changed = true;
      empty_stmt()
    }
    _ => stmt,
  }
}

fn clean_stmt(stmt: Node<Stmt>, changed: &mut bool) -> Node<Stmt> {
  let Node { loc, assoc, stx } = stmt;
  match *stx {
    Stmt::Block(mut block) => {
      let body = std::mem::take(&mut block.stx.body);
      block.stx.body = clean_stmts(body, changed);
      new_node(loc, assoc, Stmt::Block(block))
    }
    Stmt::If(mut if_stmt) => {
      if_stmt.stx.consequent = clean_single_stmt(if_stmt.stx.consequent, changed);
      if let Some(alt) = if_stmt.stx.alternate.take() {
        if_stmt.stx.alternate = Some(clean_single_stmt(alt, changed));
      }
      new_node(loc, assoc, Stmt::If(if_stmt))
    }
    Stmt::While(mut while_stmt) => {
      while_stmt.stx.body = clean_single_stmt(while_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::While(while_stmt))
    }
    Stmt::DoWhile(mut do_stmt) => {
      do_stmt.stx.body = clean_single_stmt(do_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::DoWhile(do_stmt))
    }
    Stmt::ForTriple(mut for_stmt) => {
      for_stmt.stx.body = clean_for_body(for_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::ForTriple(for_stmt))
    }
    Stmt::ForIn(mut for_stmt) => {
      for_stmt.stx.body = clean_for_body(for_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::ForIn(for_stmt))
    }
    Stmt::ForOf(mut for_stmt) => {
      for_stmt.stx.body = clean_for_body(for_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::ForOf(for_stmt))
    }
    Stmt::Switch(mut switch_stmt) => {
      let branches = std::mem::take(&mut switch_stmt.stx.branches);
      switch_stmt.stx.branches = branches
        .into_iter()
        .map(|branch| clean_switch_branch(branch, changed))
        .collect();
      new_node(loc, assoc, Stmt::Switch(switch_stmt))
    }
    Stmt::Try(mut try_stmt) => {
      clean_try_stmt(&mut try_stmt, changed);
      new_node(loc, assoc, Stmt::Try(try_stmt))
    }
    Stmt::With(mut with_stmt) => {
      with_stmt.stx.body = clean_single_stmt(with_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::With(with_stmt))
    }
    Stmt::Label(mut label_stmt) => {
      label_stmt.stx.statement = clean_single_stmt(label_stmt.stx.statement, changed);
      new_node(loc, assoc, Stmt::Label(label_stmt))
    }
    Stmt::FunctionDecl(mut decl) => {
      clean_func(&mut decl.stx.function, changed);
      new_node(loc, assoc, Stmt::FunctionDecl(decl))
    }
    Stmt::ClassDecl(mut decl) => {
      for member in decl.stx.members.iter_mut() {
        clean_class_member(member, changed);
      }
      new_node(loc, assoc, Stmt::ClassDecl(decl))
    }
    other => new_node(loc, assoc, other),
  }
}

fn clean_for_body(mut body: Node<ForBody>, changed: &mut bool) -> Node<ForBody> {
  let stmts = std::mem::take(&mut body.stx.body);
  body.stx.body = clean_stmts(stmts, changed);
  body
}

fn clean_switch_branch(mut branch: Node<SwitchBranch>, changed: &mut bool) -> Node<SwitchBranch> {
  let body = std::mem::take(&mut branch.stx.body);
  branch.stx.body = clean_stmts(body, changed);
  branch
}

fn clean_try_stmt(try_stmt: &mut Node<TryStmt>, changed: &mut bool) {
  let body = std::mem::take(&mut try_stmt.stx.wrapped.stx.body);
  try_stmt.stx.wrapped.stx.body = clean_stmts(body, changed);

  if let Some(catch) = try_stmt.stx.catch.as_mut() {
    let catch_body = std::mem::take(&mut catch.stx.body);
    catch.stx.body = clean_stmts(catch_body, changed);
  }

  if let Some(finally) = try_stmt.stx.finally.as_mut() {
    let finally_body = std::mem::take(&mut finally.stx.body);
    finally.stx.body = clean_stmts(finally_body, changed);
  }
}

fn clean_func(func: &mut Node<Func>, changed: &mut bool) {
  if let Some(body) = func.stx.body.take() {
    func.stx.body = Some(match body {
      FuncBody::Block(stmts) => FuncBody::Block(clean_stmts(stmts, changed)),
      other => other,
    });
  }
}

fn clean_class_member(member: &mut Node<ClassMember>, changed: &mut bool) {
  match &mut member.stx.val {
    ClassOrObjVal::Getter(get) => clean_func(&mut get.stx.func, changed),
    ClassOrObjVal::Setter(set) => clean_func(&mut set.stx.func, changed),
    ClassOrObjVal::Method(method) => clean_func(&mut method.stx.func, changed),
    ClassOrObjVal::StaticBlock(block) => {
      let body = std::mem::take(&mut block.stx.body);
      block.stx.body = clean_stmts(body, changed);
    }
    _ => {}
  }
}

fn empty_stmt() -> Node<Stmt> {
  Node::new(
    Loc(0, 0),
    Stmt::Empty(Node::new(Loc(0, 0), parse_js::ast::stmt::EmptyStmt {})),
  )
}

