use super::traverse::apply_to_function_like_bodies;
use super::{OptCtx, Pass};
use parse_js::ast::expr::Expr;
use parse_js::ast::import_export::ExportNames;
use parse_js::ast::node::{Node, NodeAssocData, ParenthesizedExpr};
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stmt::{BlockStmt, ExportListStmt, ForBody, ImportStmt, SwitchBranch, TryStmt};
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;

pub(super) struct CleanupPass;

impl Pass for CleanupPass {
  fn name(&self) -> &'static str {
    "cleanup"
  }

  fn run(&mut self, _cx: &mut OptCtx, top: &mut Node<TopLevel>) -> bool {
    apply_to_function_like_bodies(top, clean_stmts)
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
    append_cleaned_in_list(stmt, &mut out, changed);
  }
  out
}

fn append_cleaned_in_list(stmt: Node<Stmt>, out: &mut Vec<Node<Stmt>>, changed: &mut bool) {
  let stmt = clean_stmt(stmt, changed);
  match stmt.stx.as_ref() {
    Stmt::Empty(_) => {
      *changed = true;
    }
    Stmt::Block(block) if block.stx.body.is_empty() => {
      *changed = true;
    }
    Stmt::Block(block) if can_unwrap_block(block, /* in_list */ true) => {
      // Safe bare-block unwrap: splice the cleaned body into the parent list.
      *changed = true;
      let Node { stx, .. } = stmt;
      let Stmt::Block(block) = *stx else {
        unreachable!("matched Stmt::Block above");
      };
      out.extend(block.stx.body);
    }
    Stmt::VarDecl(decl) if decl.stx.declarators.is_empty() => {
      *changed = true;
    }
    _ => out.push(stmt),
  }
}

fn clean_single_stmt(stmt: Node<Stmt>, changed: &mut bool) -> Node<Stmt> {
  let stmt = clean_stmt(stmt, changed);
  match stmt.stx.as_ref() {
    Stmt::Block(block) if block.stx.body.is_empty() => {
      *changed = true;
      empty_stmt()
    }
    // `if (t) { stmt; }` → `if (t) stmt;` when the block introduces no scope and
    // has exactly one statement (multi-statement bodies must keep the braces).
    Stmt::Block(block)
      if block.stx.body.len() == 1 && can_unwrap_block(block, /* in_list */ false) =>
    {
      *changed = true;
      let Node { stx, .. } = stmt;
      let Stmt::Block(mut block) = *stx else {
        unreachable!("matched Stmt::Block above");
      };
      block.stx.body.pop().expect("len == 1")
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
    Stmt::ExportList(export_stmt)
      if export_stmt.stx.from.is_some()
        && !export_stmt.stx.type_only
        && matches!(export_stmt.stx.names, ExportNames::Specific(ref names) if names.is_empty()) =>
    {
      *changed = true;
      let Node {
        loc: inner_loc,
        assoc: inner_assoc,
        stx: export_stmt,
      } = export_stmt;
      let ExportListStmt {
        from, attributes, ..
      } = *export_stmt;
      let import_stmt = Node {
        loc: inner_loc,
        assoc: inner_assoc,
        stx: Box::new(ImportStmt {
          type_only: false,
          default: None,
          names: None,
          module: from.expect("guarded by is_some"),
          attributes,
        }),
      };
      new_node(loc, assoc, Stmt::Import(import_stmt))
    }
    Stmt::FunctionDecl(decl) => new_node(loc, assoc, Stmt::FunctionDecl(decl)),
    Stmt::ClassDecl(decl) => new_node(loc, assoc, Stmt::ClassDecl(decl)),
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

/// Whether a bare `{ … }` may be flattened into its parent.
///
/// Refuse when the block introduces block-scoped bindings (`let`/`const`/`class`/
/// `using`/`await using`), contains a function declaration (Annex B block-function
/// hoisting differs from a bare `function` in if/sloppy contexts), or — in list
/// position — starts with a string-literal expression statement (which would be
/// promoted into the parent's directive prologue and can flip sloppy→strict).
fn can_unwrap_block(block: &Node<BlockStmt>, in_list: bool) -> bool {
  if block.stx.body.is_empty() {
    return false;
  }
  if in_list && has_leading_string_literal_expr(&block.stx.body) {
    return false;
  }
  !block_body_has_scope_bindings(&block.stx.body)
}

fn block_body_has_scope_bindings(stmts: &[Node<Stmt>]) -> bool {
  stmts.iter().any(stmt_introduces_block_scope_binding)
}

fn stmt_introduces_block_scope_binding(stmt: &Node<Stmt>) -> bool {
  match stmt.stx.as_ref() {
    // `var` is function-scoped; unwrapping does not change its binding contour.
    Stmt::VarDecl(decl) => !matches!(decl.stx.mode, VarDeclMode::Var),
    Stmt::ClassDecl(_) | Stmt::FunctionDecl(_) => true,
    // Labels do not create a scope; a labeled lexical/function still belongs to
    // the enclosing block and must keep that block intact.
    Stmt::Label(label) => stmt_introduces_block_scope_binding(&label.stx.statement),
    _ => false,
  }
}

fn has_leading_string_literal_expr(stmts: &[Node<Stmt>]) -> bool {
  let Some(first) = stmts.first() else {
    return false;
  };
  let Stmt::Expr(expr_stmt) = first.stx.as_ref() else {
    return false;
  };
  // Parenthesized string literals are never directives.
  if expr_stmt
    .stx
    .expr
    .assoc
    .get::<ParenthesizedExpr>()
    .is_some()
  {
    return false;
  }
  matches!(expr_stmt.stx.expr.stx.as_ref(), Expr::LitStr(_))
}

fn empty_stmt() -> Node<Stmt> {
  Node::new(
    Loc(0, 0),
    Stmt::Empty(Node::new(Loc(0, 0), parse_js::ast::stmt::EmptyStmt {})),
  )
}
