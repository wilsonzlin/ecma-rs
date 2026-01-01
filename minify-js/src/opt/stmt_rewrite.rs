use super::{OptCtx, Pass};
use parse_js::ast::class_or_object::{ClassMember, ClassOrObjVal};
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::{BinaryExpr, CondExpr, Expr};
use parse_js::ast::node::{Node, NodeAssocData};
use parse_js::ast::stmt::decl::{PatDecl, VarDecl, VarDeclMode, VarDeclarator};
use parse_js::ast::stmt::{ForBody, ForInOfLhs, ForTripleStmtInit, SwitchBranch};
use parse_js::ast::stmt::{Stmt, TryStmt};
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;

pub(super) struct StmtRewritePass;

impl Pass for StmtRewritePass {
  fn name(&self) -> &'static str {
    "stmt-rewrite"
  }

  fn run(&mut self, _cx: &mut OptCtx, top: &mut Node<TopLevel>) -> bool {
    let mut changed = false;
    let body = std::mem::take(&mut top.stx.body);
    top.stx.body = rewrite_stmts(body, &mut changed);
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

fn rewrite_stmts(stmts: Vec<Node<Stmt>>, changed: &mut bool) -> Vec<Node<Stmt>> {
  let mut out = Vec::with_capacity(stmts.len());
  for stmt in stmts {
    out.extend(rewrite_stmt(stmt, changed, true));
  }
  out
}

fn rewrite_stmt(stmt: Node<Stmt>, changed: &mut bool, in_list: bool) -> Vec<Node<Stmt>> {
  let Node { loc, assoc, stx } = stmt;
  match *stx {
    Stmt::Block(mut block) => {
      let body = std::mem::take(&mut block.stx.body);
      block.stx.body = rewrite_stmts(body, changed);
      vec![new_node(loc, assoc, Stmt::Block(block))]
    }
    Stmt::If(mut if_stmt) => {
      if_stmt.stx.consequent = rewrite_single_stmt(if_stmt.stx.consequent, changed);
      if let Some(alt) = if_stmt.stx.alternate.take() {
        if_stmt.stx.alternate = Some(rewrite_single_stmt(alt, changed));
      }

      if let Some(cond) = const_truthiness(&if_stmt.stx.test) {
        let dead_stmt = if cond {
          if_stmt.stx.alternate.as_ref()
        } else {
          Some(&if_stmt.stx.consequent)
        };

        if dead_stmt.map_or(false, contains_function_decl) {
          // Conservatively keep the statement if we might be dropping hoisted
          // function declarations (Annex B semantics are subtle).
          return vec![new_node(loc, assoc, Stmt::If(if_stmt))];
        }

        let mut hoisted = Vec::new();
        if let Some(dead_stmt) = dead_stmt {
          collect_var_names(dead_stmt, &mut hoisted);
        }

        let live_exists = if cond { true } else { if_stmt.stx.alternate.is_some() };
        if !hoisted.is_empty() && live_exists && !in_list {
          // We need to emit `var ...;` alongside the chosen branch, but we
          // cannot do that in a single-statement position without introducing a
          // new block scope. Skip the rewrite instead.
          return vec![new_node(loc, assoc, Stmt::If(if_stmt))];
        }

        *changed = true;
        let mut out = Vec::new();
        if !hoisted.is_empty() {
          out.push(build_hoisted_var_decl(loc, hoisted));
        }
        if cond {
          out.push(if_stmt.stx.consequent);
        } else if let Some(live_stmt) = if_stmt.stx.alternate {
          out.push(live_stmt);
        }
        return out;
      }

      // `if (cond) a(); else b();` -> `cond ? a() : b();`
      if let Some(alt_stmt) = if_stmt.stx.alternate.take() {
        let cons_stmt = if_stmt.stx.consequent;
        match (stmt_to_expr(cons_stmt), stmt_to_expr(alt_stmt)) {
          (Ok(cons_expr), Ok(alt_expr)) => {
            *changed = true;
            let ternary = Node::new(
              loc,
              Expr::Cond(Node::new(
                loc,
                CondExpr {
                  test: if_stmt.stx.test,
                  consequent: cons_expr,
                  alternate: alt_expr,
                },
              )),
            );
            return vec![new_node(
              loc,
              assoc,
              Stmt::Expr(Node::new(loc, parse_js::ast::stmt::ExprStmt { expr: ternary })),
            )];
          }
          (Err(cons_stmt), Err(alt_stmt)) => {
            if_stmt.stx.consequent = cons_stmt;
            if_stmt.stx.alternate = Some(alt_stmt);
            return vec![new_node(loc, assoc, Stmt::If(if_stmt))];
          }
          (Err(cons_stmt), Ok(alt_expr)) => {
            if_stmt.stx.consequent = cons_stmt;
            if_stmt.stx.alternate = Some(expr_to_stmt(alt_expr));
            return vec![new_node(loc, assoc, Stmt::If(if_stmt))];
          }
          (Ok(cons_expr), Err(alt_stmt)) => {
            if_stmt.stx.consequent = expr_to_stmt(cons_expr);
            if_stmt.stx.alternate = Some(alt_stmt);
            return vec![new_node(loc, assoc, Stmt::If(if_stmt))];
          }
        }
      }

      // `if (cond) stmt;` -> `cond && stmt;` for expression statements.
      let cons_stmt = if_stmt.stx.consequent;
      match stmt_to_expr(cons_stmt) {
        Ok(cons_expr) => {
          *changed = true;
          let and_expr = Node::new(
            loc,
            Expr::Binary(Node::new(
              loc,
              BinaryExpr {
                operator: OperatorName::LogicalAnd,
                left: if_stmt.stx.test,
                right: cons_expr,
              },
            )),
          );
          vec![new_node(
            loc,
            assoc,
            Stmt::Expr(Node::new(loc, parse_js::ast::stmt::ExprStmt { expr: and_expr })),
          )]
        }
        Err(cons_stmt) => {
          if_stmt.stx.consequent = cons_stmt;
          vec![new_node(loc, assoc, Stmt::If(if_stmt))]
        }
      }
    }
    Stmt::While(mut while_stmt) => {
      while_stmt.stx.body = rewrite_single_stmt(while_stmt.stx.body, changed);
      vec![new_node(loc, assoc, Stmt::While(while_stmt))]
    }
    Stmt::DoWhile(mut do_stmt) => {
      do_stmt.stx.body = rewrite_single_stmt(do_stmt.stx.body, changed);
      vec![new_node(loc, assoc, Stmt::DoWhile(do_stmt))]
    }
    Stmt::ForTriple(mut for_stmt) => {
      for_stmt.stx.body = rewrite_for_body(for_stmt.stx.body, changed);
      vec![new_node(loc, assoc, Stmt::ForTriple(for_stmt))]
    }
    Stmt::ForIn(mut for_stmt) => {
      for_stmt.stx.body = rewrite_for_body(for_stmt.stx.body, changed);
      vec![new_node(loc, assoc, Stmt::ForIn(for_stmt))]
    }
    Stmt::ForOf(mut for_stmt) => {
      for_stmt.stx.body = rewrite_for_body(for_stmt.stx.body, changed);
      vec![new_node(loc, assoc, Stmt::ForOf(for_stmt))]
    }
    Stmt::Switch(mut switch_stmt) => {
      let branches = std::mem::take(&mut switch_stmt.stx.branches);
      switch_stmt.stx.branches = branches
        .into_iter()
        .map(|branch| rewrite_switch_branch(branch, changed))
        .collect();
      vec![new_node(loc, assoc, Stmt::Switch(switch_stmt))]
    }
    Stmt::Try(mut try_stmt) => {
      rewrite_try_stmt(&mut try_stmt, changed);
      vec![new_node(loc, assoc, Stmt::Try(try_stmt))]
    }
    Stmt::With(mut with_stmt) => {
      with_stmt.stx.body = rewrite_single_stmt(with_stmt.stx.body, changed);
      vec![new_node(loc, assoc, Stmt::With(with_stmt))]
    }
    Stmt::Label(mut label_stmt) => {
      label_stmt.stx.statement = rewrite_single_stmt(label_stmt.stx.statement, changed);
      vec![new_node(loc, assoc, Stmt::Label(label_stmt))]
    }
    Stmt::FunctionDecl(mut decl) => {
      rewrite_func_body(&mut decl.stx.function, changed);
      vec![new_node(loc, assoc, Stmt::FunctionDecl(decl))]
    }
    Stmt::ClassDecl(mut decl) => {
      for member in decl.stx.members.iter_mut() {
        rewrite_class_member(member, changed);
      }
      vec![new_node(loc, assoc, Stmt::ClassDecl(decl))]
    }
    Stmt::VarDecl(decl) => {
      // Rewrites inside initializers are handled by const folding; keep as-is.
      vec![new_node(loc, assoc, Stmt::VarDecl(decl))]
    }
    other => vec![new_node(loc, assoc, other)],
  }
}

fn rewrite_single_stmt(stmt: Node<Stmt>, changed: &mut bool) -> Node<Stmt> {
  let mut rewritten = rewrite_stmt(stmt, changed, false);
  match rewritten.len() {
    0 => empty_stmt(),
    1 => rewritten.pop().unwrap(),
    _ => {
      debug_assert!(
        false,
        "stmt rewrite unexpectedly produced multiple statements in single-statement position"
      );
      let body = rewritten;
      Node::new(
        Loc(0, 0),
        Stmt::Block(Node::new(Loc(0, 0), parse_js::ast::stmt::BlockStmt { body })),
      )
    }
  }
}

fn rewrite_for_body(mut body: Node<ForBody>, changed: &mut bool) -> Node<ForBody> {
  let stmts = std::mem::take(&mut body.stx.body);
  body.stx.body = rewrite_stmts(stmts, changed);
  body
}

fn rewrite_switch_branch(mut branch: Node<SwitchBranch>, changed: &mut bool) -> Node<SwitchBranch> {
  let body = std::mem::take(&mut branch.stx.body);
  branch.stx.body = rewrite_stmts(body, changed);
  branch
}

fn rewrite_try_stmt(try_stmt: &mut Node<TryStmt>, changed: &mut bool) {
  let wrapped = std::mem::take(&mut try_stmt.stx.wrapped.stx.body);
  try_stmt.stx.wrapped.stx.body = rewrite_stmts(wrapped, changed);
  if let Some(catch) = try_stmt.stx.catch.as_mut() {
    let body = std::mem::take(&mut catch.stx.body);
    catch.stx.body = rewrite_stmts(body, changed);
  }
  if let Some(finally) = try_stmt.stx.finally.as_mut() {
    let body = std::mem::take(&mut finally.stx.body);
    finally.stx.body = rewrite_stmts(body, changed);
  }
}

fn rewrite_func_body(func: &mut Node<parse_js::ast::func::Func>, changed: &mut bool) {
  if let Some(body) = func.stx.body.take() {
    func.stx.body = Some(match body {
      parse_js::ast::func::FuncBody::Block(stmts) => parse_js::ast::func::FuncBody::Block(
        rewrite_stmts(stmts, changed),
      ),
      other => other,
    });
  }
}

fn rewrite_class_member(member: &mut Node<ClassMember>, changed: &mut bool) {
  match &mut member.stx.val {
    ClassOrObjVal::Getter(get) => rewrite_func_body(&mut get.stx.func, changed),
    ClassOrObjVal::Setter(set) => rewrite_func_body(&mut set.stx.func, changed),
    ClassOrObjVal::Method(method) => rewrite_func_body(&mut method.stx.func, changed),
    ClassOrObjVal::StaticBlock(block) => {
      let body = std::mem::take(&mut block.stx.body);
      block.stx.body = rewrite_stmts(body, changed);
    }
    _ => {}
  }
}

fn stmt_to_expr(stmt: Node<Stmt>) -> Result<Node<Expr>, Node<Stmt>> {
  let Node { loc, assoc, stx } = stmt;
  match *stx {
    Stmt::Expr(expr_stmt) => Ok(expr_stmt.stx.expr),
    Stmt::Block(mut block) => {
      if block.stx.body.len() != 1 {
        return Err(new_node(loc, assoc, Stmt::Block(block)));
      }
      let only = block.stx.body.pop().unwrap();
      match stmt_to_expr(only) {
        Ok(expr) => Ok(expr),
        Err(stmt) => Err(new_node(loc, assoc, Stmt::Block(Node::new(loc, parse_js::ast::stmt::BlockStmt { body: vec![stmt] })))),
      }
    }
    other => Err(new_node(loc, assoc, other)),
  }
}

fn expr_to_stmt(expr: Node<Expr>) -> Node<Stmt> {
  let loc = expr.loc;
  Node::new(
    loc,
    Stmt::Expr(Node::new(loc, parse_js::ast::stmt::ExprStmt { expr })),
  )
}

fn const_truthiness(expr: &Node<Expr>) -> Option<bool> {
  match expr.stx.as_ref() {
    Expr::LitBool(b) => Some(b.stx.value),
    Expr::LitNull(_) => Some(false),
    Expr::LitNum(n) => Some(n.stx.value.0 != 0.0 && !n.stx.value.0.is_nan()),
    Expr::LitStr(s) => Some(!s.stx.value.is_empty()),
    Expr::LitBigInt(b) => Some(b.stx.value != "0"),
    _ => None,
  }
}

fn empty_stmt() -> Node<Stmt> {
  Node::new(
    Loc(0, 0),
    Stmt::Empty(Node::new(Loc(0, 0), parse_js::ast::stmt::EmptyStmt {})),
  )
}

fn contains_function_decl(stmt: &Node<Stmt>) -> bool {
  match stmt.stx.as_ref() {
    Stmt::FunctionDecl(_) => true,
    Stmt::Block(block) => block.stx.body.iter().any(contains_function_decl),
    Stmt::If(if_stmt) => {
      contains_function_decl(&if_stmt.stx.consequent)
        || if_stmt
          .stx
          .alternate
          .as_ref()
          .map_or(false, contains_function_decl)
    }
    Stmt::ForTriple(for_stmt) => for_stmt.stx.body.stx.body.iter().any(contains_function_decl),
    Stmt::ForIn(for_stmt) => for_stmt.stx.body.stx.body.iter().any(contains_function_decl),
    Stmt::ForOf(for_stmt) => for_stmt.stx.body.stx.body.iter().any(contains_function_decl),
    Stmt::While(while_stmt) => contains_function_decl(&while_stmt.stx.body),
    Stmt::DoWhile(do_stmt) => contains_function_decl(&do_stmt.stx.body),
    Stmt::Switch(switch_stmt) => switch_stmt
      .stx
      .branches
      .iter()
      .any(|b| b.stx.body.iter().any(contains_function_decl)),
    Stmt::Try(try_stmt) => {
      try_stmt.stx.wrapped.stx.body.iter().any(contains_function_decl)
        || try_stmt
          .stx
          .catch
          .as_ref()
          .map_or(false, |c| c.stx.body.iter().any(contains_function_decl))
        || try_stmt
          .stx
          .finally
          .as_ref()
          .map_or(false, |f| f.stx.body.iter().any(contains_function_decl))
    }
    Stmt::With(with_stmt) => contains_function_decl(&with_stmt.stx.body),
    Stmt::Label(label_stmt) => contains_function_decl(&label_stmt.stx.statement),
    _ => false,
  }
}

fn collect_var_names(stmt: &Node<Stmt>, out: &mut Vec<String>) {
  match stmt.stx.as_ref() {
    Stmt::VarDecl(decl) if decl.stx.mode == VarDeclMode::Var => {
      for declarator in decl.stx.declarators.iter() {
        collect_pat_names(&declarator.pattern.stx.pat, out);
      }
    }
    Stmt::ForTriple(for_stmt) => {
      if let ForTripleStmtInit::Decl(decl) = &for_stmt.stx.init {
        if decl.stx.mode == VarDeclMode::Var {
          for declarator in decl.stx.declarators.iter() {
            collect_pat_names(&declarator.pattern.stx.pat, out);
          }
        }
      }
      for stmt in for_stmt.stx.body.stx.body.iter() {
        collect_var_names(stmt, out);
      }
    }
    Stmt::ForIn(for_stmt) => {
      if let ForInOfLhs::Decl((VarDeclMode::Var, pat)) = &for_stmt.stx.lhs {
        collect_pat_names(&pat.stx.pat, out);
      }
      for stmt in for_stmt.stx.body.stx.body.iter() {
        collect_var_names(stmt, out);
      }
    }
    Stmt::ForOf(for_stmt) => {
      if let ForInOfLhs::Decl((VarDeclMode::Var, pat)) = &for_stmt.stx.lhs {
        collect_pat_names(&pat.stx.pat, out);
      }
      for stmt in for_stmt.stx.body.stx.body.iter() {
        collect_var_names(stmt, out);
      }
    }
    Stmt::Block(block) => {
      for stmt in block.stx.body.iter() {
        collect_var_names(stmt, out);
      }
    }
    Stmt::If(if_stmt) => {
      collect_var_names(&if_stmt.stx.consequent, out);
      if let Some(alt) = if_stmt.stx.alternate.as_ref() {
        collect_var_names(alt, out);
      }
    }
    Stmt::While(while_stmt) => collect_var_names(&while_stmt.stx.body, out),
    Stmt::DoWhile(do_stmt) => collect_var_names(&do_stmt.stx.body, out),
    Stmt::Switch(switch_stmt) => {
      for branch in switch_stmt.stx.branches.iter() {
        for stmt in branch.stx.body.iter() {
          collect_var_names(stmt, out);
        }
      }
    }
    Stmt::Try(try_stmt) => {
      for stmt in try_stmt.stx.wrapped.stx.body.iter() {
        collect_var_names(stmt, out);
      }
      if let Some(catch) = try_stmt.stx.catch.as_ref() {
        for stmt in catch.stx.body.iter() {
          collect_var_names(stmt, out);
        }
      }
      if let Some(finally) = try_stmt.stx.finally.as_ref() {
        for stmt in finally.stx.body.iter() {
          collect_var_names(stmt, out);
        }
      }
    }
    Stmt::With(with_stmt) => collect_var_names(&with_stmt.stx.body, out),
    Stmt::Label(label_stmt) => collect_var_names(&label_stmt.stx.statement, out),
    Stmt::FunctionDecl(_) | Stmt::ClassDecl(_) => {
      // Do not descend into nested closures / class bodies.
    }
    _ => {}
  }
}

fn collect_pat_names(pat: &Node<Pat>, out: &mut Vec<String>) {
  match pat.stx.as_ref() {
    Pat::Id(id) => push_unique(out, &id.stx.name),
    Pat::Arr(arr) => {
      for elem in arr.stx.elements.iter() {
        if let Some(elem) = elem {
          collect_pat_names(&elem.target, out);
        }
      }
      if let Some(rest) = arr.stx.rest.as_ref() {
        collect_pat_names(rest, out);
      }
    }
    Pat::Obj(obj) => {
      for prop in obj.stx.properties.iter() {
        collect_pat_names(&prop.stx.target, out);
      }
      if let Some(rest) = obj.stx.rest.as_ref() {
        collect_pat_names(rest, out);
      }
    }
    Pat::AssignTarget(_) => {}
  }
}

fn push_unique(out: &mut Vec<String>, name: &str) {
  if !out.iter().any(|existing| existing == name) {
    out.push(name.to_string());
  }
}

fn build_hoisted_var_decl(loc: Loc, names: Vec<String>) -> Node<Stmt> {
  let declarators = names
    .into_iter()
    .map(|name| VarDeclarator {
      pattern: Node::new(
        loc,
        PatDecl {
          pat: Node::new(
            loc,
            Pat::Id(Node::new(
              loc,
              parse_js::ast::expr::pat::IdPat { name },
            )),
          ),
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
