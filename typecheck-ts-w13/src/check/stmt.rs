use super::body::BodyChecker;
use super::expr::check_expr;
use super::expr::type_from_type_expr;
use super::pat::check_pattern;
use crate::diagnostic::Diagnostic;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::VarDecl;
use parse_js::ast::stmt::CatchBlock;
use parse_js::ast::stmt::ForBody;
use parse_js::ast::stmt::ForInOfLhs;
use parse_js::ast::stmt::ForTripleStmtInit;
use parse_js::ast::stmt::Stmt;

pub(crate) fn check_stmt(ctx: &mut BodyChecker<'_>, stmt: &Node<Stmt>) {
  match stmt.stx.as_ref() {
    Stmt::Expr(expr_stmt) => {
      check_expr(ctx, &expr_stmt.stx.expr, None);
    }
    Stmt::VarDecl(var_decl) => {
      check_var_decl(ctx, var_decl);
    }
    Stmt::Return(ret) => {
      let expected = ctx.expected_return.unwrap_or_else(|| ctx.store.unknown());
      if let Some(value) = &ret.stx.value {
        let actual = check_expr(ctx, value, Some(expected));
        if !ctx.store.is_assignable(actual, expected) {
          ctx.diagnostics.push(Diagnostic::new(
            "TYPE_MISMATCH",
            format!(
              "return type {:?} is not assignable to expected {:?}",
              ctx.store.get(actual),
              ctx.store.get(expected)
            ),
            value.loc,
          ));
        }
      } else if expected != ctx.store.void() {
        ctx.diagnostics.push(Diagnostic::new(
          "TYPE_MISMATCH",
          "missing return value",
          stmt.loc,
        ));
      }
    }
    Stmt::If(if_stmt) => {
      check_expr(ctx, &if_stmt.stx.test, Some(ctx.store.boolean()));
      ctx.push_scope();
      check_stmt(ctx, &if_stmt.stx.consequent);
      ctx.pop_scope();
      if let Some(alt) = &if_stmt.stx.alternate {
        ctx.push_scope();
        check_stmt(ctx, alt);
        ctx.pop_scope();
      }
    }
    Stmt::Block(block) => {
      check_block(ctx, &block.stx.body);
    }
    Stmt::While(while_stmt) => {
      check_expr(ctx, &while_stmt.stx.condition, Some(ctx.store.boolean()));
      ctx.push_scope();
      check_stmt(ctx, &while_stmt.stx.body);
      ctx.pop_scope();
    }
    Stmt::ForTriple(for_stmt) => {
      ctx.push_scope();
      match &for_stmt.stx.init {
        ForTripleStmtInit::Expr(expr) => {
          check_expr(ctx, expr, None);
        }
        ForTripleStmtInit::Decl(decl) => {
          check_var_decl(ctx, decl);
        }
        ForTripleStmtInit::None => {}
      }
      if let Some(cond) = &for_stmt.stx.cond {
        check_expr(ctx, cond, Some(ctx.store.boolean()));
      }
      if let Some(post) = &for_stmt.stx.post {
        check_expr(ctx, post, None);
      }
      check_for_body(ctx, &for_stmt.stx.body);
      ctx.pop_scope();
    }
    Stmt::ForIn(for_stmt) => {
      ctx.push_scope();
      let rhs_ty = check_expr(ctx, &for_stmt.stx.rhs, None);
      match &for_stmt.stx.lhs {
        ForInOfLhs::Assign(pat) => {
          check_pattern(ctx, pat, ctx.store.string());
        }
        ForInOfLhs::Decl((_, pat_decl)) => {
          check_pattern(ctx, &pat_decl.stx.pat, ctx.store.string());
        }
      }
      let _ = rhs_ty;
      check_for_body(ctx, &for_stmt.stx.body);
      ctx.pop_scope();
    }
    Stmt::ForOf(for_stmt) => {
      ctx.push_scope();
      let rhs_ty = check_expr(ctx, &for_stmt.stx.rhs, None);
      let element_ty = match ctx.store.get(rhs_ty) {
        crate::types::Type::Array(elem) => *elem,
        _ => ctx.store.unknown(),
      };
      match &for_stmt.stx.lhs {
        ForInOfLhs::Assign(pat) => {
          check_pattern(ctx, pat, element_ty);
        }
        ForInOfLhs::Decl((_, pat_decl)) => {
          check_pattern(ctx, &pat_decl.stx.pat, element_ty);
        }
      }
      check_for_body(ctx, &for_stmt.stx.body);
      ctx.pop_scope();
    }
    Stmt::Throw(throw_stmt) => {
      check_expr(ctx, &throw_stmt.stx.value, None);
    }
    Stmt::Try(try_stmt) => {
      ctx.push_scope();
      check_block(ctx, &try_stmt.stx.wrapped.stx.body);
      ctx.pop_scope();
      if let Some(catch) = &try_stmt.stx.catch {
        check_catch(ctx, catch);
      }
      if let Some(finally) = &try_stmt.stx.finally {
        ctx.push_scope();
        check_block(ctx, &finally.stx.body);
        ctx.pop_scope();
      }
    }
    Stmt::FunctionDecl(func_decl) => {
      let func_ty = super::expr::check_function(ctx, &func_decl.stx.function, None);
      if let Some(name) = &func_decl.stx.name {
        ctx.define(&name.stx.name, func_ty);
      }
    }
    _ => {}
  }
}

fn check_for_body(ctx: &mut BodyChecker<'_>, body: &Node<ForBody>) {
  ctx.push_scope();
  for stmt in &body.stx.body {
    check_stmt(ctx, stmt);
  }
  ctx.pop_scope();
}

fn check_catch(ctx: &mut BodyChecker<'_>, catch: &Node<CatchBlock>) {
  ctx.push_scope();
  if let Some(param) = &catch.stx.parameter {
    let ty = ctx.store.unknown();
    check_pattern(ctx, &param.stx.pat, ty);
  }
  for stmt in &catch.stx.body {
    check_stmt(ctx, stmt);
  }
  ctx.pop_scope();
}

fn check_var_decl(ctx: &mut BodyChecker<'_>, var_decl: &Node<VarDecl>) {
  for declarator in &var_decl.stx.declarators {
    let annotated = declarator
      .type_annotation
      .as_ref()
      .map(|ty| type_from_type_expr(ctx, ty));
    let init_ty = declarator
      .initializer
      .as_ref()
      .map(|init| check_expr(ctx, init, annotated));
    let pat_ty = annotated.or(init_ty).unwrap_or_else(|| ctx.store.unknown());
    check_pattern(ctx, &declarator.pattern.stx.pat, pat_ty);
  }
}

fn check_block(ctx: &mut BodyChecker<'_>, body: &[Node<Stmt>]) {
  ctx.push_scope();
  for stmt in body {
    check_stmt(ctx, stmt);
  }
  ctx.pop_scope();
}
