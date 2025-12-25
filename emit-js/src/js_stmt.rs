//! JavaScript statement emitter for the `emit_js_*` helpers.
//!
//! When `EmitOptions.stmt_sep_style` is `StmtSepStyle::AsiNewlines`, statement
//! lists use newlines and rely on automatic semicolon insertion, only emitting
//! explicit semicolons for hazards (e.g. statements starting with `/`, `[`, or
//! `(` after an expression-like statement).

use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{VarDecl, VarDeclMode};
use parse_js::ast::stmt::{
  BlockStmt, BreakStmt, ExprStmt, ForBody, ForTripleStmt, ForTripleStmtInit, IfStmt, Stmt,
  WhileStmt,
};
use parse_js::ast::stx::TopLevel;

use crate::asi::separator_between;
use crate::asi::Separator;
use crate::js_expr::{emit_js_expr, JsEmitError, JsEmitResult};
use crate::js_pat::emit_js_pat_decl;
use crate::{Emitter, StmtSepStyle};

pub fn emit_js_top_level(out: &mut Emitter, top: &TopLevel) -> JsEmitResult {
  emit_js_stmt_list(out, &top.body)
}

pub fn emit_js_stmt_list(out: &mut Emitter, stmts: &[Node<Stmt>]) -> JsEmitResult {
  let style = out.options().stmt_sep_style;
  let mut prev: Option<&Node<Stmt>> = None;

  for stmt in stmts {
    if matches!(stmt.stx.as_ref(), Stmt::Empty(_)) {
      continue;
    }

    if style == StmtSepStyle::AsiNewlines {
      match separator_between(prev, stmt) {
        Separator::None => {}
        Separator::Newline => out.write_newline(),
        Separator::Semicolon => out.write_semicolon(),
      }
    }

    emit_js_stmt(out, stmt)?;
    prev = Some(stmt);
  }

  Ok(())
}

pub fn emit_js_stmt(out: &mut Emitter, stmt: &Node<Stmt>) -> JsEmitResult {
  match stmt.stx.as_ref() {
    Stmt::Block(block) => emit_block(out, block),
    Stmt::Break(break_stmt) => emit_break(out, break_stmt),
    Stmt::Expr(expr) => emit_expr_stmt(out, expr),
    Stmt::ForTriple(for_stmt) => emit_for_triple(out, for_stmt),
    Stmt::If(if_stmt) => emit_if(out, if_stmt),
    Stmt::VarDecl(var_decl) => emit_var_decl(out, var_decl),
    Stmt::While(while_stmt) => emit_while(out, while_stmt),
    Stmt::Empty(_) => Ok(()),
    _ => Err(JsEmitError::Unsupported("statement kind not supported")),
  }
}

fn emit_block(out: &mut Emitter, block: &Node<BlockStmt>) -> JsEmitResult {
  out.write_punct("{");
  emit_js_stmt_list(out, &block.stx.body)?;
  out.write_punct("}");
  Ok(())
}

fn emit_break(out: &mut Emitter, break_stmt: &Node<BreakStmt>) -> JsEmitResult {
  out.write_keyword("break");
  if let Some(label) = &break_stmt.stx.label {
    out.write_identifier(label);
  }
  if out.options().stmt_sep_style == StmtSepStyle::Semicolons {
    out.write_semicolon();
  }
  Ok(())
}

fn emit_expr_stmt(out: &mut Emitter, expr_stmt: &Node<ExprStmt>) -> JsEmitResult {
  emit_js_expr(out, &expr_stmt.stx.expr)?;
  if out.options().stmt_sep_style == StmtSepStyle::Semicolons {
    out.write_semicolon();
  }
  Ok(())
}

fn emit_if(out: &mut Emitter, if_stmt: &Node<IfStmt>) -> JsEmitResult {
  out.write_keyword("if");
  out.write_punct("(");
  emit_js_expr(out, &if_stmt.stx.test)?;
  out.write_punct(")");
  emit_stmt_as_block(out, &if_stmt.stx.consequent)?;
  if let Some(alternate) = &if_stmt.stx.alternate {
    out.write_keyword("else");
    emit_stmt_as_block(out, alternate)?;
  }
  Ok(())
}

fn emit_stmt_as_block(out: &mut Emitter, stmt: &Node<Stmt>) -> JsEmitResult {
  match stmt.stx.as_ref() {
    Stmt::Block(block) => emit_block(out, block),
    _ => {
      out.write_punct("{");
      emit_js_stmt(out, stmt)?;
      out.write_punct("}");
      Ok(())
    }
  }
}

fn emit_while(out: &mut Emitter, while_stmt: &Node<WhileStmt>) -> JsEmitResult {
  out.write_keyword("while");
  out.write_punct("(");
  emit_js_expr(out, &while_stmt.stx.condition)?;
  out.write_punct(")");
  emit_stmt_as_block(out, &while_stmt.stx.body)
}

fn emit_for_triple(out: &mut Emitter, for_stmt: &Node<ForTripleStmt>) -> JsEmitResult {
  out.write_keyword("for");
  out.write_punct("(");
  emit_for_triple_init(out, &for_stmt.stx.init)?;
  out.write_punct(";");
  if let Some(cond) = &for_stmt.stx.cond {
    emit_js_expr(out, cond)?;
  }
  out.write_punct(";");
  if let Some(post) = &for_stmt.stx.post {
    emit_js_expr(out, post)?;
  }
  out.write_punct(")");
  emit_for_body(out, &for_stmt.stx.body)
}

fn emit_for_triple_init(out: &mut Emitter, init: &ForTripleStmtInit) -> JsEmitResult {
  match init {
    ForTripleStmtInit::None => Ok(()),
    ForTripleStmtInit::Expr(expr) => emit_js_expr(out, expr),
    ForTripleStmtInit::Decl(decl) => emit_var_decl_inner(out, decl, false, false),
  }
}

fn emit_for_body(out: &mut Emitter, body: &Node<ForBody>) -> JsEmitResult {
  out.write_punct("{");
  emit_js_stmt_list(out, &body.stx.body)?;
  out.write_punct("}");
  Ok(())
}

fn emit_var_decl(out: &mut Emitter, decl: &Node<VarDecl>) -> JsEmitResult {
  let trailing_semi = out.options().stmt_sep_style == StmtSepStyle::Semicolons;
  emit_var_decl_inner(out, decl, trailing_semi, true)
}

fn emit_var_decl_inner(
  out: &mut Emitter,
  decl: &Node<VarDecl>,
  trailing_semi: bool,
  allow_export: bool,
) -> JsEmitResult {
  if decl.stx.export && !allow_export {
    return Err(JsEmitError::Unsupported("export not allowed here"));
  }

  if decl.stx.export {
    out.write_keyword("export");
  }

  let keyword = match decl.stx.mode {
    VarDeclMode::Var => "var",
    VarDeclMode::Let => "let",
    VarDeclMode::Const => "const",
    _ => {
      return Err(JsEmitError::Unsupported(
        "unsupported variable declaration mode",
      ))
    }
  };
  out.write_keyword(keyword);
  for (idx, declarator) in decl.stx.declarators.iter().enumerate() {
    if idx > 0 {
      out.write_punct(",");
    }

    emit_js_pat_decl(out, &declarator.pattern)?;
    if let Some(init) = &declarator.initializer {
      out.write_punct("=");
      emit_js_expr(out, init)?;
    }
  }

  if trailing_semi {
    out.write_semicolon();
  }

  Ok(())
}
