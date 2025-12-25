use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{VarDecl, VarDeclMode};
use parse_js::ast::stmt::BlockStmt;
use parse_js::ast::stmt::BreakStmt;
use parse_js::ast::stmt::ExprStmt;
use parse_js::ast::stmt::ForBody;
use parse_js::ast::stmt::ForTripleStmt;
use parse_js::ast::stmt::ForTripleStmtInit;
use parse_js::ast::stmt::IfStmt;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stmt::WhileStmt;
use parse_js::ast::stx::TopLevel;

use crate::js_expr::{emit_js_expr, JsEmitError, JsEmitResult};
use crate::js_pat::emit_js_pat_decl;
use crate::Emitter;

pub fn emit_js_top_level(out: &mut Emitter, top: &TopLevel) -> JsEmitResult {
  for stmt in &top.body {
    if matches!(stmt.stx.as_ref(), Stmt::Empty(_)) {
      continue;
    }
    emit_js_stmt(out, stmt)?;
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
    Stmt::VarDecl(var_decl) => emit_var_decl(out, var_decl, true, true),
    Stmt::While(while_stmt) => emit_while(out, while_stmt),
    Stmt::Empty(_) => Ok(()),
    _ => Err(JsEmitError::Unsupported("statement kind not supported")),
  }
}

fn emit_block(out: &mut Emitter, block: &Node<BlockStmt>) -> JsEmitResult {
  out.write_punct("{");
  for stmt in &block.stx.body {
    if matches!(stmt.stx.as_ref(), Stmt::Empty(_)) {
      continue;
    }
    emit_js_stmt(out, stmt)?;
  }
  out.write_punct("}");
  Ok(())
}

fn emit_break(out: &mut Emitter, break_stmt: &Node<BreakStmt>) -> JsEmitResult {
  out.write_keyword("break");
  if let Some(label) = &break_stmt.stx.label {
    out.write_identifier(label);
  }
  out.write_punct(";");
  Ok(())
}

fn emit_expr_stmt(out: &mut Emitter, expr_stmt: &Node<ExprStmt>) -> JsEmitResult {
  emit_js_expr(out, &expr_stmt.stx.expr)?;
  out.write_punct(";");
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
    ForTripleStmtInit::Decl(decl) => emit_var_decl(out, decl, false, false),
  }
}

fn emit_for_body(out: &mut Emitter, body: &Node<ForBody>) -> JsEmitResult {
  out.write_punct("{");
  for stmt in &body.stx.body {
    if matches!(stmt.stx.as_ref(), Stmt::Empty(_)) {
      continue;
    }
    emit_js_stmt(out, stmt)?;
  }
  out.write_punct("}");
  Ok(())
}

fn emit_var_decl(
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
    _ => return Err(JsEmitError::Unsupported("unsupported variable declaration mode")),
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
    out.write_punct(";");
  }

  Ok(())
}
