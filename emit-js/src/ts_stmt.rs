use crate::emit_interface_decl;
use crate::emit_type_alias_decl;
use crate::emit_type_expr;
use crate::emit_type_members;
use crate::ts_type::emit_type_parameters;
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::*;
use std::fmt;
use std::fmt::Write;

pub fn emit_top_level<W: fmt::Write>(out: &mut W, top: &TopLevel) -> fmt::Result {
  let mut first = true;
  for stmt in &top.body {
    if matches!(stmt.stx.as_ref(), Stmt::Empty(_)) {
      continue;
    }
    if !first {
      out.write_char('\n')?;
    }
    emit_ts_stmt(out, stmt)?;
    first = false;
  }
  Ok(())
}

pub fn emit_ts_stmt<W: fmt::Write>(out: &mut W, stmt: &Node<Stmt>) -> fmt::Result {
  match stmt.stx.as_ref() {
    Stmt::InterfaceDecl(decl) => emit_interface_decl(out, decl.stx.as_ref()),
    Stmt::TypeAliasDecl(decl) => emit_type_alias_decl(out, decl.stx.as_ref()),
    Stmt::EnumDecl(decl) => emit_enum_decl(out, decl.stx.as_ref()),
    Stmt::NamespaceDecl(decl) => emit_namespace_decl(out, decl.stx.as_ref()),
    Stmt::ModuleDecl(decl) => emit_module_decl(out, decl.stx.as_ref()),
    Stmt::GlobalDecl(decl) => emit_global_decl(out, decl.stx.as_ref()),
    Stmt::AmbientVarDecl(decl) => emit_ambient_var_decl(out, decl.stx.as_ref()),
    Stmt::AmbientFunctionDecl(decl) => emit_ambient_function_decl(out, decl.stx.as_ref()),
    Stmt::AmbientClassDecl(decl) => emit_ambient_class_decl(out, decl.stx.as_ref()),
    Stmt::ImportTypeDecl(decl) => emit_import_type_decl(out, decl.stx.as_ref()),
    Stmt::ExportTypeDecl(decl) => emit_export_type_decl(out, decl.stx.as_ref()),
    Stmt::ImportEqualsDecl(decl) => emit_import_equals_decl(out, decl.stx.as_ref()),
    Stmt::ExportAssignmentDecl(decl) => emit_export_assignment_decl(out, decl.stx.as_ref()),
    _ => Err(fmt::Error),
  }
}

fn emit_enum_decl<W: fmt::Write>(out: &mut W, decl: &EnumDecl) -> fmt::Result {
  if decl.export {
    out.write_str("export ")?;
  }
  if decl.declare {
    out.write_str("declare ")?;
  }
  if decl.const_ {
    out.write_str("const ")?;
  }
  out.write_str("enum ")?;
  out.write_str(&decl.name)?;
  out.write_str(" {")?;
  if !decl.members.is_empty() {
    out.write_char(' ')?;
    for (idx, member) in decl.members.iter().enumerate() {
      if idx > 0 {
        out.write_str(", ")?;
      }
      emit_enum_member(out, member.stx.as_ref())?;
    }
    out.write_char(' ')?;
  }
  out.write_char('}')
}

fn emit_enum_member<W: fmt::Write>(out: &mut W, member: &EnumMember) -> fmt::Result {
  out.write_str(&member.name)?;
  if let Some(initializer) = &member.initializer {
    out.write_str(" = ")?;
    emit_ts_expr(out, initializer)?;
  }
  Ok(())
}

fn emit_namespace_decl<W: fmt::Write>(out: &mut W, decl: &NamespaceDecl) -> fmt::Result {
  if decl.export {
    out.write_str("export ")?;
  }
  if decl.declare {
    out.write_str("declare ")?;
  }
  out.write_str("namespace ")?;

  let (names, body) = flatten_namespace(decl);
  for (idx, name) in names.iter().enumerate() {
    if idx > 0 {
      out.write_char('.')?;
    }
    out.write_str(name)?;
  }

  match body {
    NamespaceBody::Block(stmts) => emit_block_like_body(out, stmts),
    NamespaceBody::Namespace(_) => Err(fmt::Error),
  }
}

fn flatten_namespace<'a>(decl: &'a NamespaceDecl) -> (Vec<&'a str>, &'a NamespaceBody) {
  let mut names = Vec::new();
  let mut current = decl;
  loop {
    names.push(current.name.as_str());
    match &current.body {
      NamespaceBody::Namespace(next) => current = next.stx.as_ref(),
      other => return (names, other),
    }
  }
}

fn emit_module_decl<W: fmt::Write>(out: &mut W, decl: &ModuleDecl) -> fmt::Result {
  if decl.export {
    out.write_str("export ")?;
  }
  if decl.declare {
    out.write_str("declare ")?;
  }
  out.write_str("module ")?;
  emit_module_name(out, &decl.name)?;

  if let Some(stmts) = &decl.body {
    emit_block_like_body(out, stmts)?;
  }

  Ok(())
}

fn emit_module_name<W: fmt::Write>(out: &mut W, name: &ModuleName) -> fmt::Result {
  match name {
    ModuleName::Identifier(name) => out.write_str(name),
    ModuleName::String(value) => emit_string_literal(out, value),
  }
}

fn emit_global_decl<W: fmt::Write>(out: &mut W, decl: &GlobalDecl) -> fmt::Result {
  out.write_str("declare global")?;
  emit_block_like_body(out, &decl.body)
}

fn emit_ambient_var_decl<W: fmt::Write>(out: &mut W, decl: &AmbientVarDecl) -> fmt::Result {
  if decl.export {
    out.write_str("export ")?;
  }
  out.write_str("declare var ")?;
  out.write_str(&decl.name)?;
  if let Some(annotation) = &decl.type_annotation {
    out.write_str(": ")?;
    emit_type_expr(out, annotation)?;
  }
  out.write_char(';')
}

fn emit_ambient_function_decl<W: fmt::Write>(
  out: &mut W,
  decl: &AmbientFunctionDecl,
) -> fmt::Result {
  if decl.export {
    out.write_str("export ")?;
  }
  out.write_str("declare function ")?;
  out.write_str(&decl.name)?;

  let mut type_params = String::new();
  emit_type_parameters(&mut type_params, decl.type_parameters.as_deref());
  out.write_str(&type_params)?;

  out.write_char('(')?;
  for (idx, param) in decl.parameters.iter().enumerate() {
    if idx > 0 {
      out.write_str(", ")?;
    }
    emit_ambient_function_param(out, param.stx.as_ref())?;
  }
  out.write_char(')')?;

  if let Some(return_type) = &decl.return_type {
    out.write_str(": ")?;
    emit_type_expr(out, return_type)?;
  }

  out.write_char(';')
}

fn emit_ambient_function_param<W: fmt::Write>(
  out: &mut W,
  param: &AmbientFunctionParameter,
) -> fmt::Result {
  if param.rest {
    out.write_str("...")?;
  }
  out.write_str(&param.name)?;
  if param.optional {
    out.write_char('?')?;
  }
  if let Some(annotation) = &param.type_annotation {
    out.write_str(": ")?;
    emit_type_expr(out, annotation)?;
  }
  Ok(())
}

fn emit_ambient_class_decl<W: fmt::Write>(out: &mut W, decl: &AmbientClassDecl) -> fmt::Result {
  if decl.export {
    out.write_str("export ")?;
  }
  out.write_str("declare ")?;
  if decl.abstract_ {
    out.write_str("abstract ")?;
  }
  out.write_str("class ")?;
  out.write_str(&decl.name)?;

  let mut type_params = String::new();
  emit_type_parameters(&mut type_params, decl.type_parameters.as_deref());
  out.write_str(&type_params)?;

  if let Some(extends) = &decl.extends {
    out.write_str(" extends ")?;
    emit_type_expr(out, extends)?;
  }

  if !decl.implements.is_empty() {
    out.write_str(" implements ")?;
    for (idx, ty) in decl.implements.iter().enumerate() {
      if idx > 0 {
        out.write_str(", ")?;
      }
      emit_type_expr(out, ty)?;
    }
  }

  out.write_str(" {")?;
  if !decl.members.is_empty() {
    out.write_char(' ')?;
    let mut members_buf = String::new();
    emit_type_members(&mut members_buf, &decl.members)?;
    out.write_str(&members_buf)?;
    out.write_char(' ')?;
  }
  out.write_char('}')
}

fn emit_import_type_decl<W: fmt::Write>(out: &mut W, decl: &ImportTypeDecl) -> fmt::Result {
  out.write_str("import type {")?;
  for (idx, name) in decl.names.iter().enumerate() {
    if idx > 0 {
      out.write_str(", ")?;
    }
    out.write_str(&name.imported)?;
    if let Some(local) = &name.local {
      out.write_str(" as ")?;
      out.write_str(local)?;
    }
  }
  out.write_str("} from ")?;
  emit_string_literal(out, &decl.module)?;
  out.write_char(';')
}

fn emit_export_type_decl<W: fmt::Write>(out: &mut W, decl: &ExportTypeDecl) -> fmt::Result {
  out.write_str("export type {")?;
  for (idx, name) in decl.names.iter().enumerate() {
    if idx > 0 {
      out.write_str(", ")?;
    }
    out.write_str(&name.local)?;
    if let Some(exported) = &name.exported {
      out.write_str(" as ")?;
      out.write_str(exported)?;
    }
  }
  out.write_char('}')?;
  if let Some(module) = &decl.module {
    out.write_str(" from ")?;
    emit_string_literal(out, module)?;
  }
  out.write_char(';')
}

fn emit_import_equals_decl<W: fmt::Write>(out: &mut W, decl: &ImportEqualsDecl) -> fmt::Result {
  if decl.export {
    out.write_str("export ")?;
  }
  out.write_str("import ")?;
  out.write_str(&decl.name)?;
  out.write_str(" = ")?;
  match &decl.rhs {
    ImportEqualsRhs::Require { module } => {
      out.write_str("require(")?;
      emit_string_literal(out, module)?;
      out.write_char(')')?;
    }
    ImportEqualsRhs::EntityName { path } => {
      for (idx, seg) in path.iter().enumerate() {
        if idx > 0 {
          out.write_char('.')?;
        }
        out.write_str(seg)?;
      }
    }
  }
  out.write_char(';')
}

fn emit_export_assignment_decl<W: fmt::Write>(
  out: &mut W,
  decl: &ExportAssignmentDecl,
) -> fmt::Result {
  out.write_str("export = ")?;
  emit_ts_expr(out, &decl.expression)?;
  out.write_char(';')
}

fn emit_block_like_body<W: fmt::Write>(out: &mut W, stmts: &[Node<Stmt>]) -> fmt::Result {
  out.write_char(' ')?;
  out.write_char('{')?;
  if !stmts.is_empty() {
    out.write_char(' ')?;
    for (idx, stmt) in stmts.iter().enumerate() {
      if idx > 0 {
        out.write_char(' ')?;
      }
      emit_ts_stmt(out, stmt)?;
    }
    out.write_char(' ')?;
  }
  out.write_char('}')
}

fn emit_string_literal<W: fmt::Write>(out: &mut W, value: &str) -> fmt::Result {
  let mut buf = Vec::new();
  crate::emit_string_literal_double_quoted(&mut buf, value);
  out.write_str(std::str::from_utf8(&buf).expect("string literal escape output is UTF-8"))
}

fn emit_ts_expr<W: fmt::Write>(out: &mut W, expr: &Node<Expr>) -> fmt::Result {
  let mut buf = String::new();
  emit_ts_expr_to_string(&mut buf, expr);
  out.write_str(&buf)
}

fn emit_ts_expr_to_string(out: &mut String, expr: &Node<Expr>) {
  match expr.stx.as_ref() {
    Expr::Id(id) => out.push_str(&id.stx.name),
    Expr::LitStr(lit) => {
      let mut buf = Vec::new();
      crate::emit_string_literal_double_quoted(&mut buf, &lit.stx.value);
      out.push_str(std::str::from_utf8(&buf).expect("string literal escape output is UTF-8"));
    }
    Expr::LitNum(lit) => {
      write!(out, "{}", lit.stx.value).unwrap();
    }
    Expr::LitBool(lit) => out.push_str(if lit.stx.value { "true" } else { "false" }),
    Expr::LitNull(_) => out.push_str("null"),
    Expr::LitBigInt(lit) => out.push_str(&lit.stx.value),
    Expr::This(_) => out.push_str("this"),
    Expr::Member(member) => {
      let member = member.stx.as_ref();
      emit_ts_expr_to_string(out, &member.left);
      if member.optional_chaining {
        out.push_str("?.");
      } else {
        out.push('.');
      }
      out.push_str(&member.right);
    }
    Expr::ComputedMember(member) => {
      let member = member.stx.as_ref();
      emit_ts_expr_to_string(out, &member.object);
      if member.optional_chaining {
        out.push_str("?.");
      }
      out.push('[');
      emit_ts_expr_to_string(out, &member.member);
      out.push(']');
    }
    _ => out.push_str("undefined"),
  }
}
