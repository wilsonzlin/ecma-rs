use crate::emitter::{with_node_context, EmitError, EmitErrorKind, EmitMode, EmitResult, Emitter};
use crate::ts_type::emit_type_parameters;
use crate::{emit_interface_decl, emit_type_alias_decl, emit_type_expr, emit_type_members};
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::*;
use parse_js::ast::type_expr::TypeExpr;

pub fn emit_top_level(em: &mut Emitter, top: &TopLevel) -> EmitResult {
  let mut first = true;
  for stmt in &top.body {
    if matches!(stmt.stx.as_ref(), Stmt::Empty(_)) {
      continue;
    }
    if !first {
      em.write_byte(b'\n');
    }
    emit_ts_stmt(em, stmt)?;
    first = false;
  }
  Ok(())
}

pub fn emit_ts_stmt(em: &mut Emitter, stmt: &Node<Stmt>) -> EmitResult {
  with_node_context(stmt.loc, || match stmt.stx.as_ref() {
    Stmt::InterfaceDecl(decl) => {
      emit_interface_decl(em, decl.stx.as_ref()).map_err(EmitError::from)
    }
    Stmt::TypeAliasDecl(decl) => {
      emit_type_alias_decl(em, decl.stx.as_ref()).map_err(EmitError::from)
    }
    Stmt::EnumDecl(decl) => emit_enum_decl(em, decl.stx.as_ref()),
    Stmt::NamespaceDecl(decl) => emit_namespace_decl(em, decl.stx.as_ref()),
    Stmt::ModuleDecl(decl) => emit_module_decl(em, decl.stx.as_ref()),
    Stmt::GlobalDecl(decl) => emit_global_decl(em, decl.stx.as_ref()),
    Stmt::AmbientVarDecl(decl) => emit_ambient_var_decl(em, decl.stx.as_ref()),
    Stmt::AmbientFunctionDecl(decl) => emit_ambient_function_decl(em, decl.stx.as_ref()),
    Stmt::AmbientClassDecl(decl) => emit_ambient_class_decl(em, decl.stx.as_ref()),
    Stmt::ImportTypeDecl(decl) => emit_import_type_decl(em, decl.stx.as_ref()),
    Stmt::ExportTypeDecl(decl) => emit_export_type_decl(em, decl.stx.as_ref()),
    Stmt::ImportEqualsDecl(decl) => emit_import_equals_decl(em, decl.stx.as_ref()),
    Stmt::ExportAssignmentDecl(decl) => emit_export_assignment_decl(em, decl.stx.as_ref()),
    _ => Err(EmitError::unsupported("unsupported TS statement")),
  })
}

fn emit_enum_decl(em: &mut Emitter, decl: &EnumDecl) -> EmitResult {
  if decl.export {
    em.write_keyword("export");
  }
  if decl.declare {
    em.write_keyword("declare");
  }
  if decl.const_ {
    em.write_keyword("const");
  }
  em.write_keyword("enum");
  em.write_identifier(&decl.name);
  space_if_canonical(em);
  em.write_punct("{");
  if !decl.members.is_empty() {
    space_if_canonical(em);
    for (idx, member) in decl.members.iter().enumerate() {
      if idx > 0 {
        em.write_punct(",");
        space_if_canonical(em);
      }
      emit_enum_member(em, member.stx.as_ref())?;
    }
    space_if_canonical(em);
  }
  em.write_punct("}");
  Ok(())
}

fn emit_enum_member(em: &mut Emitter, member: &EnumMember) -> EmitResult {
  em.write_identifier(&member.name);
  if let Some(initializer) = &member.initializer {
    em.write_punct("=");
    space_if_canonical(em);
    emit_ts_expr(em, initializer)?;
  }
  Ok(())
}

fn emit_namespace_decl(em: &mut Emitter, decl: &NamespaceDecl) -> EmitResult {
  if decl.export {
    em.write_keyword("export");
  }
  if decl.declare {
    em.write_keyword("declare");
  }
  em.write_keyword("namespace");

  let (names, body) = flatten_namespace(decl);
  for (idx, name) in names.iter().enumerate() {
    if idx > 0 {
      em.write_punct(".");
    }
    em.write_identifier(name);
  }

  match body {
    NamespaceBody::Block(stmts) => emit_block_like_body(em, stmts),
    NamespaceBody::Namespace(_) => {
      Err(EmitError::unsupported("nested namespace flattening failed"))
    }
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

fn emit_module_decl(em: &mut Emitter, decl: &ModuleDecl) -> EmitResult {
  if decl.export {
    em.write_keyword("export");
  }
  if decl.declare {
    em.write_keyword("declare");
  }
  em.write_keyword("module");
  em.write_space();
  emit_module_name(em, &decl.name)?;

  if let Some(stmts) = &decl.body {
    emit_block_like_body(em, stmts)?;
  }

  Ok(())
}

fn emit_module_name(em: &mut Emitter, name: &ModuleName) -> EmitResult {
  match name {
    ModuleName::Identifier(name) => {
      em.write_identifier(name);
      Ok(())
    }
    ModuleName::String(value) => emit_string_literal(em, value),
  }
}

fn emit_global_decl(em: &mut Emitter, decl: &GlobalDecl) -> EmitResult {
  em.write_keyword("declare");
  em.write_space();
  em.write_keyword("global");
  emit_block_like_body(em, &decl.body)
}

fn emit_ambient_var_decl(em: &mut Emitter, decl: &AmbientVarDecl) -> EmitResult {
  if decl.export {
    em.write_keyword("export");
  }
  em.write_keyword("declare");
  em.write_keyword("var");
  em.write_identifier(&decl.name);
  if let Some(annotation) = &decl.type_annotation {
    em.write_punct(":");
    space_if_canonical(em);
    emit_type_expr(em, annotation).map_err(EmitError::from)?;
  }
  em.write_punct(";");
  Ok(())
}

fn emit_ambient_function_decl(em: &mut Emitter, decl: &AmbientFunctionDecl) -> EmitResult {
  if decl.export {
    em.write_keyword("export");
  }
  em.write_keyword("declare");
  em.write_keyword("function");
  em.write_identifier(&decl.name);

  if decl.type_parameters.is_some() {
    let mut type_params = String::new();
    emit_type_parameters(&mut type_params, decl.type_parameters.as_deref());
    em.write_str(&type_params);
  }

  em.write_punct("(");
  for (idx, param) in decl.parameters.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
      space_if_canonical(em);
    }
    emit_ambient_function_param(em, param.stx.as_ref())?;
  }
  em.write_punct(")");

  if let Some(return_type) = &decl.return_type {
    em.write_punct(":");
    space_if_canonical(em);
    emit_type_expr(em, return_type).map_err(EmitError::from)?;
  }

  em.write_punct(";");
  Ok(())
}

fn emit_ambient_function_param(em: &mut Emitter, param: &AmbientFunctionParameter) -> EmitResult {
  if param.rest {
    em.write_punct("...");
  }
  em.write_identifier(&param.name);
  if param.optional {
    em.write_punct("?");
  }
  if let Some(annotation) = &param.type_annotation {
    em.write_punct(":");
    space_if_canonical(em);
    emit_type_expr(em, annotation).map_err(EmitError::from)?;
  }
  Ok(())
}

fn emit_ambient_class_decl(em: &mut Emitter, decl: &AmbientClassDecl) -> EmitResult {
  if decl.export {
    em.write_keyword("export");
  }
  em.write_keyword("declare");
  if decl.abstract_ {
    em.write_keyword("abstract");
  }
  em.write_keyword("class");
  em.write_identifier(&decl.name);

  if decl.type_parameters.is_some() {
    let mut type_params = String::new();
    emit_type_parameters(&mut type_params, decl.type_parameters.as_deref());
    em.write_str(&type_params);
  }

  if let Some(extends) = &decl.extends {
    em.write_keyword("extends");
    emit_type_expr(em, extends).map_err(EmitError::from)?;
  }

  if !decl.implements.is_empty() {
    em.write_keyword("implements");
    for (idx, ty) in decl.implements.iter().enumerate() {
      if idx > 0 {
        em.write_punct(",");
        space_if_canonical(em);
      }
      emit_type_expr(em, ty).map_err(EmitError::from)?;
    }
  }

  space_if_canonical(em);
  em.write_punct("{");
  if !decl.members.is_empty() {
    space_if_canonical(em);
    emit_type_members(em, &decl.members).map_err(EmitError::from)?;
    space_if_canonical(em);
  }
  em.write_punct("}");
  Ok(())
}

fn emit_import_type_decl(em: &mut Emitter, decl: &ImportTypeDecl) -> EmitResult {
  em.write_keyword("import");
  em.write_keyword("type");
  space_if_canonical(em);
  em.write_punct("{");
  if !decl.names.is_empty() {
    for (idx, name) in decl.names.iter().enumerate() {
      if idx > 0 {
        em.write_punct(",");
        space_if_canonical(em);
      }
      em.write_identifier(&name.imported);
      if let Some(local) = &name.local {
        em.write_keyword("as");
        em.write_identifier(local);
      }
    }
  }
  em.write_punct("}");
  space_if_canonical(em);
  em.write_keyword("from");
  space_if_canonical(em);
  emit_string_literal(em, &decl.module)?;
  em.write_punct(";");
  Ok(())
}

fn emit_export_type_decl(em: &mut Emitter, decl: &ExportTypeDecl) -> EmitResult {
  em.write_keyword("export");
  em.write_keyword("type");
  space_if_canonical(em);
  em.write_punct("{");
  if !decl.names.is_empty() {
    for (idx, name) in decl.names.iter().enumerate() {
      if idx > 0 {
        em.write_punct(",");
        space_if_canonical(em);
      }
      em.write_identifier(&name.local);
      if let Some(exported) = &name.exported {
        em.write_keyword("as");
        em.write_identifier(exported);
      }
    }
  }
  em.write_punct("}");
  if let Some(module) = &decl.module {
    space_if_canonical(em);
    em.write_keyword("from");
    space_if_canonical(em);
    emit_string_literal(em, module)?;
  }
  em.write_punct(";");
  Ok(())
}

fn emit_import_equals_decl(em: &mut Emitter, decl: &ImportEqualsDecl) -> EmitResult {
  if decl.export {
    em.write_keyword("export");
  }
  em.write_keyword("import");
  em.write_identifier(&decl.name);
  space_if_canonical(em);
  em.write_punct("=");
  space_if_canonical(em);
  match &decl.rhs {
    ImportEqualsRhs::Require { module } => {
      em.write_keyword("require");
      em.write_punct("(");
      emit_string_literal(em, module)?;
      em.write_punct(")");
    }
    ImportEqualsRhs::EntityName { path } => {
      for (idx, seg) in path.iter().enumerate() {
        if idx > 0 {
          em.write_punct(".");
        }
        em.write_identifier(seg);
      }
    }
  }
  em.write_punct(";");
  Ok(())
}

fn emit_export_assignment_decl(em: &mut Emitter, decl: &ExportAssignmentDecl) -> EmitResult {
  em.write_keyword("export");
  space_if_canonical(em);
  em.write_punct("=");
  space_if_canonical(em);
  emit_ts_expr(em, &decl.expression)?;
  em.write_punct(";");
  Ok(())
}

fn emit_block_like_body(em: &mut Emitter, stmts: &[Node<Stmt>]) -> EmitResult {
  if em.mode() == EmitMode::Canonical {
    em.write_space();
    em.write_punct("{");
    if !stmts.is_empty() {
      em.write_space();
      for (idx, stmt) in stmts.iter().enumerate() {
        if idx > 0 {
          em.write_space();
        }
        match emit_ts_stmt(em, stmt) {
          Ok(()) => {}
          Err(EmitError {
            kind: EmitErrorKind::Unsupported(_),
            ..
          }) => crate::stmt::emit_stmt(em, stmt)?,
          Err(other) => return Err(other),
        }
      }
      em.write_space();
    }
    em.write_punct("}");
  } else {
    em.write_punct("{");
    for (idx, stmt) in stmts.iter().enumerate() {
      if idx > 0 {
        em.write_space();
      }
      match emit_ts_stmt(em, stmt) {
        Ok(()) => {}
        Err(EmitError {
          kind: EmitErrorKind::Unsupported(_),
          ..
        }) => crate::stmt::emit_stmt(em, stmt)?,
        Err(other) => return Err(other),
      }
    }
    em.write_punct("}");
  }
  Ok(())
}

fn emit_string_literal(em: &mut Emitter, value: &str) -> EmitResult {
  em.write_string_literal(value);
  Ok(())
}

fn emit_ts_expr(em: &mut Emitter, expr: &Node<Expr>) -> EmitResult {
  let mut emit_type = |out: &mut Emitter, ty: &Node<TypeExpr>| emit_type_expr(out, ty);
  match crate::expr::emit_expr_with_options(em, expr, &mut emit_type, em.options()) {
    Ok(()) => Ok(()),
    Err(_) => emit_ts_expr_minimal(em, expr),
  }
}

fn emit_ts_expr_minimal(em: &mut Emitter, expr: &Node<Expr>) -> EmitResult {
  match expr.stx.as_ref() {
    Expr::Id(id) => em.write_identifier(&id.stx.name),
    Expr::LitStr(lit) => emit_string_literal(em, &lit.stx.value)?,
    Expr::LitNum(lit) => em.write_number(&format!("{}", lit.stx.value)),
    Expr::LitBool(lit) => em.write_keyword(if lit.stx.value { "true" } else { "false" }),
    Expr::LitNull(_) => em.write_keyword("null"),
    Expr::LitBigInt(lit) => em.write_number(&lit.stx.value),
    Expr::This(_) => em.write_keyword("this"),
    Expr::Member(member) => {
      let member = member.stx.as_ref();
      emit_ts_expr_minimal(em, &member.left)?;
      if member.optional_chaining {
        em.write_punct("?.");
      } else {
        em.write_punct(".");
      }
      em.write_identifier(&member.right);
    }
    Expr::ComputedMember(member) => {
      let member = member.stx.as_ref();
      emit_ts_expr_minimal(em, &member.object)?;
      if member.optional_chaining {
        em.write_punct("?.");
      }
      em.write_punct("[");
      emit_ts_expr_minimal(em, &member.member)?;
      em.write_punct("]");
    }
    _ => em.write_keyword("undefined"),
  }
  Ok(())
}

fn space_if_canonical(em: &mut Emitter) {
  if em.mode() == EmitMode::Canonical {
    em.write_space();
  }
}
