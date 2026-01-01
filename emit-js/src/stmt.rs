use crate::expr_js::{emit_expr, ExprCtx};
use crate::module_names::{
  emit_module_binding_identifier_or_string_literal, is_module_binding_identifier_token,
};
use crate::ts_type::{emit_ts_type, emit_type_parameters};
use crate::{EmitError, EmitMode, EmitResult, Emitter};
use parse_js::ast::class_or_object::{
  ClassIndexSignature, ClassMember, ClassOrObjKey, ClassOrObjVal,
};
use parse_js::ast::expr::pat::{ArrPat, ClassOrFuncName, IdPat, ObjPat, ObjPatProp, Pat};
use parse_js::ast::expr::{Decorator, Expr};
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::import_export::{
  ExportName, ExportNames, ImportName, ImportNames, ModuleExportImportName,
};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{
  Accessibility, ClassDecl, FuncDecl, ParamDecl, PatDecl, VarDecl, VarDeclMode, VarDeclarator,
};
use parse_js::ast::stmt::*;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::type_expr::{TypeExpr, TypeParameter};
use parse_js::token::TT;

pub fn emit_program(em: &mut Emitter, top: &TopLevel) -> EmitResult {
  emit_stmt_list(em, &top.body)
}

pub fn emit_top_level(em: &mut Emitter, top: &Node<TopLevel>) -> EmitResult {
  emit_stmt_list(em, &top.stx.body)
}

pub fn emit_stmt_list(em: &mut Emitter, stmts: &[Node<Stmt>]) -> EmitResult {
  for stmt in stmts {
    emit_stmt(em, stmt)?;
  }
  Ok(())
}

pub fn emit_stmt(em: &mut Emitter, stmt: &Node<Stmt>) -> EmitResult {
  match stmt.stx.as_ref() {
    Stmt::Block(block) => emit_block(em, block),
    Stmt::Empty(_) => Ok(()),
    Stmt::Expr(expr) => emit_expr_stmt(em, &expr.stx.expr),
    Stmt::If(if_stmt) => emit_if(em, if_stmt),
    Stmt::ForTriple(for_stmt) => emit_for_triple(em, for_stmt),
    Stmt::ForIn(for_stmt) => emit_for_in(em, for_stmt),
    Stmt::ForOf(for_stmt) => emit_for_of(em, for_stmt),
    Stmt::While(while_stmt) => emit_while(em, while_stmt),
    Stmt::DoWhile(do_stmt) => emit_do_while(em, do_stmt),
    Stmt::Switch(switch_stmt) => emit_switch(em, switch_stmt),
    Stmt::Try(try_stmt) => emit_try(em, try_stmt),
    Stmt::Throw(throw_stmt) => emit_throw(em, throw_stmt),
    Stmt::Return(ret_stmt) => emit_return(em, ret_stmt),
    Stmt::Break(brk) => emit_break(em, brk),
    Stmt::Continue(cnt) => emit_continue(em, cnt),
    Stmt::Debugger(_) => {
      em.write_keyword("debugger");
      em.write_punct(";");
      Ok(())
    }
    Stmt::With(with_stmt) => emit_with(em, with_stmt),
    Stmt::Label(label_stmt) => emit_label(em, label_stmt),
    Stmt::VarDecl(decl) => emit_var_decl(em, decl.stx.as_ref(), true),
    Stmt::FunctionDecl(decl) => emit_function_decl(em, decl.stx.as_ref()),
    Stmt::ClassDecl(decl) => emit_class_decl(em, decl),
    Stmt::Import(import_stmt) => emit_import_stmt(em, import_stmt.stx.as_ref()),
    Stmt::ExportList(export_stmt) => emit_export_list_stmt(em, export_stmt.stx.as_ref()),
    Stmt::ExportDefaultExpr(expr) => emit_export_default_expr(em, expr),
    Stmt::InterfaceDecl(_)
    | Stmt::TypeAliasDecl(_)
    | Stmt::EnumDecl(_)
    | Stmt::NamespaceDecl(_)
    | Stmt::ModuleDecl(_)
    | Stmt::GlobalDecl(_)
    | Stmt::AmbientVarDecl(_)
    | Stmt::AmbientFunctionDecl(_)
    | Stmt::AmbientClassDecl(_)
    | Stmt::ImportTypeDecl(_)
    | Stmt::ExportTypeDecl(_)
    | Stmt::ImportEqualsDecl(_)
    | Stmt::ExportAssignmentDecl(_)
    | Stmt::ExportAsNamespaceDecl(_) => Err(EmitError::unsupported("TS-only statement")),
  }
}

fn emit_block(em: &mut Emitter, block: &Node<BlockStmt>) -> EmitResult {
  em.write_punct("{");
  emit_stmt_list(em, &block.stx.body)?;
  em.write_punct("}");
  Ok(())
}

fn emit_expr_stmt(em: &mut Emitter, expr: &Node<Expr>) -> EmitResult {
  if expr_needs_paren_in_stmt(expr) {
    em.write_punct("(");
    emit_expr(em, expr, ExprCtx::Stmt)?;
    em.write_punct(")");
  } else {
    emit_expr(em, expr, ExprCtx::Stmt)?;
  }
  em.write_punct(";");
  Ok(())
}

fn expr_needs_paren_in_stmt(expr: &Node<Expr>) -> bool {
  matches!(
    expr.stx.as_ref(),
    Expr::LitObj(_) | Expr::Func(_) | Expr::Class(_) | Expr::ArrowFunc(_)
  )
}

fn emit_stmt_as_body(em: &mut Emitter, stmt: &Node<Stmt>) -> EmitResult {
  match stmt.stx.as_ref() {
    Stmt::Empty(_) => {
      em.write_punct(";");
      Ok(())
    }
    _ => emit_stmt(em, stmt),
  }
}

fn emit_if(em: &mut Emitter, if_stmt: &Node<IfStmt>) -> EmitResult {
  let if_stmt = if_stmt.stx.as_ref();
  em.write_keyword("if");
  em.write_punct("(");
  emit_expr(em, &if_stmt.test, ExprCtx::Default)?;
  em.write_punct(")");
  emit_stmt_as_body(em, &if_stmt.consequent)?;
  if let Some(alt) = &if_stmt.alternate {
    em.write_keyword("else");
    emit_stmt_as_body(em, alt)?;
  }
  Ok(())
}

fn emit_for_triple(em: &mut Emitter, for_stmt: &Node<ForTripleStmt>) -> EmitResult {
  let for_stmt = for_stmt.stx.as_ref();
  em.write_keyword("for");
  em.write_punct("(");
  match &for_stmt.init {
    ForTripleStmtInit::None => {}
    ForTripleStmtInit::Expr(expr) => {
      if crate::stmt_start::for_init_expr_needs_parens(expr) {
        em.write_punct("(");
        emit_expr(em, expr, ExprCtx::Default)?;
        em.write_punct(")");
      } else {
        emit_expr(em, expr, ExprCtx::Default)?;
      }
    }
    ForTripleStmtInit::Decl(decl) => emit_var_decl(em, decl.stx.as_ref(), false)?,
  }
  em.write_punct(";");
  if let Some(cond) = &for_stmt.cond {
    emit_expr(em, cond, ExprCtx::Default)?;
  }
  em.write_punct(";");
  if let Some(post) = &for_stmt.post {
    emit_expr(em, post, ExprCtx::Default)?;
  }
  em.write_punct(")");
  emit_for_body(em, &for_stmt.body)
}

fn emit_for_in(em: &mut Emitter, for_stmt: &Node<ForInStmt>) -> EmitResult {
  let for_stmt = for_stmt.stx.as_ref();
  em.write_keyword("for");
  em.write_punct("(");
  emit_for_in_of_lhs(em, &for_stmt.lhs)?;
  em.write_keyword("in");
  emit_expr(em, &for_stmt.rhs, ExprCtx::Default)?;
  em.write_punct(")");
  emit_for_body(em, &for_stmt.body)
}

fn emit_for_of(em: &mut Emitter, for_stmt: &Node<ForOfStmt>) -> EmitResult {
  let for_stmt = for_stmt.stx.as_ref();
  em.write_keyword("for");
  if for_stmt.await_ {
    em.write_keyword("await");
  }
  em.write_punct("(");
  emit_for_in_of_lhs(em, &for_stmt.lhs)?;
  em.write_keyword("of");
  emit_expr(em, &for_stmt.rhs, ExprCtx::Default)?;
  em.write_punct(")");
  emit_for_body(em, &for_stmt.body)
}

fn emit_for_in_of_lhs(em: &mut Emitter, lhs: &ForInOfLhs) -> EmitResult {
  match lhs {
    ForInOfLhs::Assign(pat) => {
      if crate::stmt_start::for_inof_assign_needs_parens(pat) {
        em.write_punct("(");
        emit_pat(em, pat)?;
        em.write_punct(")");
        Ok(())
      } else {
        emit_pat(em, pat)
      }
    }
    ForInOfLhs::Decl((mode, decl)) => {
      emit_var_decl_mode(em, *mode);
      emit_pat_decl(em, decl)
    }
  }
}

fn emit_for_body(em: &mut Emitter, body: &Node<ForBody>) -> EmitResult {
  let stmts = &body.stx.body;
  if stmts.len() == 1 {
    emit_stmt_as_body(em, &stmts[0])
  } else {
    em.write_punct("{");
    emit_stmt_list(em, stmts)?;
    em.write_punct("}");
    Ok(())
  }
}

fn emit_while(em: &mut Emitter, while_stmt: &Node<WhileStmt>) -> EmitResult {
  let while_stmt = while_stmt.stx.as_ref();
  em.write_keyword("while");
  em.write_punct("(");
  emit_expr(em, &while_stmt.condition, ExprCtx::Default)?;
  em.write_punct(")");
  emit_stmt_as_body(em, &while_stmt.body)
}

fn emit_do_while(em: &mut Emitter, do_stmt: &Node<DoWhileStmt>) -> EmitResult {
  let do_stmt = do_stmt.stx.as_ref();
  em.write_keyword("do");
  emit_stmt_as_body(em, &do_stmt.body)?;
  em.write_keyword("while");
  em.write_punct("(");
  emit_expr(em, &do_stmt.condition, ExprCtx::Default)?;
  em.write_punct(")");
  em.write_punct(";");
  Ok(())
}

fn emit_switch(em: &mut Emitter, switch_stmt: &Node<SwitchStmt>) -> EmitResult {
  let switch_stmt = switch_stmt.stx.as_ref();
  em.write_keyword("switch");
  em.write_punct("(");
  emit_expr(em, &switch_stmt.test, ExprCtx::Default)?;
  em.write_punct(")");
  em.write_punct("{");
  for branch in &switch_stmt.branches {
    emit_switch_branch(em, branch)?;
  }
  em.write_punct("}");
  Ok(())
}

fn emit_switch_branch(em: &mut Emitter, branch: &Node<SwitchBranch>) -> EmitResult {
  match &branch.stx.case {
    Some(case_expr) => {
      em.write_keyword("case");
      emit_expr(em, case_expr, ExprCtx::Default)?;
    }
    None => em.write_keyword("default"),
  }
  em.write_punct(":");
  for stmt in &branch.stx.body {
    emit_stmt(em, stmt)?;
  }
  Ok(())
}

fn emit_try(em: &mut Emitter, try_stmt: &Node<TryStmt>) -> EmitResult {
  let try_stmt = try_stmt.stx.as_ref();
  em.write_keyword("try");
  emit_block(em, &try_stmt.wrapped)?;
  if let Some(catch) = &try_stmt.catch {
    emit_catch(em, catch)?;
  }
  if let Some(finally) = &try_stmt.finally {
    em.write_keyword("finally");
    emit_block(em, finally)?;
  }
  Ok(())
}

fn emit_catch(em: &mut Emitter, catch: &Node<CatchBlock>) -> EmitResult {
  let catch = catch.stx.as_ref();
  em.write_keyword("catch");
  if let Some(param) = &catch.parameter {
    em.write_punct("(");
    emit_pat_decl(em, param)?;
    if let Some(ty) = &catch.type_annotation {
      emit_type_annotation(em, ty)?;
    }
    em.write_punct(")");
  }
  em.write_punct("{");
  for stmt in &catch.body {
    emit_stmt(em, stmt)?;
  }
  em.write_punct("}");
  Ok(())
}

fn emit_throw(em: &mut Emitter, throw_stmt: &Node<ThrowStmt>) -> EmitResult {
  em.write_keyword("throw");
  emit_expr(em, &throw_stmt.stx.value, ExprCtx::Default)?;
  em.write_punct(";");
  Ok(())
}

fn emit_return(em: &mut Emitter, ret_stmt: &Node<ReturnStmt>) -> EmitResult {
  em.write_keyword("return");
  if let Some(value) = &ret_stmt.stx.value {
    emit_expr(em, value, ExprCtx::Default)?;
  }
  em.write_punct(";");
  Ok(())
}

fn emit_break(em: &mut Emitter, brk: &Node<BreakStmt>) -> EmitResult {
  em.write_keyword("break");
  if let Some(label) = &brk.stx.label {
    em.write_identifier(label);
  }
  em.write_punct(";");
  Ok(())
}

fn emit_continue(em: &mut Emitter, cnt: &Node<ContinueStmt>) -> EmitResult {
  em.write_keyword("continue");
  if let Some(label) = &cnt.stx.label {
    em.write_identifier(label);
  }
  em.write_punct(";");
  Ok(())
}

fn emit_with(em: &mut Emitter, with_stmt: &Node<WithStmt>) -> EmitResult {
  em.write_keyword("with");
  em.write_punct("(");
  emit_expr(em, &with_stmt.stx.object, ExprCtx::Default)?;
  em.write_punct(")");
  emit_stmt_as_body(em, &with_stmt.stx.body)
}

fn emit_label(em: &mut Emitter, label_stmt: &Node<LabelStmt>) -> EmitResult {
  em.write_identifier(&label_stmt.stx.name);
  em.write_punct(":");
  emit_stmt_as_body(em, &label_stmt.stx.statement)
}

fn emit_var_decl(em: &mut Emitter, decl: &VarDecl, trailing_semicolon: bool) -> EmitResult {
  if decl.export {
    em.write_keyword("export");
  }
  emit_var_decl_mode(em, decl.mode);
  for (idx, var) in decl.declarators.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    emit_var_declarator(em, var)?;
  }
  if trailing_semicolon {
    em.write_punct(";");
  }
  Ok(())
}

fn emit_var_decl_mode(em: &mut Emitter, mode: VarDeclMode) {
  match mode {
    VarDeclMode::Const => em.write_keyword("const"),
    VarDeclMode::Let => em.write_keyword("let"),
    VarDeclMode::Var => em.write_keyword("var"),
    VarDeclMode::Using => em.write_keyword("using"),
    VarDeclMode::AwaitUsing => {
      em.write_keyword("await");
      em.write_keyword("using");
    }
  }
}

fn emit_var_declarator(em: &mut Emitter, decl: &VarDeclarator) -> EmitResult {
  emit_pat_decl(em, &decl.pattern)?;
  if decl.definite_assignment {
    em.write_punct("!");
  }
  if let Some(ty) = &decl.type_annotation {
    emit_type_annotation(em, ty)?;
  }
  if let Some(init) = &decl.initializer {
    em.write_punct("=");
    emit_expr(em, init, ExprCtx::Default)?;
  }
  Ok(())
}

fn emit_function_decl(em: &mut Emitter, decl: &FuncDecl) -> EmitResult {
  if decl.export {
    em.write_keyword("export");
  }
  if decl.export_default {
    em.write_keyword("default");
  }
  emit_function(
    em,
    decl.name.as_ref(),
    decl.function.stx.as_ref(),
    /*allow_anonymous=*/ decl.export_default,
  )
}

fn emit_function(
  em: &mut Emitter,
  name: Option<&Node<ClassOrFuncName>>,
  func: &Func,
  allow_anonymous: bool,
) -> EmitResult {
  if func.arrow {
    return Err(EmitError::unsupported("arrow function in declaration"));
  }
  if func.async_ {
    em.write_keyword("async");
  }
  em.write_keyword("function");
  if func.generator {
    em.write_punct("*");
  }
  if let Some(name) = name {
    em.write_identifier(&name.stx.name);
  } else if !allow_anonymous {
    return Err(EmitError::unsupported("named function required"));
  }

  emit_type_params(em, func.type_parameters.as_deref());
  em.write_punct("(");
  for (idx, param) in func.parameters.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    emit_param_decl(em, param)?;
  }
  em.write_punct(")");
  if let Some(ret) = &func.return_type {
    emit_type_annotation(em, ret)?;
  }
  match &func.body {
    Some(body) => emit_func_body(em, body),
    None => {
      em.write_punct(";");
      Ok(())
    }
  }
}

fn emit_func_body(em: &mut Emitter, body: &FuncBody) -> EmitResult {
  match body {
    FuncBody::Block(stmts) => {
      em.write_punct("{");
      for stmt in stmts {
        emit_stmt(em, stmt)?;
      }
      em.write_punct("}");
      Ok(())
    }
    FuncBody::Expression(_) => Err(EmitError::unsupported("expression-bodied function")),
  }
}

pub(crate) fn emit_class_like<T>(
  em: &mut Emitter,
  name: Option<&Node<ClassOrFuncName>>,
  type_parameters: Option<&[Node<TypeParameter>]>,
  extends: Option<&Node<Expr>>,
  implements: &[T],
  mut emit_implements: impl FnMut(&mut Emitter, &T) -> EmitResult,
  members: &[Node<ClassMember>],
  allow_anonymous: bool,
) -> EmitResult {
  em.write_keyword("class");
  if let Some(name) = name {
    em.write_identifier(&name.stx.name);
  } else if !allow_anonymous {
    return Err(EmitError::unsupported("class declaration missing name"));
  }
  emit_type_params(em, type_parameters);
  if let Some(extends) = extends {
    em.write_keyword("extends");
    emit_expr(em, extends, ExprCtx::Default)?;
  }
  if !implements.is_empty() {
    em.write_keyword("implements");
    for (idx, ty) in implements.iter().enumerate() {
      if idx > 0 {
        em.write_punct(",");
      }
      emit_implements(em, ty)?;
    }
  }
  em.write_punct("{");
  for member in members {
    emit_class_member(em, member)?;
  }
  em.write_punct("}");
  Ok(())
}

pub fn emit_class_decl(em: &mut Emitter, decl: &Node<ClassDecl>) -> EmitResult {
  let decl = decl.stx.as_ref();
  emit_decorators(em, &decl.decorators)?;
  if decl.export {
    em.write_keyword("export");
  }
  if decl.export_default {
    em.write_keyword("default");
  }
  if decl.declare {
    em.write_keyword("declare");
  }
  if decl.abstract_ {
    em.write_keyword("abstract");
  }
  emit_class_like(
    em,
    decl.name.as_ref(),
    decl.type_parameters.as_deref(),
    decl.extends.as_ref(),
    &decl.implements,
    |em, ty| emit_expr(em, ty, ExprCtx::Default),
    &decl.members,
    decl.export_default,
  )
}

fn emit_class_member(em: &mut Emitter, member: &Node<ClassMember>) -> EmitResult {
  let member = member.stx.as_ref();
  emit_decorators(em, &member.decorators)?;
  if let Some(accessibility) = &member.accessibility {
    emit_accessibility(em, *accessibility);
  }
  let is_static_block = matches!(member.val, ClassOrObjVal::StaticBlock(_));
  if member.static_ && !is_static_block {
    em.write_keyword("static");
  }
  if member.abstract_ {
    em.write_keyword("abstract");
  }
  if member.override_ {
    em.write_keyword("override");
  }
  if member.accessor {
    em.write_keyword("accessor");
  }
  if member.readonly {
    em.write_keyword("readonly");
  }
  match &member.val {
    ClassOrObjVal::StaticBlock(block) => {
      em.write_keyword("static");
      em.write_punct("{");
      for stmt in &block.stx.body {
        emit_stmt(em, stmt)?;
      }
      em.write_punct("}");
      return Ok(());
    }
    ClassOrObjVal::Getter(get) => {
      em.write_keyword("get");
      emit_class_or_object_key(em, &member.key)?;
      emit_method_like(
        em,
        &get.stx.func,
        member.optional,
        member.definite_assignment,
        member.type_annotation.as_ref(),
      )
    }
    ClassOrObjVal::Setter(set) => {
      em.write_keyword("set");
      emit_class_or_object_key(em, &member.key)?;
      emit_method_like(
        em,
        &set.stx.func,
        member.optional,
        member.definite_assignment,
        member.type_annotation.as_ref(),
      )
    }
    ClassOrObjVal::Method(method) => {
      if method.stx.func.stx.async_ {
        em.write_keyword("async");
      }
      if method.stx.func.stx.generator {
        em.write_punct("*");
      }
      emit_class_or_object_key(em, &member.key)?;
      emit_method_like(
        em,
        &method.stx.func,
        member.optional,
        member.definite_assignment,
        member.type_annotation.as_ref(),
      )
    }
    ClassOrObjVal::Prop(init) => {
      emit_class_or_object_key(em, &member.key)?;
      if member.optional {
        em.write_punct("?");
      }
      if member.definite_assignment {
        em.write_punct("!");
      }
      if let Some(ty) = &member.type_annotation {
        emit_type_annotation(em, ty)?;
      }
      if let Some(init) = init {
        em.write_punct("=");
        emit_expr(em, init, ExprCtx::Default)?;
      }
      em.write_punct(";");
      Ok(())
    }
    ClassOrObjVal::IndexSignature(sig) => emit_class_index_signature(em, sig),
  }
}

fn emit_class_index_signature(em: &mut Emitter, sig: &Node<ClassIndexSignature>) -> EmitResult {
  em.write_punct("[");
  em.write_identifier(&sig.stx.parameter_name);
  em.write_punct(":");
  space_if_canonical(em);
  emit_ts_type(em, &sig.stx.parameter_type)?;
  em.write_punct("]");
  emit_type_annotation(em, &sig.stx.type_annotation)?;
  em.write_punct(";");
  Ok(())
}

fn emit_method_like(
  em: &mut Emitter,
  func: &Node<Func>,
  optional: bool,
  definite: bool,
  type_annotation: Option<&Node<TypeExpr>>,
) -> EmitResult {
  if func.stx.arrow {
    return Err(EmitError::unsupported("arrow function used as method"));
  }
  if optional {
    em.write_punct("?");
  }
  if definite {
    em.write_punct("!");
  }
  emit_type_params(em, func.stx.type_parameters.as_deref());
  em.write_punct("(");
  for (idx, param) in func.stx.parameters.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    emit_param_decl(em, param)?;
  }
  em.write_punct(")");
  if let Some(ty) = type_annotation {
    emit_type_annotation(em, ty)?;
  } else if let Some(ret) = &func.stx.return_type {
    emit_type_annotation(em, ret)?;
  }
  if let Some(body) = &func.stx.body {
    emit_func_body(em, body)
  } else {
    em.write_punct(";");
    Ok(())
  }
}

fn emit_import_stmt(em: &mut Emitter, import: &ImportStmt) -> EmitResult {
  em.write_keyword("import");
  if import.type_only {
    em.write_keyword("type");
  }

  let mut wrote_specifier = false;
  if let Some(default) = &import.default {
    emit_pat_decl(em, default)?;
    wrote_specifier = true;
  }

  if let Some(names) = &import.names {
    if wrote_specifier {
      em.write_punct(",");
    }
    emit_import_names(em, names)?;
    wrote_specifier = true;
  }

  if wrote_specifier {
    em.write_keyword("from");
  }
  emit_string_literal(em, &import.module);
  if let Some(attrs) = &import.attributes {
    em.write_keyword("with");
    emit_expr(em, attrs, ExprCtx::Default)?;
  }
  em.write_punct(";");
  Ok(())
}

fn emit_import_names(em: &mut Emitter, names: &ImportNames) -> EmitResult {
  match names {
    ImportNames::All(alias) => {
      em.write_punct("*");
      em.write_keyword("as");
      emit_pat_decl(em, alias)
    }
    ImportNames::Specific(list) => {
      em.write_punct("{");
      for (idx, name) in list.iter().enumerate() {
        if idx > 0 {
          em.write_punct(",");
        }
        emit_import_name(em, name)?;
      }
      em.write_punct("}");
      Ok(())
    }
  }
}

fn pat_decl_ident_name(decl: &Node<PatDecl>) -> Option<&str> {
  match decl.stx.pat.stx.as_ref() {
    Pat::Id(id) => Some(id.stx.name.as_str()),
    _ => None,
  }
}

fn emit_import_name(em: &mut Emitter, name: &Node<ImportName>) -> EmitResult {
  let name = name.stx.as_ref();
  if name.type_only {
    em.write_keyword("type");
  }
  emit_module_export_import_name(em, &name.importable);
  let alias_name = pat_decl_ident_name(&name.alias);
  // Some imported names require an explicit alias even when the alias matches:
  // - string-literal imported names (`import { "a-b" as ... }`)
  // - imported names that are not valid pattern identifiers (`import { while as ... }`)
  let alias_required = match &name.importable {
    ModuleExportImportName::Str(_) => true,
    ModuleExportImportName::Ident(name) => !is_module_binding_identifier_token(name),
  };
  if alias_required || alias_name != Some(name.importable.as_str()) {
    em.write_keyword("as");
    if let Some(alias_name) = alias_name {
      emit_module_binding_identifier_or_string_literal(em, alias_name);
    } else {
      emit_pat_decl(em, &name.alias)?;
    }
  }
  Ok(())
}

fn emit_export_list_stmt(em: &mut Emitter, export: &ExportListStmt) -> EmitResult {
  em.write_keyword("export");
  if export.type_only {
    em.write_keyword("type");
  }
  match &export.names {
    ExportNames::All(name) => {
      em.write_punct("*");
      if let Some(name) = name {
        em.write_keyword("as");
        emit_module_binding_identifier_or_string_literal(em, &name.stx.name);
      }
    }
    ExportNames::Specific(names) => {
      em.write_punct("{");
      for (idx, name) in names.iter().enumerate() {
        if idx > 0 {
          em.write_punct(",");
        }
        emit_export_name(em, name)?;
      }
      em.write_punct("}");
    }
  }
  if let Some(from) = &export.from {
    em.write_keyword("from");
    emit_string_literal(em, from);
  }
  if let Some(attrs) = &export.attributes {
    em.write_keyword("with");
    emit_expr(em, attrs, ExprCtx::Default)?;
  }
  em.write_punct(";");
  Ok(())
}

fn emit_export_name(em: &mut Emitter, name: &Node<ExportName>) -> EmitResult {
  let name = name.stx.as_ref();
  if name.type_only {
    em.write_keyword("type");
  }
  emit_module_export_import_name(em, &name.exportable);
  // Some exported names require an explicit alias even when the alias matches:
  // - string-literal exported names (`export { "a-b" as ... }`)
  // - exported names that are not valid pattern identifiers (`export { while as ... }`)
  let alias_required = match &name.exportable {
    ModuleExportImportName::Str(_) => true,
    ModuleExportImportName::Ident(name) => !is_module_binding_identifier_token(name),
  };
  if alias_required || name.alias.stx.name != name.exportable.as_str() {
    em.write_keyword("as");
    emit_module_binding_identifier_or_string_literal(em, &name.alias.stx.name);
  }
  Ok(())
}

fn emit_export_default_expr(em: &mut Emitter, stmt: &Node<ExportDefaultExprStmt>) -> EmitResult {
  em.write_keyword("export");
  em.write_keyword("default");
  if expr_needs_paren_in_stmt(&stmt.stx.expression) {
    em.write_punct("(");
    emit_expr(em, &stmt.stx.expression, ExprCtx::ExportDefault)?;
    em.write_punct(")");
  } else {
    emit_expr(em, &stmt.stx.expression, ExprCtx::ExportDefault)?;
  }
  em.write_punct(";");
  Ok(())
}

fn emit_module_export_import_name(em: &mut Emitter, name: &ModuleExportImportName) {
  match name {
    ModuleExportImportName::Ident(id) => em.write_identifier(id),
    ModuleExportImportName::Str(value) => emit_string_literal(em, value),
  }
}

fn space_if_canonical(em: &mut Emitter) {
  if em.mode() == EmitMode::Canonical {
    em.write_space();
  }
}

fn emit_type_annotation(em: &mut Emitter, ty: &Node<TypeExpr>) -> EmitResult {
  em.write_punct(":");
  space_if_canonical(em);
  emit_ts_type(em, ty)
}

fn emit_pat_decl(em: &mut Emitter, decl: &Node<PatDecl>) -> EmitResult {
  emit_pat(em, &decl.stx.pat)
}

fn emit_pat(em: &mut Emitter, pat: &Node<Pat>) -> EmitResult {
  match pat.stx.as_ref() {
    Pat::Arr(arr) => emit_array_pattern(em, arr),
    Pat::Id(id) => emit_id_pat(em, id),
    Pat::Obj(obj) => emit_object_pattern(em, obj),
    Pat::AssignTarget(expr) => emit_expr(em, expr, ExprCtx::Default),
  }
}

fn emit_id_pat(em: &mut Emitter, id: &Node<IdPat>) -> EmitResult {
  em.write_identifier(&id.stx.name);
  Ok(())
}

fn emit_array_pattern(em: &mut Emitter, arr: &Node<ArrPat>) -> EmitResult {
  em.write_punct("[");
  for (idx, elem) in arr.stx.elements.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    if let Some(elem) = elem {
      emit_pat(em, &elem.target)?;
      if let Some(default) = &elem.default_value {
        em.write_punct("=");
        emit_expr(em, default, ExprCtx::Default)?;
      }
    }
  }
  if let Some(rest) = &arr.stx.rest {
    if !arr.stx.elements.is_empty() {
      em.write_punct(",");
    }
    em.write_punct("...");
    emit_pat(em, rest)?;
  }
  em.write_punct("]");
  Ok(())
}

fn emit_object_pattern(em: &mut Emitter, obj: &Node<ObjPat>) -> EmitResult {
  em.write_punct("{");
  for (idx, prop) in obj.stx.properties.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    emit_obj_pat_prop(em, prop)?;
  }
  if let Some(rest) = &obj.stx.rest {
    if !obj.stx.properties.is_empty() {
      em.write_punct(",");
    }
    em.write_punct("...");
    emit_pat(em, rest)?;
  }
  em.write_punct("}");
  Ok(())
}

fn emit_obj_pat_prop(em: &mut Emitter, prop: &Node<ObjPatProp>) -> EmitResult {
  emit_class_or_object_key(em, &prop.stx.key)?;
  if !prop.stx.shorthand {
    em.write_punct(":");
    emit_pat(em, &prop.stx.target)?;
  }
  if let Some(default) = &prop.stx.default_value {
    em.write_punct("=");
    emit_expr(em, default, ExprCtx::Default)?;
  }
  Ok(())
}

fn emit_class_or_object_key(em: &mut Emitter, key: &ClassOrObjKey) -> EmitResult {
  match key {
    ClassOrObjKey::Direct(name) => {
      match name.stx.tt {
        TT::LiteralString => emit_string_literal(em, &name.stx.key),
        TT::LiteralNumber | TT::LiteralNumberBin | TT::LiteralNumberHex | TT::LiteralNumberOct => {
          em.write_number(&name.stx.key)
        }
        tt if tt == TT::Identifier || tt.is_keyword() => em.write_identifier(&name.stx.key),
        _ => em.write_str(&name.stx.key),
      }
      Ok(())
    }
    ClassOrObjKey::Computed(expr) => {
      em.write_punct("[");
      emit_expr(em, expr, ExprCtx::Default)?;
      em.write_punct("]");
      Ok(())
    }
  }
}

fn emit_param_decl(em: &mut Emitter, param: &Node<ParamDecl>) -> EmitResult {
  let param = param.stx.as_ref();
  emit_decorators(em, &param.decorators)?;
  if param.rest {
    em.write_punct("...");
  }
  if let Some(accessibility) = &param.accessibility {
    emit_accessibility(em, *accessibility);
  }
  if param.readonly {
    em.write_keyword("readonly");
  }
  emit_pat_decl(em, &param.pattern)?;
  if param.optional {
    em.write_punct("?");
  }
  if let Some(ty) = &param.type_annotation {
    emit_type_annotation(em, ty)?;
  }
  if let Some(default) = &param.default_value {
    em.write_punct("=");
    emit_expr(em, default, ExprCtx::Default)?;
  }
  Ok(())
}

pub(crate) fn emit_decorators(em: &mut Emitter, decorators: &[Node<Decorator>]) -> EmitResult {
  for deco in decorators {
    em.write_punct("@");
    emit_expr(em, &deco.stx.expression, ExprCtx::Default)?;
    em.write_space();
  }
  Ok(())
}

fn emit_accessibility(em: &mut Emitter, accessibility: Accessibility) {
  match accessibility {
    Accessibility::Public => em.write_keyword("public"),
    Accessibility::Private => em.write_keyword("private"),
    Accessibility::Protected => em.write_keyword("protected"),
  }
}

fn emit_type_params(em: &mut Emitter, params: Option<&[Node<TypeParameter>]>) {
  if let Some(params) = params {
    if params.is_empty() {
      return;
    }
    let mut buf = String::new();
    emit_type_parameters(&mut buf, Some(params));
    em.write_str(&buf);
  }
}

fn emit_comma_separated_exprs(em: &mut Emitter, exprs: &[Node<Expr>]) -> EmitResult {
  for (idx, expr) in exprs.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    emit_expr(em, expr, ExprCtx::Default)?;
  }
  Ok(())
}

fn emit_string_literal(em: &mut Emitter, value: &str) {
  em.write_string_literal(value);
}
