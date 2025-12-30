use crate::escape::{emit_regex_literal, emit_string_literal, emit_template_literal_segment};
use crate::precedence::{
  child_min_prec_for_binary, needs_parens, Prec, ARROW_FUNCTION_PRECEDENCE, CALL_MEMBER_PRECEDENCE,
  PRIMARY_PRECEDENCE,
};
use crate::{EmitError, EmitOptions, EmitResult, Emitter};
use diagnostics::Diagnostic;
use hir_js::{
  AssignOp, BinaryOp, Body, BodyId, DefData, DefId, Export, ExportAll, ExportDefault,
  ExportDefaultValue, ExportKind, ExportNamed, Expr, ExprId, ExprKind, FunctionBody, FunctionData,
  Import, ImportBinding, ImportEqualsTarget, ImportEs, ImportKind, Literal, LowerResult,
  MemberExpr, NameId, ObjectKey, ObjectLiteral, ObjectProperty, Param, Pat, PatId, PatKind, Stmt,
  StmtId, StmtKind, TemplateLiteral, UnaryOp, UpdateOp, VarDecl, VarDeclKind,
};
use parse_js::operator::{OperatorName, OPERATORS};

/// Emit a lowered HIR file to a string using the provided options.
pub fn emit_hir_file_to_string(
  lowered: &LowerResult,
  options: EmitOptions,
) -> Result<String, EmitError> {
  let mut emitter = Emitter::new(options);
  emit_hir_file(&mut emitter, lowered)?;
  Ok(String::from_utf8(emitter.into_bytes()).expect("emitted JavaScript is UTF-8"))
}

/// Emit a lowered HIR file, returning a diagnostic on failure with a best-effort
/// span.
pub fn emit_hir_file_diagnostic(
  lowered: &LowerResult,
  options: EmitOptions,
) -> Result<String, Diagnostic> {
  emit_hir_file_to_string(lowered, options)
    .map_err(|err| crate::diagnostic_from_emit_error(lowered.hir.file, err))
}

/// Emit top-level items for a lowered HIR file. This is declaration oriented and
/// will skip unsupported definitions rather than partially emitting them.
pub fn emit_hir_file(em: &mut Emitter, lowered: &LowerResult) -> EmitResult {
  let ctx = HirContext::new(lowered);
  let mut first = true;
  for item in top_level_items(&ctx) {
    if !first && !em.minify() {
      em.write_newline();
    }
    match item {
      TopItem::Def(def) => emit_def(em, &ctx, def)?,
      TopItem::Import(import) => emit_import(em, &ctx, import)?,
      TopItem::Export(export) => emit_export(em, &ctx, export)?,
    }
    first = false;
  }
  Ok(())
}

/// Emit the root statements of a specific body.
pub fn emit_hir_body(em: &mut Emitter, lowered: &LowerResult, body_id: BodyId) -> EmitResult {
  let ctx = HirContext::new(lowered);
  let body = ctx
    .body(body_id)
    .ok_or_else(|| EmitError::unsupported("missing body for emission"))?;
  emit_root_stmts(em, &ctx, body)
}

struct HirContext<'a> {
  lowered: &'a LowerResult,
}

impl<'a> HirContext<'a> {
  fn new(lowered: &'a LowerResult) -> Self {
    Self { lowered }
  }

  fn def(&self, id: DefId) -> Option<&'a DefData> {
    self
      .lowered
      .def_index
      .get(&id)
      .and_then(|idx| self.lowered.defs.get(*idx))
  }

  fn body(&self, id: BodyId) -> Option<&'a Body> {
    self
      .lowered
      .body_index
      .get(&id)
      .and_then(|idx| self.lowered.bodies.get(*idx))
      .map(|arc| arc.as_ref())
  }

  fn expr<'b>(&self, body: &'b Body, id: ExprId) -> &'b Expr {
    body
      .exprs
      .get(id.0 as usize)
      .expect("expression id out of bounds")
  }

  fn pat<'b>(&self, body: &'b Body, id: PatId) -> &'b Pat {
    body
      .pats
      .get(id.0 as usize)
      .expect("pattern id out of bounds")
  }

  fn stmt<'b>(&self, body: &'b Body, id: StmtId) -> &'b Stmt {
    body
      .stmts
      .get(id.0 as usize)
      .expect("stmt id out of bounds")
  }

  fn name(&self, id: NameId) -> &str {
    self.lowered.names.resolve(id).unwrap_or("<unknown>")
  }
}

fn emit_def(em: &mut Emitter, ctx: &HirContext<'_>, def: &DefData) -> EmitResult {
  if def.is_exported || def.is_default_export {
    em.write_keyword("export");
  }
  if def.is_default_export {
    em.write_keyword("default");
  }

  match def.path.kind {
    hir_js::DefKind::Function => emit_function_decl(em, ctx, def),
    hir_js::DefKind::Var => emit_var_def(em, ctx, def),
    _ => Err(EmitError::unsupported(
      "definition kind not supported for HIR emission",
    )),
  }
}

fn emit_import(em: &mut Emitter, ctx: &HirContext<'_>, import: &Import) -> EmitResult {
  match &import.kind {
    ImportKind::Es(es) => emit_import_es(em, ctx, es),
    ImportKind::ImportEquals(eq) => emit_import_equals(em, ctx, &eq.local, &eq.target),
  }
}

fn emit_import_es(em: &mut Emitter, ctx: &HirContext<'_>, es: &ImportEs) -> EmitResult {
  // Type-only imports do not produce runtime code after type erasure.
  if es.is_type_only {
    return Ok(());
  }
  em.write_keyword("import");
  let mut wrote = false;
  if let Some(default) = &es.default {
    em.write_identifier(ctx.name(default.local));
    wrote = true;
  }
  if let Some(ns) = &es.namespace {
    if wrote {
      em.write_punct(",");
    }
    em.write_punct("*");
    em.write_keyword("as");
    em.write_identifier(ctx.name(ns.local));
    wrote = true;
  }
  let named_specifiers: Vec<_> = es.named.iter().filter(|s| !s.is_type_only).collect();
  if !named_specifiers.is_empty() {
    if wrote {
      em.write_punct(",");
    }
    em.write_punct("{");
    for (idx, spec) in named_specifiers.iter().enumerate() {
      if idx > 0 {
        em.write_punct(",");
      }
      em.write_identifier(ctx.name(spec.imported));
      if spec.imported != spec.local {
        em.write_keyword("as");
        em.write_identifier(ctx.name(spec.local));
      }
    }
    em.write_punct("}");
    wrote = true;
  }
  if wrote {
    em.write_keyword("from");
  }
  emit_string(em, &es.specifier.value);
  em.write_semicolon();
  Ok(())
}

fn emit_import_equals(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  import: &ImportBinding,
  target: &ImportEqualsTarget,
) -> EmitResult {
  em.write_keyword("const");
  em.write_identifier(ctx.name(import.local));
  em.write_punct("=");
  match target {
    ImportEqualsTarget::Module(spec) => {
      em.write_identifier("require");
      em.write_punct("(");
      emit_string(em, &spec.value);
      em.write_punct(")");
    }
    ImportEqualsTarget::Path(path) => {
      for (idx, part) in path.iter().enumerate() {
        if idx > 0 {
          em.write_punct(".");
        }
        em.write_identifier(ctx.name(*part));
      }
    }
  }
  em.write_semicolon();
  Ok(())
}

fn emit_export(em: &mut Emitter, ctx: &HirContext<'_>, export: &Export) -> EmitResult {
  match &export.kind {
    ExportKind::Named(named) => emit_export_named(em, ctx, named),
    ExportKind::ExportAll(all) => emit_export_all(em, ctx, all),
    ExportKind::Default(default) => emit_export_default(em, ctx, default),
    ExportKind::Assignment(assign) => {
      em.write_keyword("export");
      em.write_punct("=");
      let body = ctx
        .body(assign.body)
        .ok_or_else(|| EmitError::unsupported("export assignment body missing"))?;
      emit_expr_with_min_prec(em, ctx, body, assign.expr, Prec::LOWEST)?;
      em.write_semicolon();
      Ok(())
    }
  }
}

fn emit_export_named(em: &mut Emitter, ctx: &HirContext<'_>, named: &ExportNamed) -> EmitResult {
  let specs: Vec<_> = named
    .specifiers
    .iter()
    .filter(|s| {
      if s.is_type_only {
        return false;
      }
      if named.source.is_none() && s.exported == s.local {
        // Skip redundant named exports for locally emitted declarations.
        return s.local_def.is_none();
      }
      true
    })
    .collect();
  if specs.is_empty() {
    return Ok(());
  }
  em.write_keyword("export");
  em.write_punct("{");
  for (idx, spec) in specs.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    em.write_identifier(ctx.name(spec.local));
    if spec.local != spec.exported {
      em.write_keyword("as");
      em.write_identifier(ctx.name(spec.exported));
    }
  }
  em.write_punct("}");
  if let Some(source) = &named.source {
    em.write_keyword("from");
    emit_string(em, &source.value);
  }
  em.write_semicolon();
  Ok(())
}

fn emit_export_all(em: &mut Emitter, ctx: &HirContext<'_>, all: &ExportAll) -> EmitResult {
  em.write_keyword("export");
  em.write_punct("*");
  em.write_keyword("from");
  emit_string(em, &all.source.value);
  if let Some(alias) = &all.alias {
    em.write_keyword("as");
    em.write_identifier(ctx.name(alias.exported));
  }
  em.write_semicolon();
  Ok(())
}

fn emit_export_default(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  default: &ExportDefault,
) -> EmitResult {
  em.write_keyword("export");
  em.write_keyword("default");
  match &default.value {
    ExportDefaultValue::Expr { expr, body } => {
      let body = ctx
        .body(*body)
        .ok_or_else(|| EmitError::unsupported("export default body missing"))?;
      emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)?;
      em.write_semicolon();
      Ok(())
    }
    ExportDefaultValue::Function { body, name, .. } => {
      let body = ctx
        .body(*body)
        .ok_or_else(|| EmitError::unsupported("function body not found for export default"))?;
      let func = body
        .function
        .as_ref()
        .ok_or_else(|| EmitError::unsupported("function metadata missing for export default"))?;
      emit_function_like(em, ctx, name.map(|n| ctx.name(n)), func, body)
    }
    ExportDefaultValue::Class { .. } => Err(EmitError::unsupported(
      "class default exports are not supported in HIR emission",
    )),
  }
}

fn top_level_items<'a>(ctx: &'a HirContext<'a>) -> Vec<TopItem<'a>> {
  let mut items = Vec::new();
  for import in &ctx.lowered.hir.imports {
    items.push(TopItem::Import(import));
  }
  for export in &ctx.lowered.hir.exports {
    items.push(TopItem::Export(export));
  }
  for def_id in ctx.lowered.hir.items.iter().copied() {
    if let Some(def) = ctx.def(def_id) {
      if !def.is_exported && !def.is_default_export {
        items.push(TopItem::Def(def));
      }
    }
  }
  items.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
  items
}

enum TopItem<'a> {
  Def(&'a DefData),
  Import(&'a Import),
  Export(&'a Export),
}

impl<'a> TopItem<'a> {
  fn sort_key(&self) -> (u32, u8) {
    match self {
      TopItem::Import(import) => (import.span.start, 0),
      TopItem::Export(export) => (export.span.start, 1),
      TopItem::Def(def) => (def.span.start, 2),
    }
  }
}

fn emit_var_def(em: &mut Emitter, ctx: &HirContext<'_>, def: &DefData) -> EmitResult {
  let Some(body_id) = def.body else {
    return Ok(());
  };
  let body = ctx
    .body(body_id)
    .ok_or_else(|| EmitError::unsupported("variable body not found"))?;
  let decl = body
    .root_stmts
    .iter()
    .find_map(|stmt_id| match &ctx.stmt(body, *stmt_id).kind {
      StmtKind::Var(decl) => Some(decl),
      _ => None,
    })
    .ok_or_else(|| EmitError::unsupported("variable body did not contain a declaration"))?;
  emit_var_decl(em, ctx, body, decl, true)
}

fn emit_function_decl(em: &mut Emitter, ctx: &HirContext<'_>, def: &DefData) -> EmitResult {
  let Some(body_id) = def.body else {
    return Ok(());
  };
  let body = ctx
    .body(body_id)
    .ok_or_else(|| EmitError::unsupported("function body not found"))?;
  let func = body
    .function
    .as_ref()
    .ok_or_else(|| EmitError::unsupported("function metadata missing"))?;
  emit_function_like(em, ctx, Some(ctx.name(def.name)), func, body)
}

fn emit_function_like(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  name: Option<&str>,
  func: &FunctionData,
  body: &Body,
) -> EmitResult {
  if func.is_arrow {
    emit_arrow_function(em, ctx, func, body)
  } else {
    if func.async_ {
      em.write_keyword("async");
    }
    em.write_keyword("function");
    if func.generator {
      em.write_punct("*");
    }
    if let Some(name) = name {
      em.write_identifier(name);
    }
    emit_param_list(em, ctx, body, &func.params)?;
    emit_function_body(em, ctx, body, &func.body, true)
  }
}

fn emit_arrow_function(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  func: &FunctionData,
  body: &Body,
) -> EmitResult {
  if func.async_ {
    em.write_keyword("async");
  }
  emit_param_list(em, ctx, body, &func.params)?;
  em.write_punct("=>");
  match &func.body {
    FunctionBody::Expr(expr) => emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST),
    FunctionBody::Block(stmts) => emit_block_like(em, ctx, body, stmts),
  }
}

fn emit_function_body(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  func_body: &FunctionBody,
  force_block: bool,
) -> EmitResult {
  match func_body {
    FunctionBody::Expr(expr) if !force_block => {
      emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)
    }
    FunctionBody::Expr(expr) => {
      if body.root_stmts.is_empty() {
        em.write_punct("{");
        if !em.minify() {
          em.write_newline();
        }
        em.write_keyword("return");
        emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)?;
        em.write_semicolon();
        if !em.minify() {
          em.write_newline();
        }
        em.write_punct("}");
      } else {
        emit_block_like(em, ctx, body, &body.root_stmts)?;
      }
      Ok(())
    }
    FunctionBody::Block(stmts) => emit_block_like(em, ctx, body, stmts),
  }
}

fn emit_param_list(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  params: &[Param],
) -> EmitResult {
  em.write_punct("(");
  for (idx, param) in params.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    emit_pat(em, ctx, body, param.pat, false)?;
    if let Some(default) = param.default {
      em.write_punct("=");
      emit_expr_with_min_prec(
        em,
        ctx,
        body,
        default,
        Prec::new(OPERATORS[&OperatorName::Assignment].precedence),
      )?;
    }
  }
  em.write_punct(")");
  Ok(())
}

fn emit_root_stmts(em: &mut Emitter, ctx: &HirContext<'_>, body: &Body) -> EmitResult {
  emit_stmt_list(em, ctx, body, &body.root_stmts)
}

fn emit_stmt_list(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  stmts: &[StmtId],
) -> EmitResult {
  let mut first = true;
  for stmt_id in stmts {
    if !first && !em.minify() {
      em.write_newline();
    }
    emit_stmt(em, ctx, body, *stmt_id)?;
    first = false;
  }
  Ok(())
}

fn emit_stmt(em: &mut Emitter, ctx: &HirContext<'_>, body: &Body, stmt_id: StmtId) -> EmitResult {
  let stmt = ctx.stmt(body, stmt_id);
  match &stmt.kind {
    StmtKind::Expr(expr) => {
      let needs_parens = expr_stmt_needs_parens(ctx.expr(body, *expr));
      if needs_parens {
        em.write_punct("(");
      }
      emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)?;
      if needs_parens {
        em.write_punct(")");
      }
      em.write_semicolon();
    }
    StmtKind::Decl(def) => {
      let def_data = ctx
        .def(*def)
        .ok_or_else(|| EmitError::unsupported("declaration definition not found"))?;
      emit_def(em, ctx, def_data)?;
    }
    StmtKind::Return(value) => {
      em.write_keyword("return");
      if let Some(value) = value {
        emit_expr_with_min_prec(em, ctx, body, *value, Prec::LOWEST)?;
      }
      em.write_semicolon();
    }
    StmtKind::Block(stmts) => emit_block_like(em, ctx, body, stmts)?,
    StmtKind::If {
      test,
      consequent,
      alternate,
    } => {
      em.write_keyword("if");
      em.write_punct("(");
      emit_expr_with_min_prec(em, ctx, body, *test, Prec::LOWEST)?;
      em.write_punct(")");
      emit_stmt(em, ctx, body, *consequent)?;
      if let Some(alt) = alternate {
        em.write_keyword("else");
        emit_stmt(em, ctx, body, *alt)?;
      }
    }
    StmtKind::While { test, body: inner } => {
      em.write_keyword("while");
      em.write_punct("(");
      emit_expr_with_min_prec(em, ctx, body, *test, Prec::LOWEST)?;
      em.write_punct(")");
      emit_stmt(em, ctx, body, *inner)?;
    }
    StmtKind::DoWhile { test, body: inner } => {
      em.write_keyword("do");
      emit_stmt(em, ctx, body, *inner)?;
      em.write_keyword("while");
      em.write_punct("(");
      emit_expr_with_min_prec(em, ctx, body, *test, Prec::LOWEST)?;
      em.write_punct(")");
    }
    StmtKind::For {
      init,
      test,
      update,
      body: inner,
    } => {
      em.write_keyword("for");
      em.write_punct("(");
      if let Some(init) = init {
        match init {
          hir_js::ForInit::Expr(expr) => {
            emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)?
          }
          hir_js::ForInit::Var(decl) => emit_var_decl(em, ctx, body, decl, false)?,
        }
      }
      em.write_punct(";");
      if let Some(test) = test {
        emit_expr_with_min_prec(em, ctx, body, *test, Prec::LOWEST)?;
      }
      em.write_punct(";");
      if let Some(update) = update {
        emit_expr_with_min_prec(em, ctx, body, *update, Prec::LOWEST)?;
      }
      em.write_punct(")");
      emit_stmt(em, ctx, body, *inner)?;
    }
    StmtKind::ForIn {
      left,
      right,
      body: inner,
      is_for_of,
      await_,
    } => {
      em.write_keyword("for");
      if *await_ {
        em.write_keyword("await");
      }
      em.write_punct("(");
      match left {
        hir_js::ForHead::Pat(pat) => emit_pat(em, ctx, body, *pat, true)?,
        hir_js::ForHead::Var(decl) => emit_var_decl(em, ctx, body, decl, false)?,
      }
      if *is_for_of {
        em.write_keyword("of");
      } else {
        em.write_keyword("in");
      }
      emit_expr_with_min_prec(em, ctx, body, *right, Prec::LOWEST)?;
      em.write_punct(")");
      emit_stmt(em, ctx, body, *inner)?;
    }
    StmtKind::Switch {
      discriminant,
      cases,
    } => {
      em.write_keyword("switch");
      em.write_punct("(");
      emit_expr_with_min_prec(em, ctx, body, *discriminant, Prec::LOWEST)?;
      em.write_punct(")");
      em.write_punct("{");
      for case in cases {
        if let Some(test) = case.test {
          em.write_keyword("case");
          emit_expr_with_min_prec(em, ctx, body, test, Prec::LOWEST)?;
          em.write_punct(":");
        } else {
          em.write_keyword("default");
          em.write_punct(":");
        }
        if !em.minify() {
          em.write_newline();
        }
        emit_stmt_list(em, ctx, body, &case.consequent)?;
      }
      em.write_punct("}");
    }
    StmtKind::Try {
      block,
      catch,
      finally_block,
    } => {
      em.write_keyword("try");
      emit_stmt(em, ctx, body, *block)?;
      if let Some(catch) = catch {
        em.write_keyword("catch");
        if let Some(param) = catch.param {
          em.write_punct("(");
          emit_pat(em, ctx, body, param, false)?;
          em.write_punct(")");
        }
        emit_stmt(em, ctx, body, catch.body)?;
      }
      if let Some(finally_block) = finally_block {
        em.write_keyword("finally");
        emit_stmt(em, ctx, body, *finally_block)?;
      }
    }
    StmtKind::Throw(expr) => {
      em.write_keyword("throw");
      emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)?;
      em.write_semicolon();
    }
    StmtKind::Break(label) => {
      em.write_keyword("break");
      if let Some(label) = label {
        em.write_identifier(ctx.name(*label));
      }
      em.write_semicolon();
    }
    StmtKind::Continue(label) => {
      em.write_keyword("continue");
      if let Some(label) = label {
        em.write_identifier(ctx.name(*label));
      }
      em.write_semicolon();
    }
    StmtKind::Var(decl) => {
      emit_var_decl(em, ctx, body, decl, true)?;
    }
    StmtKind::Labeled { label, body: inner } => {
      em.write_identifier(ctx.name(*label));
      em.write_punct(":");
      emit_stmt(em, ctx, body, *inner)?;
    }
    StmtKind::With {
      object,
      body: inner,
    } => {
      em.write_keyword("with");
      em.write_punct("(");
      emit_expr_with_min_prec(em, ctx, body, *object, Prec::LOWEST)?;
      em.write_punct(")");
      emit_stmt(em, ctx, body, *inner)?;
    }
    StmtKind::Empty => em.write_semicolon(),
  }
  Ok(())
}

fn emit_block_like(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  stmts: &[StmtId],
) -> EmitResult {
  em.write_punct("{");
  if !stmts.is_empty() {
    if !em.minify() {
      em.write_newline();
    }
    emit_stmt_list(em, ctx, body, stmts)?;
    if !em.minify() {
      em.write_newline();
    }
  }
  em.write_punct("}");
  Ok(())
}

fn emit_var_decl(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  decl: &VarDecl,
  trailing_semicolon: bool,
) -> EmitResult {
  let keyword = match decl.kind {
    VarDeclKind::Const => "const",
    VarDeclKind::Let => "let",
    VarDeclKind::Var => "var",
  };
  em.write_keyword(keyword);
  for (idx, declarator) in decl.declarators.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    emit_pat(em, ctx, body, declarator.pat, false)?;
    if let Some(init) = declarator.init {
      em.write_punct("=");
      emit_expr_with_min_prec(
        em,
        ctx,
        body,
        init,
        Prec::new(OPERATORS[&OperatorName::Assignment].precedence),
      )?;
    }
  }
  if trailing_semicolon {
    em.write_semicolon();
  }
  Ok(())
}

fn emit_pat(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  pat_id: PatId,
  in_assignment: bool,
) -> EmitResult {
  let pat = ctx.pat(body, pat_id);
  match &pat.kind {
    PatKind::Ident(name) => em.write_identifier(ctx.name(*name)),
    PatKind::Rest(inner) => {
      em.write_punct("...");
      emit_pat(em, ctx, body, **inner, in_assignment)?;
    }
    PatKind::Array(array) => {
      em.write_punct("[");
      for (idx, element) in array.elements.iter().enumerate() {
        if idx > 0 {
          em.write_punct(",");
        }
        if let Some(element) = element {
          emit_pat(em, ctx, body, element.pat, in_assignment)?;
          if let Some(default) = element.default_value {
            em.write_punct("=");
            emit_expr_with_min_prec(
              em,
              ctx,
              body,
              default,
              Prec::new(OPERATORS[&OperatorName::Assignment].precedence),
            )?;
          }
        }
      }
      if let Some(rest) = array.rest {
        if !array.elements.is_empty() {
          em.write_punct(",");
        }
        em.write_punct("...");
        emit_pat(em, ctx, body, rest, in_assignment)?;
      }
      em.write_punct("]");
    }
    PatKind::Object(obj) => {
      if in_assignment {
        em.write_punct("(");
      }
      em.write_punct("{");
      for (idx, prop) in obj.props.iter().enumerate() {
        if idx > 0 {
          em.write_punct(",");
        }
        emit_object_key(em, ctx, body, &prop.key)?;
        if !prop.shorthand {
          em.write_punct(":");
          emit_pat(em, ctx, body, prop.value, in_assignment)?;
        }
        if let Some(default) = prop.default_value {
          em.write_punct("=");
          emit_expr_with_min_prec(
            em,
            ctx,
            body,
            default,
            Prec::new(OPERATORS[&OperatorName::Assignment].precedence),
          )?;
        }
      }
      if let Some(rest) = obj.rest {
        if !obj.props.is_empty() {
          em.write_punct(",");
        }
        em.write_punct("...");
        emit_pat(em, ctx, body, rest, in_assignment)?;
      }
      em.write_punct("}");
      if in_assignment {
        em.write_punct(")");
      }
    }
    PatKind::Assign {
      target,
      default_value,
    } => {
      emit_pat(em, ctx, body, *target, in_assignment)?;
      em.write_punct("=");
      emit_expr_with_min_prec(
        em,
        ctx,
        body,
        *default_value,
        Prec::new(OPERATORS[&OperatorName::Assignment].precedence),
      )?;
    }
    PatKind::AssignTarget(expr) => {
      emit_expr_with_min_prec(
        em,
        ctx,
        body,
        *expr,
        Prec::new(OPERATORS[&OperatorName::Assignment].precedence),
      )?;
    }
  }
  Ok(())
}

fn emit_expr_with_min_prec(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  expr_id: ExprId,
  min_prec: Prec,
) -> EmitResult {
  let prec = expr_prec(ctx, body, expr_id)?;
  let needs_paren = needs_parens(prec, min_prec);
  if needs_paren {
    em.write_punct("(");
  }
  emit_expr_no_parens(em, ctx, body, expr_id)?;
  if needs_paren {
    em.write_punct(")");
  }
  Ok(())
}

fn expr_prec(ctx: &HirContext<'_>, body: &Body, expr_id: ExprId) -> Result<Prec, EmitError> {
  let expr = ctx.expr(body, expr_id);
  let prec = match &expr.kind {
    ExprKind::Binary { op, .. } => Prec::new(OPERATORS[&binary_operator(*op)].precedence),
    ExprKind::Assignment { op, .. } => Prec::new(OPERATORS[&assign_operator(*op)].precedence),
    ExprKind::Conditional { .. } => Prec::new(OPERATORS[&OperatorName::Conditional].precedence),
    ExprKind::Call(_) | ExprKind::Member(_) | ExprKind::TaggedTemplate { .. } => {
      CALL_MEMBER_PRECEDENCE
    }
    ExprKind::Update { op, prefix, .. } => {
      Prec::new(OPERATORS[&update_operator(*op, *prefix)].precedence)
    }
    ExprKind::Unary { op, .. } => Prec::new(OPERATORS[&unary_operator(*op)].precedence),
    ExprKind::Await { .. } => Prec::new(OPERATORS[&OperatorName::Await].precedence),
    ExprKind::Yield { delegate, .. } => {
      let op = if *delegate {
        OperatorName::YieldDelegated
      } else {
        OperatorName::Yield
      };
      Prec::new(OPERATORS[&op].precedence)
    }
    ExprKind::Template(_) => PRIMARY_PRECEDENCE,
    ExprKind::Array(_) => PRIMARY_PRECEDENCE,
    ExprKind::Object(_) => PRIMARY_PRECEDENCE,
    ExprKind::FunctionExpr { is_arrow, .. } => {
      if *is_arrow {
        ARROW_FUNCTION_PRECEDENCE
      } else {
        PRIMARY_PRECEDENCE
      }
    }
    ExprKind::ClassExpr { .. } => PRIMARY_PRECEDENCE,
    ExprKind::Literal(_) => PRIMARY_PRECEDENCE,
    ExprKind::ImportCall { .. } => CALL_MEMBER_PRECEDENCE,
    ExprKind::This
    | ExprKind::Super
    | ExprKind::Ident(_)
    | ExprKind::ImportMeta
    | ExprKind::NewTarget => PRIMARY_PRECEDENCE,
    ExprKind::Jsx(_) => return Err(EmitError::unsupported("jsx expressions are not supported")),
    ExprKind::TypeAssertion { .. } | ExprKind::NonNull { .. } | ExprKind::Satisfies { .. } => {
      CALL_MEMBER_PRECEDENCE
    }
    ExprKind::Missing => return Err(EmitError::unsupported("missing expression")),
  };
  Ok(prec)
}

fn emit_expr_no_parens(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  expr_id: ExprId,
) -> EmitResult {
  let expr = ctx.expr(body, expr_id);
  match &expr.kind {
    ExprKind::Missing => return Err(EmitError::unsupported("missing expression")),
    ExprKind::Ident(id) => em.write_identifier(ctx.name(*id)),
    ExprKind::This => em.write_keyword("this"),
    ExprKind::Super => em.write_keyword("super"),
    ExprKind::Literal(lit) => emit_literal(em, lit)?,
    ExprKind::Unary { op, expr } => emit_unary(em, ctx, body, *op, *expr)?,
    ExprKind::Update { op, expr, prefix } => emit_update(em, ctx, body, *op, *expr, *prefix)?,
    ExprKind::Binary { op, left, right } => emit_binary(em, ctx, body, *op, *left, *right)?,
    ExprKind::Assignment { op, target, value } => {
      emit_pat(em, ctx, body, *target, true)?;
      emit_assign_operator(em, *op);
      emit_expr_with_min_prec(
        em,
        ctx,
        body,
        *value,
        Prec::new(OPERATORS[&assign_operator(*op)].precedence),
      )?;
    }
    ExprKind::Call(call) => emit_call(em, ctx, body, call)?,
    ExprKind::Member(member) => emit_member(em, ctx, body, member)?,
    ExprKind::Conditional {
      test,
      consequent,
      alternate,
    } => {
      let cond_prec = Prec::new(OPERATORS[&OperatorName::Conditional].precedence);
      emit_expr_with_min_prec(em, ctx, body, *test, cond_prec.tighter())?;
      em.write_punct("?");
      emit_expr_with_min_prec(em, ctx, body, *consequent, cond_prec)?;
      em.write_punct(":");
      emit_expr_with_min_prec(em, ctx, body, *alternate, cond_prec)?;
    }
    ExprKind::Array(array) => emit_array_literal(em, ctx, body, array)?,
    ExprKind::Object(obj) => emit_object_literal(em, ctx, body, obj)?,
    ExprKind::FunctionExpr {
      def: _,
      body: body_id,
      name,
      is_arrow,
    } => {
      let body = ctx
        .body(*body_id)
        .ok_or_else(|| EmitError::unsupported("function body not found"))?;
      let func = body
        .function
        .as_ref()
        .ok_or_else(|| EmitError::unsupported("function metadata missing"))?;
      emit_function_like(
        em,
        ctx,
        name.map(|n| ctx.name(n)),
        &FunctionData {
          is_arrow: *is_arrow,
          ..func.clone()
        },
        body,
      )?;
    }
    ExprKind::ClassExpr { .. } => {
      return Err(EmitError::unsupported("class emission is not implemented"))
    }
    ExprKind::Template(tmpl) => emit_template_literal(em, ctx, body, tmpl)?,
    ExprKind::TaggedTemplate { tag, template } => {
      emit_expr_with_min_prec(em, ctx, body, *tag, CALL_MEMBER_PRECEDENCE)?;
      emit_template_literal(em, ctx, body, template)?;
    }
    ExprKind::Await { expr } => {
      em.write_keyword("await");
      emit_expr_with_min_prec(
        em,
        ctx,
        body,
        *expr,
        Prec::new(OPERATORS[&OperatorName::Await].precedence),
      )?;
    }
    ExprKind::Yield { expr, delegate } => {
      em.write_keyword("yield");
      if *delegate {
        em.write_punct("*");
      }
      if let Some(expr) = expr {
        emit_expr_with_min_prec(
          em,
          ctx,
          body,
          *expr,
          Prec::new(OPERATORS[&OperatorName::Yield].precedence),
        )?;
      }
    }
    ExprKind::TypeAssertion { .. } | ExprKind::Satisfies { .. } => {
      return Err(EmitError::unsupported(
        "type assertions are not preserved in HIR emission",
      ))
    }
    ExprKind::NonNull { expr } => {
      emit_expr_with_min_prec(em, ctx, body, *expr, CALL_MEMBER_PRECEDENCE)?;
      em.write_punct("!");
    }
    ExprKind::ImportCall {
      argument,
      attributes,
    } => {
      em.write_keyword("import");
      em.write_punct("(");
      emit_expr_with_min_prec(em, ctx, body, *argument, Prec::LOWEST)?;
      if let Some(attrs) = attributes {
        em.write_punct(",");
        emit_expr_with_min_prec(em, ctx, body, *attrs, Prec::LOWEST)?;
      }
      em.write_punct(")");
    }
    ExprKind::ImportMeta => em.write_str("import.meta"),
    ExprKind::NewTarget => em.write_str("new.target"),
    ExprKind::Jsx(_) => return Err(EmitError::unsupported("JSX emission is not supported")),
  }
  Ok(())
}

fn emit_call(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  call: &hir_js::CallExpr,
) -> EmitResult {
  if call.is_new {
    em.write_keyword("new");
  }
  emit_expr_with_min_prec(em, ctx, body, call.callee, CALL_MEMBER_PRECEDENCE)?;
  if call.optional {
    em.write_str("?.(");
  } else {
    em.write_punct("(");
  }
  for (idx, arg) in call.args.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    if arg.spread {
      em.write_punct("...");
    }
    emit_expr_with_min_prec(em, ctx, body, arg.expr, Prec::LOWEST)?;
  }
  em.write_punct(")");
  Ok(())
}

fn emit_member(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  member: &MemberExpr,
) -> EmitResult {
  emit_expr_with_min_prec(em, ctx, body, member.object, CALL_MEMBER_PRECEDENCE)?;
  let use_brackets = !matches!(member.property, ObjectKey::Ident(_));
  if member.optional {
    if use_brackets {
      em.write_str("?.[");
      emit_member_property(em, ctx, body, &member.property)?;
      em.write_punct("]");
    } else if let ObjectKey::Ident(name) = &member.property {
      em.write_punct("?.");
      em.write_identifier(ctx.name(*name));
    }
  } else if use_brackets {
    em.write_punct("[");
    emit_member_property(em, ctx, body, &member.property)?;
    em.write_punct("]");
  } else if let ObjectKey::Ident(name) = &member.property {
    em.write_punct(".");
    em.write_identifier(ctx.name(*name));
  }
  Ok(())
}

fn emit_member_property(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  property: &ObjectKey,
) -> EmitResult {
  match property {
    ObjectKey::Ident(name) => em.write_identifier(ctx.name(*name)),
    ObjectKey::String(name) => emit_string(em, name),
    ObjectKey::Number(num) => em.write_number(num),
    ObjectKey::Computed(expr) => emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)?,
  }
  Ok(())
}

fn emit_array_literal(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  array: &hir_js::ArrayLiteral,
) -> EmitResult {
  em.write_punct("[");
  for (idx, element) in array.elements.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    match element {
      hir_js::ArrayElement::Expr(expr) => {
        emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)?;
      }
      hir_js::ArrayElement::Spread(expr) => {
        em.write_punct("...");
        emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)?;
      }
      hir_js::ArrayElement::Empty => {}
    }
  }
  em.write_punct("]");
  Ok(())
}

fn emit_object_literal(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  obj: &ObjectLiteral,
) -> EmitResult {
  em.write_punct("{");
  for (idx, prop) in obj.properties.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    match prop {
      ObjectProperty::KeyValue {
        key,
        value,
        method,
        shorthand,
      } => {
        if *method {
          emit_object_key(em, ctx, body, key)?;
          if let ExprKind::FunctionExpr {
            body: func_body, ..
          } = &ctx.expr(body, *value).kind
          {
            let func_body = ctx
              .body(*func_body)
              .ok_or_else(|| EmitError::unsupported("method body missing"))?;
            let func_data = func_body
              .function
              .as_ref()
              .ok_or_else(|| EmitError::unsupported("method metadata missing"))?;
            emit_param_list(em, ctx, func_body, &func_data.params)?;
            emit_function_body(em, ctx, func_body, &func_data.body, true)?;
          } else {
            em.write_punct(":");
            emit_expr_with_min_prec(em, ctx, body, *value, Prec::LOWEST)?;
          }
        } else {
          emit_object_key(em, ctx, body, key)?;
          if !*shorthand {
            em.write_punct(":");
            emit_expr_with_min_prec(em, ctx, body, *value, Prec::LOWEST)?;
          }
        }
      }
      ObjectProperty::Getter { key, body: body_id } => {
        em.write_keyword("get");
        emit_object_key(em, ctx, body, key)?;
        let getter_body = ctx
          .body(*body_id)
          .ok_or_else(|| EmitError::unsupported("getter body missing"))?;
        if let Some(func) = &getter_body.function {
          emit_param_list(em, ctx, getter_body, &func.params)?;
          emit_function_body(em, ctx, getter_body, &func.body, true)?;
        } else {
          emit_block_like(em, ctx, getter_body, &getter_body.root_stmts)?;
        }
      }
      ObjectProperty::Setter { key, body: body_id } => {
        em.write_keyword("set");
        emit_object_key(em, ctx, body, key)?;
        let setter_body = ctx
          .body(*body_id)
          .ok_or_else(|| EmitError::unsupported("setter body missing"))?;
        if let Some(func) = &setter_body.function {
          emit_param_list(em, ctx, setter_body, &func.params)?;
          emit_function_body(em, ctx, setter_body, &func.body, true)?;
        } else {
          emit_block_like(em, ctx, setter_body, &setter_body.root_stmts)?;
        }
      }
      ObjectProperty::Spread(expr) => {
        em.write_punct("...");
        emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)?;
      }
    }
  }
  em.write_punct("}");
  Ok(())
}

fn emit_object_key(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  key: &ObjectKey,
) -> EmitResult {
  match key {
    ObjectKey::Ident(name) => em.write_identifier(ctx.name(*name)),
    ObjectKey::String(str) => emit_string(em, str),
    ObjectKey::Number(num) => em.write_number(num),
    ObjectKey::Computed(expr) => {
      em.write_punct("[");
      emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)?;
      em.write_punct("]");
    }
  }
  Ok(())
}

fn emit_template_literal(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  template: &TemplateLiteral,
) -> EmitResult {
  em.write_punct("`");
  let mut buf = Vec::new();
  emit_template_literal_segment(&mut buf, &template.head);
  em.write_str(std::str::from_utf8(&buf).expect("template literal head is UTF-8"));
  for span in template.spans.iter() {
    em.write_punct("${");
    emit_expr_with_min_prec(em, ctx, body, span.expr, Prec::LOWEST)?;
    em.write_punct("}");
    buf.clear();
    emit_template_literal_segment(&mut buf, &span.literal);
    em.write_str(std::str::from_utf8(&buf).expect("template literal span is UTF-8"));
  }
  em.write_punct("`");
  Ok(())
}

fn emit_literal(em: &mut Emitter, lit: &Literal) -> EmitResult {
  match lit {
    Literal::Number(num) => em.write_number(num),
    Literal::String(str) => emit_string(em, str),
    Literal::Boolean(true) => em.write_keyword("true"),
    Literal::Boolean(false) => em.write_keyword("false"),
    Literal::Null => em.write_keyword("null"),
    Literal::Undefined => em.write_identifier("undefined"),
    Literal::BigInt(num) => em.write_bigint_literal(num),
    Literal::Regex(regex) => {
      let mut buf = Vec::new();
      emit_regex_literal(&mut buf, regex);
      em.write_str(std::str::from_utf8(&buf).expect("regex literal is UTF-8"));
    }
  }
  Ok(())
}

fn emit_string(em: &mut Emitter, value: &str) {
  let mut buf = Vec::new();
  emit_string_literal(&mut buf, value, em.opts().quote_style, em.minify());
  em.write_str(std::str::from_utf8(&buf).expect("string literal is UTF-8"));
}

fn emit_unary(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  op: UnaryOp,
  expr: ExprId,
) -> EmitResult {
  let op_name = unary_operator(op);
  emit_unary_operator(em, op_name)?;
  emit_expr_with_min_prec(
    em,
    ctx,
    body,
    expr,
    Prec::new(OPERATORS[&op_name].precedence),
  )
}

fn emit_update(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  op: UpdateOp,
  expr: ExprId,
  prefix: bool,
) -> EmitResult {
  let op_name = update_operator(op, prefix);
  if prefix {
    emit_unary_operator(em, op_name)?;
    emit_expr_with_min_prec(
      em,
      ctx,
      body,
      expr,
      Prec::new(OPERATORS[&op_name].precedence),
    )
  } else {
    emit_expr_with_min_prec(
      em,
      ctx,
      body,
      expr,
      Prec::new(OPERATORS[&op_name].precedence),
    )?;
    emit_unary_operator(em, op_name)
  }
}

fn emit_binary(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  op: BinaryOp,
  left: ExprId,
  right: ExprId,
) -> EmitResult {
  let op_name = binary_operator(op);
  let left_needs_paren = op_name == OperatorName::Exponentiation
    && matches!(
      ctx.expr(body, left).kind,
      ExprKind::Unary { .. } | ExprKind::Update { .. }
    );
  if left_needs_paren {
    em.write_punct("(");
    emit_expr_no_parens(em, ctx, body, left)?;
    em.write_punct(")");
  } else {
    emit_expr_with_min_prec(
      em,
      ctx,
      body,
      left,
      child_min_prec_for_binary(op_name, crate::precedence::Side::Left),
    )?;
  }

  emit_binary_operator(em, op_name)?;

  let right_prec = child_min_prec_for_binary(op_name, crate::precedence::Side::Right);
  emit_expr_with_min_prec(em, ctx, body, right, right_prec)?;
  Ok(())
}

fn emit_unary_operator(em: &mut Emitter, op: OperatorName) -> EmitResult {
  match op {
    OperatorName::LogicalNot => em.write_punct("!"),
    OperatorName::BitwiseNot => em.write_punct("~"),
    OperatorName::UnaryPlus => em.write_punct("+"),
    OperatorName::UnaryNegation => em.write_punct("-"),
    OperatorName::Typeof => em.write_keyword("typeof"),
    OperatorName::Void => em.write_keyword("void"),
    OperatorName::Delete => em.write_keyword("delete"),
    OperatorName::Await => em.write_keyword("await"),
    OperatorName::PrefixIncrement => em.write_punct("++"),
    OperatorName::PrefixDecrement => em.write_punct("--"),
    OperatorName::PostfixIncrement => em.write_punct("++"),
    OperatorName::PostfixDecrement => em.write_punct("--"),
    OperatorName::Yield | OperatorName::YieldDelegated => em.write_keyword("yield"),
    _ => return Err(EmitError::unsupported("unary operator not supported")),
  }
  Ok(())
}

fn emit_binary_operator(em: &mut Emitter, op: OperatorName) -> EmitResult {
  match op {
    OperatorName::Addition => em.write_punct("+"),
    OperatorName::Subtraction => em.write_punct("-"),
    OperatorName::Multiplication => em.write_punct("*"),
    OperatorName::Division => em.write_punct("/"),
    OperatorName::Remainder => em.write_punct("%"),
    OperatorName::Exponentiation => em.write_punct("**"),
    OperatorName::BitwiseLeftShift => em.write_punct("<<"),
    OperatorName::BitwiseRightShift => em.write_punct(">>"),
    OperatorName::BitwiseUnsignedRightShift => em.write_punct(">>>"),
    OperatorName::BitwiseOr => em.write_punct("|"),
    OperatorName::BitwiseAnd => em.write_punct("&"),
    OperatorName::BitwiseXor => em.write_punct("^"),
    OperatorName::LogicalOr => em.write_punct("||"),
    OperatorName::LogicalAnd => em.write_punct("&&"),
    OperatorName::NullishCoalescing => em.write_punct("??"),
    OperatorName::Equality => em.write_punct("=="),
    OperatorName::Inequality => em.write_punct("!="),
    OperatorName::StrictEquality => em.write_punct("==="),
    OperatorName::StrictInequality => em.write_punct("!=="),
    OperatorName::LessThan => em.write_punct("<"),
    OperatorName::LessThanOrEqual => em.write_punct("<="),
    OperatorName::GreaterThan => em.write_punct(">"),
    OperatorName::GreaterThanOrEqual => em.write_punct(">="),
    OperatorName::In => em.write_keyword("in"),
    OperatorName::Instanceof => em.write_keyword("instanceof"),
    OperatorName::Comma => em.write_punct(","),
    _ => return Err(EmitError::unsupported("binary operator not supported")),
  }
  Ok(())
}

fn emit_assign_operator(em: &mut Emitter, op: AssignOp) {
  let text = match op {
    AssignOp::Assign => "=",
    AssignOp::AddAssign => "+=",
    AssignOp::SubAssign => "-=",
    AssignOp::MulAssign => "*=",
    AssignOp::DivAssign => "/=",
    AssignOp::RemAssign => "%=",
    AssignOp::ShiftLeftAssign => "<<=",
    AssignOp::ShiftRightAssign => ">>=",
    AssignOp::ShiftRightUnsignedAssign => ">>>=",
    AssignOp::BitOrAssign => "|=",
    AssignOp::BitAndAssign => "&=",
    AssignOp::BitXorAssign => "^=",
    AssignOp::LogicalAndAssign => "&&=",
    AssignOp::LogicalOrAssign => "||=",
    AssignOp::NullishAssign => "??=",
    AssignOp::ExponentAssign => "**=",
  };
  em.write_punct(text);
}

fn expr_stmt_needs_parens(expr: &Expr) -> bool {
  matches!(
    expr.kind,
    ExprKind::Object(_)
      | ExprKind::FunctionExpr {
        is_arrow: false,
        ..
      }
      | ExprKind::ClassExpr { .. }
  )
}

fn binary_operator(op: BinaryOp) -> OperatorName {
  match op {
    BinaryOp::Add => OperatorName::Addition,
    BinaryOp::Subtract => OperatorName::Subtraction,
    BinaryOp::Multiply => OperatorName::Multiplication,
    BinaryOp::Divide => OperatorName::Division,
    BinaryOp::Remainder => OperatorName::Remainder,
    BinaryOp::Exponent => OperatorName::Exponentiation,
    BinaryOp::ShiftLeft => OperatorName::BitwiseLeftShift,
    BinaryOp::ShiftRight => OperatorName::BitwiseRightShift,
    BinaryOp::ShiftRightUnsigned => OperatorName::BitwiseUnsignedRightShift,
    BinaryOp::BitOr => OperatorName::BitwiseOr,
    BinaryOp::BitAnd => OperatorName::BitwiseAnd,
    BinaryOp::BitXor => OperatorName::BitwiseXor,
    BinaryOp::LogicalOr => OperatorName::LogicalOr,
    BinaryOp::LogicalAnd => OperatorName::LogicalAnd,
    BinaryOp::NullishCoalescing => OperatorName::NullishCoalescing,
    BinaryOp::Equality => OperatorName::Equality,
    BinaryOp::Inequality => OperatorName::Inequality,
    BinaryOp::StrictEquality => OperatorName::StrictEquality,
    BinaryOp::StrictInequality => OperatorName::StrictInequality,
    BinaryOp::LessThan => OperatorName::LessThan,
    BinaryOp::LessEqual => OperatorName::LessThanOrEqual,
    BinaryOp::GreaterThan => OperatorName::GreaterThan,
    BinaryOp::GreaterEqual => OperatorName::GreaterThanOrEqual,
    BinaryOp::In => OperatorName::In,
    BinaryOp::Instanceof => OperatorName::Instanceof,
    BinaryOp::Comma => OperatorName::Comma,
  }
}

fn assign_operator(op: AssignOp) -> OperatorName {
  match op {
    AssignOp::Assign => OperatorName::Assignment,
    AssignOp::AddAssign => OperatorName::AssignmentAddition,
    AssignOp::SubAssign => OperatorName::AssignmentSubtraction,
    AssignOp::MulAssign => OperatorName::AssignmentMultiplication,
    AssignOp::DivAssign => OperatorName::AssignmentDivision,
    AssignOp::RemAssign => OperatorName::AssignmentRemainder,
    AssignOp::ShiftLeftAssign => OperatorName::AssignmentBitwiseLeftShift,
    AssignOp::ShiftRightAssign => OperatorName::AssignmentBitwiseRightShift,
    AssignOp::ShiftRightUnsignedAssign => OperatorName::AssignmentBitwiseUnsignedRightShift,
    AssignOp::BitOrAssign => OperatorName::AssignmentBitwiseOr,
    AssignOp::BitAndAssign => OperatorName::AssignmentBitwiseAnd,
    AssignOp::BitXorAssign => OperatorName::AssignmentBitwiseXor,
    AssignOp::LogicalAndAssign => OperatorName::AssignmentLogicalAnd,
    AssignOp::LogicalOrAssign => OperatorName::AssignmentLogicalOr,
    AssignOp::NullishAssign => OperatorName::AssignmentNullishCoalescing,
    AssignOp::ExponentAssign => OperatorName::AssignmentExponentiation,
  }
}

fn unary_operator(op: UnaryOp) -> OperatorName {
  match op {
    UnaryOp::Not => OperatorName::LogicalNot,
    UnaryOp::BitNot => OperatorName::BitwiseNot,
    UnaryOp::Plus => OperatorName::UnaryPlus,
    UnaryOp::Minus => OperatorName::UnaryNegation,
    UnaryOp::Typeof => OperatorName::Typeof,
    UnaryOp::Void => OperatorName::Void,
    UnaryOp::Delete => OperatorName::Delete,
    UnaryOp::Await => OperatorName::Await,
  }
}

fn update_operator(op: UpdateOp, prefix: bool) -> OperatorName {
  match (op, prefix) {
    (UpdateOp::Increment, true) => OperatorName::PrefixIncrement,
    (UpdateOp::Decrement, true) => OperatorName::PrefixDecrement,
    (UpdateOp::Increment, false) => OperatorName::PostfixIncrement,
    (UpdateOp::Decrement, false) => OperatorName::PostfixDecrement,
  }
}
