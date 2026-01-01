use crate::escape::{emit_regex_literal, emit_string_literal, emit_template_literal_segment};
use crate::module_names::{
  emit_identifier_name_or_string_literal, emit_module_binding_identifier_or_string_literal,
  is_module_binding_identifier_token,
};
use crate::precedence::{
  child_min_prec_for_binary, needs_parens, Prec, ARROW_FUNCTION_PRECEDENCE, CALL_MEMBER_PRECEDENCE,
  PRIMARY_PRECEDENCE,
};
use crate::{EmitError, EmitOptions, EmitResult, Emitter};
use diagnostics::Diagnostic;
use hir_js::{
  AssignOp, BinaryOp, Body, BodyId, ClassMember, ClassMemberKey, ClassMemberKind, ClassMethodKind,
  Decorator, DefData, DefId, Export, ExportAll, ExportDefault, ExportDefaultValue, ExportKind,
  ExportNamed, Expr, ExprId, ExprKind, FunctionBody, FunctionData, Import, ImportBinding,
  ImportEqualsTarget, ImportEs, ImportKind, JsxAttr, JsxAttrValue, JsxChild, JsxElement,
  JsxElementName, JsxExprContainer, JsxMemberExpr, JsxName, Literal, LowerResult, MemberExpr,
  ModuleAttributes, NameId, ObjectKey, ObjectLiteral, ObjectProperty, Param, Pat, PatId, PatKind,
  Stmt, StmtId, StmtKind, TemplateLiteral, UnaryOp, UpdateOp, VarDecl, VarDeclKind,
};
use parse_js::operator::{OperatorName, OPERATORS};
use std::fmt::Write;

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

/// Emit a lowered HIR file (imports/exports plus the root body statements).
///
/// This is intended to reproduce full file output. Unsupported constructs are
/// reported as errors so callers can fall back to alternative emitters.
pub fn emit_hir_file(em: &mut Emitter, lowered: &LowerResult) -> EmitResult {
  let ctx = HirContext::new(lowered);
  let root_body = ctx
    .body(ctx.lowered.root_body())
    .ok_or_else(|| EmitError::unsupported("missing root body for emission"))?;

  enum ModuleItem<'a> {
    Import(&'a Import),
    Export(&'a Export),
    Stmt(StmtId),
  }

  struct ItemWithSpan<'a> {
    start: u32,
    kind: u8,
    item: ModuleItem<'a>,
  }

  let mut items: Vec<ItemWithSpan<'_>> = Vec::new();
  for import in &ctx.lowered.hir.imports {
    items.push(ItemWithSpan {
      start: import.span.start,
      kind: 0,
      item: ModuleItem::Import(import),
    });
  }
  for export in &ctx.lowered.hir.exports {
    // `hir-js` records exported declarations both as root-body statements with
    // `DefData::{is_exported,is_default_export}` set and as explicit `Export`
    // entries. Since `emit_def` already emits `export`/`export default` on the
    // declaration itself, emitting the corresponding `ExportDefault` entries
    // would duplicate output (e.g. `export default class ...export default class ...`).
    //
    // Named exports have their own filtering in `emit_export_named` (based on
    // `ExportSpecifier::local_def`), but default-exported class/function
    // declarations need special casing here.
    if let ExportKind::Default(default) = &export.kind {
      let def_id = match &default.value {
        ExportDefaultValue::Function { def, .. } | ExportDefaultValue::Class { def, .. } => {
          Some(*def)
        }
        ExportDefaultValue::Expr { .. } => None,
      };
      if let Some(def_id) = def_id {
        if ctx.def(def_id).is_some_and(|def| def.is_default_export) {
          continue;
        }
      }
    }

    items.push(ItemWithSpan {
      start: export.span.start,
      kind: 1,
      item: ModuleItem::Export(export),
    });
  }
  for stmt_id in root_body.root_stmts.iter().copied() {
    let stmt = ctx.stmt(root_body, stmt_id);
    items.push(ItemWithSpan {
      start: stmt.span.start,
      kind: 2,
      item: ModuleItem::Stmt(stmt_id),
    });
  }
  items.sort_by(|a, b| (a.start, a.kind).cmp(&(b.start, b.kind)));

  let mut first = true;
  for item in items {
    if !first && !em.minify() {
      em.write_newline();
    }
    match item.item {
      ModuleItem::Import(import) => emit_import(em, &ctx, import)?,
      ModuleItem::Export(export) => emit_export(em, &ctx, export)?,
      ModuleItem::Stmt(stmt_id) => emit_stmt(em, &ctx, root_body, stmt_id)?,
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

fn emit_decorators(em: &mut Emitter, ctx: &HirContext<'_>, decorators: &[Decorator]) -> EmitResult {
  for deco in decorators {
    em.write_punct("@");
    let deco_body = ctx
      .body(deco.body)
      .ok_or_else(|| EmitError::unsupported("decorator body not found"))?;
    emit_expr_with_min_prec(em, ctx, deco_body, deco.expr, Prec::LOWEST)?;
    em.write_space();
  }
  Ok(())
}

fn emit_def(em: &mut Emitter, ctx: &HirContext<'_>, def: &DefData) -> EmitResult {
  emit_decorators(em, ctx, &def.decorators)?;
  if def.is_exported || def.is_default_export {
    em.write_keyword("export");
  }
  if def.is_default_export {
    em.write_keyword("default");
  }

  match def.path.kind {
    hir_js::DefKind::Function => emit_function_decl(em, ctx, def),
    hir_js::DefKind::Var | hir_js::DefKind::VarDeclarator => emit_var_def(em, ctx, def),
    hir_js::DefKind::Class => emit_class_decl(em, ctx, def),
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

fn emit_module_attributes(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  attrs: &ModuleAttributes,
) -> EmitResult {
  em.write_keyword("with");
  let body = ctx
    .body(attrs.body)
    .ok_or_else(|| EmitError::unsupported("module attributes body missing"))?;
  emit_expr_with_min_prec(em, ctx, body, attrs.expr, Prec::LOWEST)
}

fn emit_import_es(em: &mut Emitter, ctx: &HirContext<'_>, es: &ImportEs) -> EmitResult {
  // Type-only imports do not produce runtime code after type erasure.
  if es.is_type_only {
    return Ok(());
  }
  let named_specifiers: Vec<_> = es.named.iter().filter(|s| !s.is_type_only).collect();
  if es.default.is_none()
    && es.namespace.is_none()
    && named_specifiers.is_empty()
    && !es.named.is_empty()
  {
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
  if !named_specifiers.is_empty() {
    if wrote {
      em.write_punct(",");
    }
    em.write_punct("{");
    for (idx, spec) in named_specifiers.iter().enumerate() {
      if idx > 0 {
        em.write_punct(",");
      }
      let imported = ctx.name(spec.imported);
      emit_identifier_name_or_string_literal(em, imported);
      let imported_requires_alias = !is_module_binding_identifier_token(imported);
      if spec.imported != spec.local || imported_requires_alias {
        em.write_keyword("as");
        emit_module_binding_identifier_or_string_literal(em, ctx.name(spec.local));
      }
    }
    em.write_punct("}");
    wrote = true;
  }
  if wrote {
    em.write_keyword("from");
  }
  emit_string(em, &es.specifier.value);
  if let Some(attrs) = &es.attributes {
    emit_module_attributes(em, ctx, attrs)?;
  }
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
    // TypeScript-only declaration; no runtime output.
    ExportKind::AsNamespace(_) => Ok(()),
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
    if !named.is_type_only {
      if let Some(source) = &named.source {
        // Preserve side-effect-only export-from statements (`export {} from "mod";`).
        //
        // `hir-js` represents these as `ExportNamed { source: Some(_), specifiers: [] }`.
        // After filtering type-only specifiers, we can distinguish this from
        // `export { type Foo } from "mod"` (which becomes empty but still has
        // specifiers) and should not produce a runtime import.
        if named.specifiers.is_empty() {
          em.write_keyword("import");
          emit_string(em, &source.value);
          if let Some(attrs) = &named.attributes {
            emit_module_attributes(em, ctx, attrs)?;
          }
          em.write_semicolon();
        }
      }
    }
    return Ok(());
  }
  em.write_keyword("export");
  em.write_punct("{");
  for (idx, spec) in specs.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    let local = ctx.name(spec.local);
    emit_identifier_name_or_string_literal(em, local);
    let local_requires_alias = !is_module_binding_identifier_token(local);
    if spec.local != spec.exported || local_requires_alias {
      em.write_keyword("as");
      emit_module_binding_identifier_or_string_literal(em, ctx.name(spec.exported));
    }
  }
  em.write_punct("}");
  if let Some(source) = &named.source {
    em.write_keyword("from");
    emit_string(em, &source.value);
    if let Some(attrs) = &named.attributes {
      emit_module_attributes(em, ctx, attrs)?;
    }
  }
  em.write_semicolon();
  Ok(())
}

fn emit_export_all(em: &mut Emitter, ctx: &HirContext<'_>, all: &ExportAll) -> EmitResult {
  em.write_keyword("export");
  em.write_punct("*");
  if let Some(alias) = &all.alias {
    em.write_keyword("as");
    emit_module_binding_identifier_or_string_literal(em, ctx.name(alias.exported));
  }
  em.write_keyword("from");
  emit_string(em, &all.source.value);
  if let Some(attrs) = &all.attributes {
    emit_module_attributes(em, ctx, attrs)?;
  }
  em.write_semicolon();
  Ok(())
}

fn emit_export_default(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  default: &ExportDefault,
) -> EmitResult {
  match &default.value {
    ExportDefaultValue::Function { def, .. } | ExportDefaultValue::Class { def, .. } => {
      if let Some(def_data) = ctx.def(*def) {
        emit_decorators(em, ctx, &def_data.decorators)?;
      }
    }
    ExportDefaultValue::Expr { .. } => {}
  }
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
    ExportDefaultValue::Class { body, name, .. } => {
      let body = ctx
        .body(*body)
        .ok_or_else(|| EmitError::unsupported("class body not found for export default"))?;
      emit_class_like(em, ctx, body, name.map(|n| ctx.name(n)), true)
    }
  }
}

// `emit_hir_file` drives emission through the lowered root body, merging in
// import/export declarations which are stored separately on `HirFile`.

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

fn emit_class_decl(em: &mut Emitter, ctx: &HirContext<'_>, def: &DefData) -> EmitResult {
  let Some(body_id) = def.body else {
    return Ok(());
  };
  let body = ctx
    .body(body_id)
    .ok_or_else(|| EmitError::unsupported("class body not found"))?;
  emit_class_like(em, ctx, body, Some(ctx.name(def.name)), false)
}

fn emit_class_like(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  name: Option<&str>,
  allow_anonymous: bool,
) -> EmitResult {
  let Some(class) = body.class.as_ref() else {
    return Err(EmitError::unsupported(
      "class metadata missing for emission",
    ));
  };

  em.write_keyword("class");
  if let Some(name) = name {
    em.write_identifier(name);
  } else if !allow_anonymous {
    return Err(EmitError::unsupported("class declaration missing name"));
  }

  if let Some(extends) = class.extends {
    em.write_keyword("extends");
    emit_expr_with_min_prec(em, ctx, body, extends, Prec::LOWEST)?;
  }

  em.write_punct("{");
  for member in &class.members {
    emit_class_member(em, ctx, body, member)?;
  }
  em.write_punct("}");
  Ok(())
}

fn emit_class_member(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  class_body: &Body,
  member: &ClassMember,
) -> EmitResult {
  let member_def = match &member.kind {
    ClassMemberKind::Constructor { def, .. }
    | ClassMemberKind::Method { def, .. }
    | ClassMemberKind::Field { def, .. } => Some(*def),
    ClassMemberKind::StaticBlock { .. } => None,
  };
  if let Some(def_id) = member_def {
    let def = ctx
      .def(def_id)
      .ok_or_else(|| EmitError::unsupported("class member definition not found"))?;
    emit_decorators(em, ctx, &def.decorators)?;
  }

  match &member.kind {
    ClassMemberKind::StaticBlock { stmt } => {
      em.write_keyword("static");
      emit_stmt(em, ctx, class_body, *stmt)
    }
    ClassMemberKind::Field {
      initializer, key, ..
    } => {
      if member.static_ {
        em.write_keyword("static");
      }
      emit_class_member_key(em, ctx, class_body, key)?;
      if let Some(init_body) = initializer {
        let init_body = ctx
          .body(*init_body)
          .ok_or_else(|| EmitError::unsupported("class field initializer body missing"))?;
        let expr = init_body
          .root_stmts
          .iter()
          .find_map(|stmt_id| match &ctx.stmt(init_body, *stmt_id).kind {
            StmtKind::Expr(expr) => Some(*expr),
            _ => None,
          })
          .ok_or_else(|| EmitError::unsupported("class field initializer expression missing"))?;
        em.write_punct("=");
        emit_expr_with_min_prec(
          em,
          ctx,
          init_body,
          expr,
          Prec::new(OPERATORS[&OperatorName::Assignment].precedence),
        )?;
      }
      em.write_semicolon();
      Ok(())
    }
    ClassMemberKind::Constructor { body, .. } => {
      if member.static_ {
        return Err(EmitError::unsupported(
          "static class constructors are invalid",
        ));
      }
      let body_id = body.ok_or_else(|| EmitError::unsupported("constructor body missing"))?;
      let ctor_body = ctx
        .body(body_id)
        .ok_or_else(|| EmitError::unsupported("constructor body not found"))?;
      let func = ctor_body
        .function
        .as_ref()
        .ok_or_else(|| EmitError::unsupported("constructor metadata missing"))?;
      em.write_identifier("constructor");
      emit_param_list(em, ctx, ctor_body, &func.params)?;
      emit_function_body(em, ctx, ctor_body, &func.body, true)
    }
    ClassMemberKind::Method {
      body, key, kind, ..
    } => {
      if member.static_ {
        em.write_keyword("static");
      }
      match kind {
        ClassMethodKind::Getter => em.write_keyword("get"),
        ClassMethodKind::Setter => em.write_keyword("set"),
        ClassMethodKind::Method => {}
      }

      let body_id = body.ok_or_else(|| EmitError::unsupported("class method body missing"))?;
      let method_body = ctx
        .body(body_id)
        .ok_or_else(|| EmitError::unsupported("class method body not found"))?;
      let func = method_body
        .function
        .as_ref()
        .ok_or_else(|| EmitError::unsupported("class method metadata missing"))?;

      if matches!(kind, ClassMethodKind::Method) {
        if func.async_ {
          em.write_keyword("async");
        }
        if func.generator {
          em.write_punct("*");
        }
      }

      emit_class_member_key(em, ctx, class_body, key)?;
      emit_param_list(em, ctx, method_body, &func.params)?;
      emit_function_body(em, ctx, method_body, &func.body, true)
    }
  }
}

fn emit_class_member_key(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  key: &ClassMemberKey,
) -> EmitResult {
  match key {
    ClassMemberKey::Ident(name) => em.write_identifier(ctx.name(*name)),
    ClassMemberKey::Private(name) => em.write_str(ctx.name(*name)),
    ClassMemberKey::String(value) => emit_string(em, value),
    ClassMemberKey::Number(value) => em.write_number(value),
    ClassMemberKey::Computed(expr) => {
      em.write_punct("[");
      emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)?;
      em.write_punct("]");
    }
  }
  Ok(())
}

fn emit_jsx_elem(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  elem: &JsxElement,
) -> EmitResult {
  match &elem.name {
    Some(name) => {
      em.write_char('<')?;
      emit_jsx_elem_name(em, ctx, name)?;
      for attr in &elem.attributes {
        em.write_char(' ')?;
        emit_jsx_attr(em, ctx, body, attr)?;
      }
      if elem.children.is_empty() {
        em.write_str("/>");
        return Ok(());
      }
      em.write_char('>')?;
      emit_jsx_children(em, ctx, body, &elem.children)?;
      em.write_str("</");
      emit_jsx_elem_name(em, ctx, name)?;
      em.write_char('>')?;
      Ok(())
    }
    None => {
      em.write_str("<>");
      emit_jsx_children(em, ctx, body, &elem.children)?;
      em.write_str("</>");
      Ok(())
    }
  }
}

fn emit_jsx_elem_name(em: &mut Emitter, ctx: &HirContext<'_>, name: &JsxElementName) -> EmitResult {
  match name {
    JsxElementName::Ident(id) => {
      em.write_str(ctx.name(*id));
      Ok(())
    }
    JsxElementName::Name(name) => emit_jsx_name(em, name),
    JsxElementName::Member(member) => emit_jsx_member_expr(em, ctx, member),
  }
}

fn emit_jsx_member_expr(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  member: &JsxMemberExpr,
) -> EmitResult {
  em.write_str(ctx.name(member.base));
  for segment in &member.path {
    em.write_char('.')?;
    em.write_str(ctx.name(*segment));
  }
  Ok(())
}

fn emit_jsx_name(em: &mut Emitter, name: &JsxName) -> EmitResult {
  if let Some(namespace) = &name.namespace {
    em.write_str(namespace);
    em.write_char(':')?;
  }
  em.write_str(&name.name);
  Ok(())
}

fn emit_jsx_attr(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  attr: &JsxAttr,
) -> EmitResult {
  match attr {
    JsxAttr::Named { name, value } => {
      emit_jsx_name(em, name)?;
      if let Some(value) = value {
        em.write_char('=')?;
        emit_jsx_attr_value(em, ctx, body, value)?;
      }
      Ok(())
    }
    JsxAttr::Spread { expr } => {
      em.write_str("{...");
      emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)?;
      em.write_char('}')?;
      Ok(())
    }
  }
}

fn emit_jsx_attr_value(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  value: &JsxAttrValue,
) -> EmitResult {
  match value {
    JsxAttrValue::Text(text) => crate::jsx::escape_jsx_string_literal(em, text),
    JsxAttrValue::Expression(expr) => emit_jsx_expr_container(em, ctx, body, expr),
    JsxAttrValue::Element(elem) => emit_jsx_elem(em, ctx, body, elem),
  }
}

fn emit_jsx_expr_container(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  container: &JsxExprContainer,
) -> EmitResult {
  if container.expr.is_none() {
    em.write_str("{}");
    return Ok(());
  }
  em.write_char('{')?;
  if container.spread {
    em.write_str("...");
  }
  if let Some(expr) = container.expr {
    emit_expr_with_min_prec(em, ctx, body, expr, Prec::LOWEST)?;
  }
  em.write_char('}')?;
  Ok(())
}

fn emit_jsx_children(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  children: &[JsxChild],
) -> EmitResult {
  let mut idx = 0;
  while idx < children.len() {
    match &children[idx] {
      JsxChild::Text(text) => {
        let mut combined = text.clone();
        idx += 1;
        while idx < children.len() {
          if let JsxChild::Text(next) = &children[idx] {
            combined.push_str(next);
            idx += 1;
          } else {
            break;
          }
        }
        crate::jsx::escape_jsx_child_text(em, &combined)?;
      }
      JsxChild::Element(elem) => {
        emit_jsx_elem(em, ctx, body, elem)?;
        idx += 1;
      }
      JsxChild::Expr(expr) => {
        emit_jsx_expr_container(em, ctx, body, expr)?;
        idx += 1;
      }
    }
  }
  Ok(())
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
    FunctionBody::Expr(expr) => {
      let needs_parens = arrow_concise_body_needs_parens(ctx.expr(body, *expr));
      if needs_parens {
        em.write_punct("(");
      }
      emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)?;
      if needs_parens {
        em.write_punct(")");
      }
      Ok(())
    }
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
  // Default values are followed by either `,` or `)` and must therefore treat
  // the comma operator as needing parentheses to avoid being parsed as a
  // parameter separator (e.g. `a=(b,c)`).
  let assignment_expr_min_prec = Prec::new(OPERATORS[&OperatorName::Comma].precedence).tighter();
  em.write_punct("(");
  for (idx, param) in params.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    emit_decorators(em, ctx, &param.decorators)?;
    if param.rest {
      em.write_punct("...");
    }
    emit_pat(em, ctx, body, param.pat, false)?;
    if let Some(default) = param.default {
      em.write_punct("=");
      emit_expr_with_min_prec(em, ctx, body, default, assignment_expr_min_prec)?;
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
    if matches!(ctx.stmt(body, *stmt_id).kind, StmtKind::Empty) {
      continue;
    }
    if !first && !em.minify() {
      em.write_newline();
    }
    emit_stmt(em, ctx, body, *stmt_id)?;
    first = false;
  }
  Ok(())
}

fn emit_stmt_as_body(
  em: &mut Emitter,
  ctx: &HirContext<'_>,
  body: &Body,
  stmt_id: StmtId,
) -> EmitResult {
  if matches!(ctx.stmt(body, stmt_id).kind, StmtKind::Empty) {
    em.write_semicolon();
    Ok(())
  } else {
    emit_stmt(em, ctx, body, stmt_id)
  }
}

fn var_decl_is_exported(ctx: &HirContext<'_>, body: &Body, decl: &VarDecl) -> bool {
  decl
    .declarators
    .iter()
    .any(|declarator| pat_contains_exported_binding(ctx, body, declarator.pat))
}

fn def_is_root_export(ctx: &HirContext<'_>, mut def_id: DefId) -> bool {
  loop {
    let Some(def) = ctx.def(def_id) else {
      return false;
    };
    if !def.is_exported {
      return false;
    }

    let Some(parent) = def.parent else {
      return true;
    };
    let Some(parent_def) = ctx.def(parent) else {
      return false;
    };
    if parent_def.path.kind == hir_js::DefKind::VarDeclarator {
      def_id = parent;
      continue;
    }

    return false;
  }
}

fn pat_contains_exported_binding(ctx: &HirContext<'_>, body: &Body, pat_id: PatId) -> bool {
  let pat = ctx.pat(body, pat_id);
  match &pat.kind {
    PatKind::Ident(name) => {
      // `VarDecl` statements in HIR do not record whether they were preceded by
      // an `export` keyword, so we infer that by looking up the definition that
      // corresponds to the binding pattern.
      //
      // Most of the time `SpanMap::def_at_offset` returns the correct def, but
      // TypeScript lowering (e.g. enums/namespaces) can synthesize multiple defs
      // with the exact same span start (notably the `var` binding, its
      // `VarDeclarator` wrapper, and the IIFE parameter that shadows it). In
      // those cases, the span map tie-breaker may return a non-binding def (like
      // the parameter), causing us to drop `export` on the `var` declaration and
      // silently change module exports.
      //
      // To keep emission correct, validate that the span map lookup refers to
      // the expected var def, and fall back to a direct scan for a matching var
      // binding when it doesn't.

      if let Some(def_id) = ctx.lowered.hir.span_map.def_at_offset(pat.span.start) {
        if let Some(def) = ctx.def(def_id) {
          if matches!(
            def.path.kind,
            hir_js::DefKind::Var | hir_js::DefKind::VarDeclarator
          ) && def.name == *name
            && def.span == pat.span
            && def_is_root_export(ctx, def_id)
          {
            return true;
          }
        }
      }
      ctx.lowered.defs.iter().any(|def| {
        matches!(
          def.path.kind,
          hir_js::DefKind::Var | hir_js::DefKind::VarDeclarator
        ) && def.name == *name
          && def.span == pat.span
          && def_is_root_export(ctx, def.id)
      })
    }
    PatKind::Array(array) => {
      array
        .elements
        .iter()
        .flatten()
        .any(|elem| pat_contains_exported_binding(ctx, body, elem.pat))
        || array
          .rest
          .is_some_and(|rest| pat_contains_exported_binding(ctx, body, rest))
    }
    PatKind::Object(obj) => {
      obj
        .props
        .iter()
        .any(|prop| pat_contains_exported_binding(ctx, body, prop.value))
        || obj
          .rest
          .is_some_and(|rest| pat_contains_exported_binding(ctx, body, rest))
    }
    PatKind::Rest(inner) => pat_contains_exported_binding(ctx, body, **inner),
    PatKind::Assign { target, .. } => pat_contains_exported_binding(ctx, body, *target),
    PatKind::AssignTarget(_) => false,
  }
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
      emit_stmt_as_body(em, ctx, body, *consequent)?;
      if let Some(alt) = alternate {
        em.write_keyword("else");
        emit_stmt_as_body(em, ctx, body, *alt)?;
      }
    }
    StmtKind::While { test, body: inner } => {
      em.write_keyword("while");
      em.write_punct("(");
      emit_expr_with_min_prec(em, ctx, body, *test, Prec::LOWEST)?;
      em.write_punct(")");
      emit_stmt_as_body(em, ctx, body, *inner)?;
    }
    StmtKind::DoWhile { test, body: inner } => {
      em.write_keyword("do");
      emit_stmt_as_body(em, ctx, body, *inner)?;
      em.write_keyword("while");
      em.write_punct("(");
      emit_expr_with_min_prec(em, ctx, body, *test, Prec::LOWEST)?;
      em.write_punct(")");
      em.write_semicolon();
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
            let needs_parens = for_init_expr_needs_parens(ctx, body, *expr);
            if needs_parens {
              em.write_punct("(");
            }
            emit_expr_with_min_prec(em, ctx, body, *expr, Prec::LOWEST)?;
            if needs_parens {
              em.write_punct(")");
            }
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
      emit_stmt_as_body(em, ctx, body, *inner)?;
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
        hir_js::ForHead::Pat(pat) => {
          let needs_parens = for_inof_assign_needs_parens(ctx, body, *pat);
          if needs_parens {
            em.write_punct("(");
          }
          emit_pat(em, ctx, body, *pat, true)?;
          if needs_parens {
            em.write_punct(")");
          }
        }
        hir_js::ForHead::Var(decl) => emit_var_decl(em, ctx, body, decl, false)?,
      }
      if *is_for_of {
        em.write_keyword("of");
      } else {
        em.write_keyword("in");
      }
      emit_expr_with_min_prec(em, ctx, body, *right, Prec::LOWEST)?;
      em.write_punct(")");
      emit_stmt_as_body(em, ctx, body, *inner)?;
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
      if var_decl_is_exported(ctx, body, decl) {
        em.write_keyword("export");
      }
      emit_var_decl(em, ctx, body, decl, true)?;
    }
    StmtKind::Labeled { label, body: inner } => {
      em.write_identifier(ctx.name(*label));
      em.write_punct(":");
      emit_stmt_as_body(em, ctx, body, *inner)?;
    }
    StmtKind::With {
      object,
      body: inner,
    } => {
      em.write_keyword("with");
      em.write_punct("(");
      emit_expr_with_min_prec(em, ctx, body, *object, Prec::LOWEST)?;
      em.write_punct(")");
      emit_stmt_as_body(em, ctx, body, *inner)?;
    }
    StmtKind::Debugger => {
      em.write_keyword("debugger");
      em.write_semicolon();
    }
    StmtKind::Empty => {}
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
  // Initializers are followed by `,` or `;`, so comma expressions must be
  // parenthesized to avoid being parsed as additional declarators.
  let assignment_expr_min_prec = Prec::new(OPERATORS[&OperatorName::Comma].precedence).tighter();
  match decl.kind {
    VarDeclKind::Const => em.write_keyword("const"),
    VarDeclKind::Let => em.write_keyword("let"),
    VarDeclKind::Var => em.write_keyword("var"),
    VarDeclKind::Using => em.write_keyword("using"),
    VarDeclKind::AwaitUsing => {
      em.write_keyword("await");
      em.write_keyword("using");
    }
  }
  for (idx, declarator) in decl.declarators.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    emit_pat(em, ctx, body, declarator.pat, false)?;
    if let Some(init) = declarator.init {
      em.write_punct("=");
      emit_expr_with_min_prec(em, ctx, body, init, assignment_expr_min_prec)?;
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
      // Default values are followed by `,` or `]` and must therefore treat the
      // comma operator as needing parentheses.
      let assignment_expr_min_prec =
        Prec::new(OPERATORS[&OperatorName::Comma].precedence).tighter();
      em.write_punct("[");
      for (idx, element) in array.elements.iter().enumerate() {
        if idx > 0 {
          em.write_punct(",");
        }
        if let Some(element) = element {
          emit_pat(em, ctx, body, element.pat, in_assignment)?;
          if let Some(default) = element.default_value {
            em.write_punct("=");
            emit_expr_with_min_prec(em, ctx, body, default, assignment_expr_min_prec)?;
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
      // Default values are followed by `,` or `}` and must therefore treat the
      // comma operator as needing parentheses.
      let assignment_expr_min_prec =
        Prec::new(OPERATORS[&OperatorName::Comma].precedence).tighter();
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
          emit_expr_with_min_prec(em, ctx, body, default, assignment_expr_min_prec)?;
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
      let assignment_expr_min_prec =
        Prec::new(OPERATORS[&OperatorName::Comma].precedence).tighter();
      emit_pat(em, ctx, body, *target, in_assignment)?;
      em.write_punct("=");
      emit_expr_with_min_prec(em, ctx, body, *default_value, assignment_expr_min_prec)?;
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
    ExprKind::Jsx(_) => PRIMARY_PRECEDENCE,
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
    ExprKind::ClassExpr {
      def: def_id,
      body: body_id,
      name,
    } => {
      if let Some(def) = ctx.def(*def_id) {
        emit_decorators(em, ctx, &def.decorators)?;
      }
      let class_body = ctx
        .body(*body_id)
        .ok_or_else(|| EmitError::unsupported("class body not found"))?;
      emit_class_like(em, ctx, class_body, name.map(|n| ctx.name(n)), true)?;
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
    ExprKind::Jsx(jsx) => emit_jsx_elem(em, ctx, body, jsx)?,
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

fn arrow_concise_body_needs_parens(expr: &Expr) -> bool {
  matches!(
    expr.kind,
    ExprKind::Object(_)
      | ExprKind::Binary {
        op: BinaryOp::Comma,
        ..
      }
  )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ContextualKeyword {
  Let,
  Using,
  AwaitUsing,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
enum NextTokenAfterKeyword {
  None,
  Brace,
  Bracket,
  IdentLike,
  In,
  Other,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ContextualKeywordStart {
  kind: ContextualKeyword,
  next: NextTokenAfterKeyword,
}

fn contextual_keyword_from_name(name: &str) -> Option<ContextualKeyword> {
  match name {
    "let" => Some(ContextualKeyword::Let),
    "using" => Some(ContextualKeyword::Using),
    _ => None,
  }
}

fn contextual_keyword_start_from_expr(
  ctx: &HirContext<'_>,
  body: &Body,
  expr_id: ExprId,
) -> Option<ContextualKeywordStart> {
  let expr = ctx.expr(body, expr_id);
  match &expr.kind {
    ExprKind::Ident(name) => {
      contextual_keyword_from_name(ctx.name(*name)).map(|kind| ContextualKeywordStart {
        kind,
        next: NextTokenAfterKeyword::None,
      })
    }
    ExprKind::Await { expr } => {
      if let Some(child_start) = contextual_keyword_start_from_expr(ctx, body, *expr) {
        if child_start.kind == ContextualKeyword::Using {
          Some(ContextualKeywordStart {
            kind: ContextualKeyword::AwaitUsing,
            next: child_start.next,
          })
        } else {
          None
        }
      } else {
        None
      }
    }
    ExprKind::Unary {
      op: UnaryOp::Await,
      expr,
    } => {
      if let Some(child_start) = contextual_keyword_start_from_expr(ctx, body, *expr) {
        if child_start.kind == ContextualKeyword::Using {
          Some(ContextualKeywordStart {
            kind: ContextualKeyword::AwaitUsing,
            next: child_start.next,
          })
        } else {
          None
        }
      } else {
        None
      }
    }
    ExprKind::Member(member) => propagate_keyword_start(
      ctx,
      body,
      member.object,
      match (&member.property, member.optional) {
        (ObjectKey::Computed(_), false) => NextTokenAfterKeyword::Bracket,
        _ => NextTokenAfterKeyword::Other,
      },
    ),
    ExprKind::Call(call) => {
      if call.is_new {
        None
      } else {
        propagate_keyword_start(ctx, body, call.callee, NextTokenAfterKeyword::Other)
      }
    }
    ExprKind::Binary { op, left, .. } => propagate_keyword_start(
      ctx,
      body,
      *left,
      if *op == BinaryOp::In {
        NextTokenAfterKeyword::In
      } else {
        NextTokenAfterKeyword::Other
      },
    ),
    ExprKind::Assignment { target, .. } => {
      propagate_keyword_start_from_pat(ctx, body, *target, NextTokenAfterKeyword::Other)
    }
    ExprKind::Conditional { test, .. } => {
      propagate_keyword_start(ctx, body, *test, NextTokenAfterKeyword::Other)
    }
    ExprKind::TypeAssertion { expr, .. }
    | ExprKind::NonNull { expr }
    | ExprKind::Satisfies { expr, .. } => {
      propagate_keyword_start(ctx, body, *expr, NextTokenAfterKeyword::Other)
    }
    _ => None,
  }
}

fn propagate_keyword_start(
  ctx: &HirContext<'_>,
  body: &Body,
  expr_id: ExprId,
  fallback_next: NextTokenAfterKeyword,
) -> Option<ContextualKeywordStart> {
  contextual_keyword_start_from_expr(ctx, body, expr_id).map(|mut start| {
    if start.next == NextTokenAfterKeyword::None {
      start.next = fallback_next;
    }
    start
  })
}

fn contextual_keyword_start_from_pat(
  ctx: &HirContext<'_>,
  body: &Body,
  pat_id: PatId,
) -> Option<ContextualKeywordStart> {
  let pat = ctx.pat(body, pat_id);
  match &pat.kind {
    PatKind::Ident(name) => {
      contextual_keyword_from_name(ctx.name(*name)).map(|kind| ContextualKeywordStart {
        kind,
        next: NextTokenAfterKeyword::None,
      })
    }
    PatKind::AssignTarget(expr) => contextual_keyword_start_from_expr(ctx, body, *expr),
    PatKind::Assign { target, .. } => contextual_keyword_start_from_pat(ctx, body, *target),
    PatKind::Rest(inner) => contextual_keyword_start_from_pat(ctx, body, **inner),
    PatKind::Array(_) | PatKind::Object(_) => None,
  }
}

fn propagate_keyword_start_from_pat(
  ctx: &HirContext<'_>,
  body: &Body,
  pat_id: PatId,
  fallback_next: NextTokenAfterKeyword,
) -> Option<ContextualKeywordStart> {
  contextual_keyword_start_from_pat(ctx, body, pat_id).map(|mut start| {
    if start.next == NextTokenAfterKeyword::None {
      start.next = fallback_next;
    }
    start
  })
}

fn for_init_expr_needs_parens(ctx: &HirContext<'_>, body: &Body, expr_id: ExprId) -> bool {
  contextual_keyword_start_from_expr(ctx, body, expr_id).map_or(false, |start| match start.kind {
    ContextualKeyword::AwaitUsing => true,
    ContextualKeyword::Let | ContextualKeyword::Using => matches!(
      start.next,
      NextTokenAfterKeyword::Brace
        | NextTokenAfterKeyword::Bracket
        | NextTokenAfterKeyword::IdentLike
    ),
  })
}

fn for_inof_assign_needs_parens(ctx: &HirContext<'_>, body: &Body, pat_id: PatId) -> bool {
  contextual_keyword_start_from_pat(ctx, body, pat_id).map_or(false, |start| match start.kind {
    ContextualKeyword::AwaitUsing => true,
    ContextualKeyword::Let | ContextualKeyword::Using => matches!(
      start.next,
      NextTokenAfterKeyword::Brace
        | NextTokenAfterKeyword::Bracket
        | NextTokenAfterKeyword::IdentLike
        | NextTokenAfterKeyword::In
        | NextTokenAfterKeyword::None
    ),
  })
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
