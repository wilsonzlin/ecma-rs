use std::collections::{HashMap, HashSet};
use std::panic::panic_any;
use std::sync::atomic::Ordering;
use std::sync::Arc;

use diagnostics::{FileId, Span, TextRange};
use hir_js::{BodyKind, ExprKind, TypeExprId, TypeExprKind};
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassStaticBlock};
use parse_js::ast::expr::pat::{ArrPat, ObjPat, Pat as AstPat};
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{VarDecl, VarDeclMode};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::ts_stmt::{EnumDecl, NamespaceBody, NamespaceDecl};
use parse_js::ast::type_expr::TypeExpr;

use super::super::super::flow_narrow::narrow_non_nullish;
use parse_js::operator::OperatorName;
use types_ts_interned::{
  ObjectType, Param, PropData, PropKey, Shape, Signature, TypeDisplay, TypeId, TypeKind,
  TypeParamDecl, TypeParamId, TypeStore,
};

use super::super::super::decls::HirDeclLowerer;
use super::super::super::flow_narrow::narrow_by_typeof;
use super::super::super::overload::callable_signatures;
use crate::codes;
use crate::lib_support::ScriptTarget;

use super::super::{
  awaited_type, contains_range, loc_to_range, ranges_overlap, Binding, Checker,
  ClassFieldInitializerContext, ClassStaticBlockInfo, FunctionInfo, Scope, SpiCtorState, VarInfo,
};

impl<'a> Checker<'a> {
  /// HIR-only var annotation when arenas are present.
  ///
  /// Covers primitives/literals/unions/arrays/tuples, named type refs,
  /// local/module `typeof`, `import("mod").T` (via program [`TypeResolver`]),
  /// function/constructor types, object type literals, mapped / conditional /
  /// template-literal / infer / predicate types (via body [`TypeResolver`] +
  /// live scope bindings). Residual AST: `typeof import(...)` (needs host
  /// resolution) and JSDoc `@type`.
  pub(crate) fn hir_var_annotation_ty(&mut self, pat_span: TextRange) -> Option<TypeId> {
    let ann = *self.hir_var_type_anns.get(&pat_span)?;
    self.hir_lower_type_expr_id(ann)
  }

  /// Lower a body-owned HIR [`TypeExprId`] (var/`as`/`satisfies`/Instantiation
  /// type-arg / function param/return annotations).
  ///
  /// Returns `None` when arenas are missing or the annotation is outside the
  /// supported HIR subset (caller falls back to AST `TypeLowerer`).
  pub(crate) fn hir_lower_type_expr_id(&mut self, ann: TypeExprId) -> Option<TypeId> {
    let arenas_by_def = self.type_arenas?;
    if !self.hir_type_expr_can_lower(ann) {
      return None;
    }
    let owner = self.body.owner;
    let typeof_bindings = self.typeof_bindings_snapshot();
    let (tp_bindings, next_tp) = self.hir_type_param_bindings();
    let mut lowerer = HirDeclLowerer::new(
      Arc::clone(&self.store),
      arenas_by_def,
      None,
      Default::default(),
      self.file,
      None,
      Default::default(),
      &mut self.diagnostics,
      None,
      None,
      None,
      None,
      None,
      None,
    )
    .with_typeof_bindings(typeof_bindings)
    .with_type_param_bindings(tp_bindings, next_tp);
    if let Some(resolver) = self.type_resolver.clone() {
      lowerer = lowerer.with_type_resolver(resolver);
    }
    Some(lowerer.lower_body_annotation(owner, ann, self.names))
  }

  /// Map this body's HIR type-parameter `NameId`s to the body checker's
  /// [`TypeParamId`]s (from AST `TypeLowerer` scopes). Empty when the body has
  /// no function/class type params or scopes are not yet pushed.
  ///
  /// Also binds enclosing class type parameters (`class C<T> { #foo: T; m(): T }`)
  /// once they have been pushed onto the AST `TypeLowerer` via
  /// [`Self::push_class_type_param_scope`]. Without that, HIR param/return
  /// annotations emit false TC2008 for class-`T` while the AST fallback would
  /// resolve them.
  fn hir_type_param_bindings(
    &self,
  ) -> (
    std::collections::HashMap<hir_js::NameId, types_ts_interned::TypeParamId>,
    u32,
  ) {
    let mut bindings = std::collections::HashMap::new();
    let next = self.lowerer.next_type_param_alloc();
    let tp_map = self.lowerer.type_param_map();
    // Prefer name→id from the AST TypeLowerer scope first. Member bodies push
    // class-`T` there even when the method's own arenas omit class type params;
    // do not early-return before this when `type_arenas` is missing.
    for (name, id) in tp_map.iter() {
      let Some(name_id) = self.names.get(name) else {
        continue;
      };
      bindings.insert(name_id, *id);
    }
    let Some(arenas_by_def) = self.type_arenas else {
      return (bindings, next);
    };
    let Some(arenas) = arenas_by_def.get(&self.body.owner) else {
      return (bindings, next);
    };
    if let Some(func) = self.body.function.as_ref() {
      for tp_id in func.type_params.iter() {
        let Some(tp) = arenas.type_params.get(tp_id.0 as usize) else {
          continue;
        };
        let Some(name) = self.names.resolve(tp.name) else {
          continue;
        };
        if let Some(id) = tp_map.get(name) {
          bindings.insert(tp.name, *id);
        }
      }
    }
    // Class body: owner arenas hold class type params (`class C<T>`).
    if matches!(self.body_kind, BodyKind::Class) {
      for tp in arenas.type_params.iter() {
        let Some(name) = self.names.resolve(tp.name) else {
          continue;
        };
        if let Some(id) = tp_map.get(name) {
          bindings.insert(tp.name, *id);
        }
      }
    }
    (bindings, next)
  }

  /// Push class type parameters into AST `TypeLowerer` + checker scopes.
  /// Returns whether a scope was pushed (caller must pop symmetrically).
  fn push_class_type_param_scope(&mut self, class_index: usize) -> bool {
    let names = self
      .index
      .classes
      .get(class_index)
      .map(|c| c.type_param_names.clone())
      .unwrap_or_default();
    if names.is_empty() {
      return false;
    }
    self.lowerer.push_type_param_scope();
    let decls = self.lowerer.register_named_type_params(&names);
    self.type_param_scopes.push(decls);
    true
  }

  fn pop_class_type_param_scope(&mut self) {
    self.type_param_scopes.pop();
    self.lowerer.pop_type_param_scope();
  }

  /// Whether `func` is this body's HIR [`hir_js::FunctionData`] (param pattern
  /// spans match). Nested function expressions refined while checking an outer
  /// body must not consume the outer `FunctionData` annotations.
  fn hir_function_is(&self, func: &Node<Func>) -> bool {
    let Some(hir_func) = self.body.function.as_ref() else {
      return false;
    };
    if hir_func.params.len() != func.stx.parameters.len() {
      return false;
    }
    for (hir_param, ast_param) in hir_func.params.iter().zip(func.stx.parameters.iter()) {
      let Some(hir_pat) = self.body.pats.get(hir_param.pat.0 as usize) else {
        return false;
      };
      let ast_span = loc_to_range(self.file, ast_param.stx.pattern.stx.pat.loc);
      if hir_pat.span != ast_span {
        return false;
      }
    }
    true
  }

  /// HIR `FunctionData.params[idx].type_annotation` when `func` is this body.
  pub(crate) fn hir_param_annotation_ty(
    &mut self,
    func: &Node<Func>,
    idx: usize,
  ) -> Option<TypeId> {
    if !self.hir_function_is(func) {
      return None;
    }
    let ann = self
      .body
      .function
      .as_ref()?
      .params
      .get(idx)?
      .type_annotation?;
    self.hir_lower_type_expr_id(ann)
  }

  /// HIR `FunctionData.return_type` when `func` is this body.
  pub(crate) fn hir_return_annotation_ty(&mut self, func: &Node<Func>) -> Option<TypeId> {
    if !self.hir_function_is(func) {
      return None;
    }
    let ann = self.body.function.as_ref()?.return_type?;
    self.hir_lower_type_expr_id(ann)
  }

  /// HIR `as T` / `as const` at `expr_span` → `(const_assertion, type_annotation)`.
  pub(crate) fn hir_type_assertion_at(
    &self,
    expr_span: TextRange,
  ) -> Option<(bool, Option<TypeExprId>)> {
    let expr_id = *self.expr_map.get(&expr_span)?;
    match &self.body.exprs.get(expr_id.0 as usize)?.kind {
      ExprKind::TypeAssertion {
        const_assertion,
        type_annotation,
        ..
      } => Some((*const_assertion, *type_annotation)),
      _ => None,
    }
  }

  /// HIR `satisfies T` annotation at `expr_span`.
  pub(crate) fn hir_satisfies_annotation_at(&self, expr_span: TextRange) -> Option<TypeExprId> {
    let expr_id = *self.expr_map.get(&expr_span)?;
    match &self.body.exprs.get(expr_id.0 as usize)?.kind {
      ExprKind::Satisfies {
        type_annotation, ..
      } => Some(*type_annotation),
      _ => None,
    }
  }

  /// HIR `expr<T, U>` type arguments at `expr_span`.
  pub(crate) fn hir_instantiation_type_args_at(
    &self,
    expr_span: TextRange,
  ) -> Option<&[TypeExprId]> {
    let expr_id = *self.expr_map.get(&expr_span)?;
    match &self.body.exprs.get(expr_id.0 as usize)?.kind {
      ExprKind::Instantiation { type_args, .. } => Some(type_args.as_slice()),
      _ => None,
    }
  }

  /// HIR `ExprKind::Jsx` element at `expr_span` (tag / attrs / children).
  pub(crate) fn hir_jsx_element_at(&self, expr_span: TextRange) -> Option<&hir_js::JsxElement> {
    let expr_id = *self.expr_map.get(&expr_span)?;
    match &self.body.exprs.get(expr_id.0 as usize)?.kind {
      ExprKind::Jsx(elem) => Some(elem),
      _ => None,
    }
  }

  /// Snapshot of in-scope value bindings for HIR `typeof` lowering.
  /// Later (inner) scopes win on name collisions.
  fn typeof_bindings_snapshot(&self) -> std::collections::HashMap<String, TypeId> {
    let mut map = std::collections::HashMap::new();
    for scope in &self.scopes {
      for (name, binding) in &scope.bindings {
        map.insert(name.clone(), binding.ty);
      }
    }
    map
  }

  /// Annotations that [`HirDeclLowerer`] can lower for body var decls /
  /// type assertions / `satisfies` / Instantiation type args / function
  /// param+return annotations.
  fn hir_type_expr_can_lower(&self, id: TypeExprId) -> bool {
    let Some(arenas_by_def) = self.type_arenas else {
      return false;
    };
    let Some(arenas) = arenas_by_def.get(&self.body.owner) else {
      return false;
    };
    let Some(ty) = arenas.type_exprs.get(id.0 as usize) else {
      return false;
    };
    match &ty.kind {
      TypeExprKind::Any
      | TypeExprKind::Unknown
      | TypeExprKind::Never
      | TypeExprKind::Void
      | TypeExprKind::Null
      | TypeExprKind::Undefined
      | TypeExprKind::Object
      | TypeExprKind::Boolean
      | TypeExprKind::Number
      | TypeExprKind::String
      | TypeExprKind::BigInt
      | TypeExprKind::Symbol
      | TypeExprKind::UniqueSymbol
      | TypeExprKind::Literal(_)
      | TypeExprKind::This
      | TypeExprKind::Intrinsic => true,
      // `typeof` of a local/module value is HIR-ok (body typeof_bindings /
      // TypeResolver). `typeof import("...")` needs host resolution — residual AST.
      TypeExprKind::TypeQuery(name) => !matches!(
        name,
        hir_js::TypeName::Import(_) | hir_js::TypeName::ImportExpr
      ),
      TypeExprKind::TypeRef(r) => r.type_args.iter().all(|a| self.hir_type_expr_can_lower(*a)),
      TypeExprKind::Parenthesized(inner) | TypeExprKind::KeyOf(inner) => {
        self.hir_type_expr_can_lower(*inner)
      }
      TypeExprKind::Array(arr) => self.hir_type_expr_can_lower(arr.element),
      TypeExprKind::Union(members) | TypeExprKind::Intersection(members) => {
        members.iter().all(|m| self.hir_type_expr_can_lower(*m))
      }
      TypeExprKind::Tuple(tuple) => tuple
        .elements
        .iter()
        .all(|elem| self.hir_type_expr_can_lower(elem.ty)),
      TypeExprKind::IndexedAccess {
        object_type,
        index_type,
      } => self.hir_type_expr_can_lower(*object_type) && self.hir_type_expr_can_lower(*index_type),
      TypeExprKind::Function(func) | TypeExprKind::Constructor(func) => {
        func
          .type_params
          .iter()
          .all(|tp| self.hir_type_param_can_lower(*tp))
          && func
            .params
            .iter()
            .all(|p| self.hir_type_expr_can_lower(p.ty))
          && self.hir_type_expr_can_lower(func.ret)
      }
      TypeExprKind::TypeLiteral(obj) => obj
        .members
        .iter()
        .all(|m| self.hir_type_member_can_lower(*m)),
      TypeExprKind::Conditional(cond) => {
        self.hir_type_expr_can_lower(cond.check_type)
          && self.hir_type_expr_can_lower(cond.extends_type)
          && self.hir_type_expr_can_lower(cond.true_type)
          && self.hir_type_expr_can_lower(cond.false_type)
      }
      TypeExprKind::Mapped(mapped) => {
        self.hir_type_param_can_lower(mapped.type_param)
          && self.hir_type_expr_can_lower(mapped.constraint)
          && self.hir_type_expr_can_lower(mapped.value_type)
          && mapped
            .name_type
            .map_or(true, |n| self.hir_type_expr_can_lower(n))
      }
      TypeExprKind::TemplateLiteral(tpl) => tpl
        .spans
        .iter()
        .all(|span| self.hir_type_expr_can_lower(span.type_expr)),
      TypeExprKind::Infer(param) => self.hir_type_param_can_lower(*param),
      TypeExprKind::TypePredicate(pred) => pred
        .type_annotation
        .map_or(true, |ann| self.hir_type_expr_can_lower(ann)),
      // `import("mod").T` lowers via [`TypeResolver::resolve_import_type`] on the
      // body [`HirDeclLowerer`] (program-grade resolver; DeclHost optional).
      // (`typeof import(...)` is still gated above via `TypeQuery`.)
      TypeExprKind::Import(_) => self.type_resolver.is_some(),
    }
  }

  fn hir_type_param_can_lower(&self, id: hir_js::TypeParamId) -> bool {
    let Some(arenas_by_def) = self.type_arenas else {
      return false;
    };
    let Some(arenas) = arenas_by_def.get(&self.body.owner) else {
      return false;
    };
    let Some(tp) = arenas.type_params.get(id.0 as usize) else {
      return false;
    };
    tp.constraint
      .map_or(true, |c| self.hir_type_expr_can_lower(c))
      && tp.default.map_or(true, |d| self.hir_type_expr_can_lower(d))
  }

  fn hir_type_member_can_lower(&self, id: hir_js::TypeMemberId) -> bool {
    let Some(arenas_by_def) = self.type_arenas else {
      return false;
    };
    let Some(arenas) = arenas_by_def.get(&self.body.owner) else {
      return false;
    };
    let Some(member) = arenas.type_members.get(id.0 as usize) else {
      return false;
    };
    match &member.kind {
      hir_js::TypeMemberKind::Property(prop) => prop
        .type_annotation
        .map_or(true, |t| self.hir_type_expr_can_lower(t)),
      hir_js::TypeMemberKind::Method(method) => {
        method
          .type_params
          .iter()
          .all(|tp| self.hir_type_param_can_lower(*tp))
          && method
            .params
            .iter()
            .all(|p| self.hir_type_expr_can_lower(p.ty))
          && method
            .return_type
            .map_or(true, |r| self.hir_type_expr_can_lower(r))
      }
      hir_js::TypeMemberKind::Constructor(sig) | hir_js::TypeMemberKind::CallSignature(sig) => {
        sig
          .type_params
          .iter()
          .all(|tp| self.hir_type_param_can_lower(*tp))
          && sig
            .params
            .iter()
            .all(|p| self.hir_type_expr_can_lower(p.ty))
          && sig
            .return_type
            .map_or(true, |r| self.hir_type_expr_can_lower(r))
      }
      hir_js::TypeMemberKind::IndexSignature(idx) => {
        self.hir_type_expr_can_lower(idx.parameter_type)
          && self.hir_type_expr_can_lower(idx.type_annotation)
      }
      hir_js::TypeMemberKind::Getter(getter) => getter
        .return_type
        .map_or(true, |r| self.hir_type_expr_can_lower(r)),
      hir_js::TypeMemberKind::Setter(setter) => self.hir_type_expr_can_lower(setter.parameter.ty),
      hir_js::TypeMemberKind::Mapped(mapped) => {
        self.hir_type_param_can_lower(mapped.type_param)
          && self.hir_type_expr_can_lower(mapped.constraint)
          && self.hir_type_expr_can_lower(mapped.value_type)
          && mapped
            .name_type
            .map_or(true, |n| self.hir_type_expr_can_lower(n))
      }
    }
  }

  /// Prefer HIR `VarDeclarator.type_annotation`; residual AST / JSDoc otherwise.
  pub(crate) fn var_annotation_ty(
    &mut self,
    pat_span: TextRange,
    ast_ann: Option<&Node<TypeExpr>>,
    jsdoc_loc: parse_js::loc::Loc,
  ) -> Option<TypeId> {
    if let Some(ty) = self.hir_var_annotation_ty(pat_span) {
      return Some(ty);
    }
    ast_ann
      .map(|ann| {
        self
          .lookup_typeof_query_binding(ann)
          .unwrap_or_else(|| self.lowerer.lower_type_expr(ann))
      })
      .or_else(|| self.jsdoc_declared_type(jsdoc_loc))
  }

  pub(crate) fn binding_name_range(&self, pat: &Node<AstPat>) -> TextRange {
    match pat.stx.as_ref() {
      AstPat::Id(id) => {
        let range = loc_to_range(self.file, id.loc);
        let len = id.stx.name.len() as u32;
        TextRange::new(range.start, range.start.saturating_add(len))
      }
      _ => loc_to_range(self.file, pat.loc),
    }
  }

  pub(crate) fn report_implicit_any(&mut self, range: TextRange, name: Option<&str>) {
    if !self.no_implicit_any {
      return;
    }
    if !self.implicit_any_reported.insert(range) {
      return;
    }
    self.diagnostics.push(codes::IMPLICIT_ANY.error(
      codes::implicit_any_message(name),
      Span::new(self.file, range),
    ));
  }

  pub(crate) fn report_implicit_any_in_pat(&mut self, pat: &Node<AstPat>) {
    match pat.stx.as_ref() {
      AstPat::Id(id) => {
        let range = self.binding_name_range(pat);
        self.report_implicit_any(range, Some(&id.stx.name));
      }
      AstPat::Arr(arr) => {
        for elem in arr.stx.elements.iter().flatten() {
          self.report_implicit_any_in_pat(&elem.target);
        }
        if let Some(rest) = &arr.stx.rest {
          self.report_implicit_any_in_pat(rest);
        }
      }
      AstPat::Obj(obj) => {
        for prop in obj.stx.properties.iter() {
          self.report_implicit_any_in_pat(&prop.stx.target);
        }
        if let Some(rest) = &obj.stx.rest {
          self.report_implicit_any_in_pat(rest);
        }
      }
      AstPat::AssignTarget(_) => {}
    }
  }

  pub(crate) fn check_abstract_property_initializers(&mut self) {
    for class in self.index.classes.iter() {
      for (name, span) in class.abstract_props_with_initializer.iter() {
        self
          .diagnostics
          .push(codes::ABSTRACT_PROPERTY_INITIALIZER.error(
            format!("Property '{name}' cannot have an initializer because it is marked abstract."),
            Span::new(self.file, *span),
          ));
      }
    }
  }

  /// TS2564 under `strictPropertyInitialization` + `strictNullChecks`.
  ///
  /// Mirrors tsc `checkPropertyInitialization`: non-static, non-abstract,
  /// non-`!`, non-ambient instance properties whose type is not any/unknown and
  /// does not contain `undefined` must be assigned by an initializer or on
  /// every constructor exit path. String/numeric literal keys are skipped.
  pub(crate) fn check_strict_property_initialization(&mut self) {
    if !self.strict_property_initialization || !self.strict_null_checks {
      return;
    }
    for class_index in 0..self.index.classes.len() {
      let Some(required) = self.spi_required_props(class_index) else {
        continue;
      };
      if required.is_empty() {
        continue;
      }
      let assigned = self.spi_props_assigned_in_constructor(class_index);
      for (name, span) in required {
        if assigned.contains(&name) {
          continue;
        }
        self
          .diagnostics
          .push(codes::PROPERTY_NOT_DEFINITELY_ASSIGNED.error(
            format!(
              "Property '{name}' has no initializer and is not definitely assigned in the constructor."
            ),
            Span::new(self.file, span),
          ));
      }
    }
  }

  /// Properties on `class_index` that need SPI definite assignment, or `None`
  /// when the class is ambient / SPI is inactive for it.
  fn spi_required_props(&mut self, class_index: usize) -> Option<Vec<(String, TextRange)>> {
    if self.index.classes.get(class_index)?.declare {
      return None;
    }
    let candidates: Vec<(String, TextRange, Option<&'a Node<TypeExpr>>)> = self
      .index
      .classes
      .get(class_index)?
      .instance_fields
      .iter()
      .filter(|f| {
        f.spi_checked_name
          && !f.optional
          && !f.has_initializer
          && !f.definite_assignment
          && !f.abstract_
          && !f.declare_
      })
      .map(|f| (f.name.clone(), f.key_range, f.type_annotation))
      .collect();
    // Class-`T` on field anns (`#foo: T`) must resolve during TopLevel SPI
    // (no member body has pushed class type params yet).
    let pushed = self.push_class_type_param_scope(class_index);
    let mut required = Vec::new();
    for (name, span, ann) in candidates {
      let needs = match ann {
        // Implicit any — tsc treats any as exempt from SPI.
        None => false,
        Some(ann) => {
          let ty = self.lowerer.lower_type_expr(ann);
          self.spi_type_needs_initialization(ty)
        }
      };
      if needs {
        required.push((name, span));
      }
    }
    if pushed {
      self.pop_class_type_param_scope();
    }
    Some(required)
  }

  /// Whether a property type requires definite assignment under SPI.
  /// Exempt: `any` / `unknown`, or any type that contains `undefined`.
  fn spi_type_needs_initialization(&self, ty: TypeId) -> bool {
    fn contains_undefined(
      store: &types_ts_interned::TypeStore,
      ty: TypeId,
      seen: &mut HashSet<TypeId>,
    ) -> bool {
      let ty = store.canon(ty);
      if !seen.insert(ty) {
        return false;
      }
      match store.type_kind(ty) {
        TypeKind::Undefined => true,
        TypeKind::Union(members) => members.iter().any(|m| contains_undefined(store, *m, seen)),
        _ => false,
      }
    }
    let ty = self.store.canon(ty);
    if matches!(self.store.type_kind(ty), TypeKind::Any | TypeKind::Unknown) {
      return false;
    }
    let mut seen = HashSet::new();
    !contains_undefined(&self.store, ty, &mut seen)
  }

  /// Props definitely assigned on all constructor exit paths (plus param props).
  fn spi_props_assigned_in_constructor(&self, class_index: usize) -> HashSet<String> {
    let Some(class) = self.index.classes.get(class_index) else {
      return HashSet::new();
    };
    let seed: HashSet<String> = class.instance_param_props.iter().cloned().collect();
    let Some(ctor) = class.constructor else {
      return seed;
    };
    let body_stmts = match ctor.stx.body.as_ref() {
      Some(FuncBody::Block(stmts)) => stmts.as_slice(),
      Some(FuncBody::Expression(_)) | None => return seed,
    };
    let analysis = spi_analyze_stmts(body_stmts, &seed);
    match analysis.exit_assigned {
      Some(set) => set,
      // No reachable exit (e.g. always throw): vacuously assigned.
      None => class
        .instance_fields
        .iter()
        .map(|f| f.name.clone())
        .chain(seed)
        .collect(),
    }
  }

  /// Begin TS2565 tracking when entering a constructor body.
  pub(crate) fn begin_spi_ctor(&mut self, class_index: usize) {
    if !self.strict_property_initialization || !self.strict_null_checks {
      return;
    }
    let Some(required_vec) = self.spi_required_props(class_index) else {
      return;
    };
    let required: HashSet<String> = required_vec.into_iter().map(|(n, _)| n).collect();
    if required.is_empty() {
      return;
    }
    let mut assigned = HashSet::new();
    if let Some(class) = self.index.classes.get(class_index) {
      assigned.extend(class.instance_param_props.iter().cloned());
    }
    self.spi_ctor = Some(SpiCtorState { required, assigned });
  }

  pub(crate) fn end_spi_ctor(&mut self) {
    self.spi_ctor = None;
  }

  pub(crate) fn spi_note_assigned(&mut self, prop: &str) {
    if let Some(state) = self.spi_ctor.as_mut() {
      if state.required.contains(prop) {
        state.assigned.insert(prop.to_string());
      }
    }
  }

  pub(crate) fn check_property_used_before_assigned(
    &mut self,
    obj: &Node<AstExpr>,
    prop: &str,
    prop_span: TextRange,
  ) {
    if !matches!(obj.stx.as_ref(), AstExpr::This(_)) {
      return;
    }
    let Some(state) = self.spi_ctor.as_ref() else {
      return;
    };
    if !state.required.contains(prop) || state.assigned.contains(prop) {
      return;
    }
    self
      .diagnostics
      .push(codes::PROPERTY_USED_BEFORE_ASSIGNED.error(
        format!("Property '{prop}' is used before being assigned."),
        Span::new(self.file, prop_span),
      ));
  }

  /// Class index when the current check is inside class initialization
  /// (constructor body or instance field initializer), for TS2715.
  pub(crate) fn class_initialization_index(&self) -> Option<usize> {
    if let Some(ctx) = self.class_field_initializer.as_ref() {
      if ctx.is_static {
        return None;
      }
      return Some(ctx.class_index);
    }
    self.constructor_class_index
  }

  pub(crate) fn check_abstract_property_in_constructor(
    &mut self,
    obj: &Node<AstExpr>,
    prop: &str,
    prop_span: TextRange,
  ) {
    if !matches!(obj.stx.as_ref(), AstExpr::This(_)) {
      return;
    }
    let Some(class_index) = self.class_initialization_index() else {
      return;
    };
    let Some(class_name) = self
      .index
      .unresolved_abstract_instance_prop(class_index, prop)
    else {
      return;
    };
    let class_label = if class_name.is_empty() {
      "(anonymous)".to_string()
    } else {
      class_name.to_string()
    };
    self
      .diagnostics
      .push(codes::ABSTRACT_PROPERTY_IN_CONSTRUCTOR.error(
        format!(
          "Abstract property '{prop}' in class '{class_label}' cannot be accessed in the constructor."
        ),
        Span::new(self.file, prop_span),
      ));
    // tsc also emits TS2729 for abstract instance props read from a field
    // initializer (`other = this.prop`): the abstract member is never
    // initialized, so it counts as used-before-initialization.
    if self.class_field_initializer.is_some() {
      self
        .diagnostics
        .push(codes::PROPERTY_USED_BEFORE_INITIALIZATION.error(
          format!("Property '{prop}' is used before its initialization."),
          Span::new(self.file, prop_span),
        ));
    }
  }

  pub(crate) fn check_abstract_props_destructured_from_this(
    &mut self,
    obj: &Node<parse_js::ast::expr::pat::ObjPat>,
    init: &Node<AstExpr>,
  ) {
    if !matches!(init.stx.as_ref(), AstExpr::This(_)) {
      return;
    }
    if self.class_initialization_index().is_none() {
      return;
    }
    for prop in obj.stx.properties.iter() {
      let ClassOrObjKey::Direct(key) = &prop.stx.key else {
        continue;
      };
      let name = key.stx.key.as_str();
      let range = loc_to_range(self.file, key.loc);
      let prop_span = TextRange::new(
        range.start,
        range.start.saturating_add(name.len() as u32).min(range.end),
      );
      self.check_abstract_property_in_constructor(init, name, prop_span);
    }
  }

  /// TS2393 — duplicate method implementations within each class body
  /// (tsc overload group with more than one body).
  pub(crate) fn check_class_duplicate_function_implementations(&mut self) {
    use super::super::ast_index::ClassValueMemberKind;

    for class in self.index.classes.iter() {
      // (name, is_static) → method decls in source order (deterministic keys).
      let mut groups: HashMap<(String, bool), Vec<(TextRange, bool)>> = HashMap::new();
      let mut order: Vec<(String, bool)> = Vec::new();
      for decl in class.value_member_decls.iter() {
        if decl.kind != ClassValueMemberKind::Method || decl.name == "constructor" {
          continue;
        }
        let key = (decl.name.clone(), decl.is_static);
        if let std::collections::hash_map::Entry::Vacant(slot) = groups.entry(key.clone()) {
          slot.insert(Vec::new());
          order.push(key.clone());
        }
        groups
          .get_mut(&key)
          .expect("group just inserted")
          .push((decl.key_range, decl.has_body));
      }
      for key in order {
        let Some(decls) = groups.remove(&key) else {
          continue;
        };
        let body_count = decls.iter().filter(|(_, has_body)| *has_body).count();
        if body_count < 2 {
          continue;
        }
        for (range, _) in decls {
          self
            .diagnostics
            .push(codes::DUPLICATE_FUNCTION_IMPLEMENTATION.error(
              "Duplicate function implementation.",
              Span::new(self.file, range),
            ));
        }
      }
    }
  }

  /// TS2717 — later class fields must match the type of the first same-name
  /// value declaration (method or field) on the same side.
  pub(crate) fn check_class_subsequent_property_types(&mut self) {
    use super::super::ast_index::{ClassValueMemberDecl, ClassValueMemberKind};
    use crate::check::widen::widen_literal;

    for class_index in 0..self.index.classes.len() {
      // Nested classes are not in the TopLevel type-resolver's local bindings.
      // Lowering their method signatures here (e.g. `m(x: Derived)`) falsely
      // emits TC2008 for the class's own name. Nested TS2717 is covered when
      // those class/method bodies are checked with parent Decl seeding.
      if self.index.classes[class_index].parent_class_index.is_some() {
        continue;
      }
      let decls: Vec<ClassValueMemberDecl<'_>> =
        self.index.classes[class_index].value_member_decls.clone();
      // Class-`T` must be in scope for field/method anns (`#foo: T`, `#bar(): T`).
      let pushed = self.push_class_type_param_scope(class_index);
      // (name, is_static) → type of the first value declaration
      let mut first_ty: HashMap<(String, bool), TypeId> = HashMap::new();
      for decl in decls {
        let key = (decl.name.clone(), decl.is_static);
        let ty = match decl.kind {
          ClassValueMemberKind::Method => {
            let Some(func) = decl.func else {
              continue;
            };
            self.class_method_property_type(func)
          }
          ClassValueMemberKind::Field => {
            if let Some(ann) = decl.type_annotation {
              self.lowerer.lower_type_expr(ann)
            } else if let Some(init) = decl.initializer {
              // TopLevel subsequent-property pass re-checks field inits; keep
              // lexical private access (TS18013) scoped to the declaring class
              // (e.g. `static #f = D.#m()` inside `const C = class D { … }`).
              // Diagnostics from this re-check are drained: the pass runs with
              // the *current* body's scope, which cannot see enclosing-function
              // bindings of lexically nested classes (`localTypes2.ts` —
              // `class C { x = x; }` inside `function f(x)` falsely TS2304'd).
              // Genuine init diagnostics are reported by the field-initializer
              // body check with the correct lexical scope.
              let prev_enclosing = self.enclosing_class_index;
              self.enclosing_class_index = Some(class_index);
              let diag_mark = self.diagnostics.len();
              let init_ty = self.check_expr(init);
              self.diagnostics.truncate(diag_mark);
              self.enclosing_class_index = prev_enclosing;
              widen_literal(self.store.as_ref(), init_ty)
            } else {
              self.store.primitive_ids().any
            }
          }
        };
        let ty = self.store.canon(ty);
        if let Some(&prev) = first_ty.get(&key) {
          if decl.kind != ClassValueMemberKind::Field {
            // Methods use TS2393 for duplicate implementations; skip here.
            continue;
          }
          if prev != ty {
            self.diagnostics.push(codes::SUBSEQUENT_PROPERTY_DECLARATIONS.error(
              format!(
                "Subsequent property declarations must have the same type.  Property '{}' must be of type '{}', but here has type '{}'.",
                decl.name,
                TypeDisplay::new(self.store.as_ref(), prev),
                TypeDisplay::new(self.store.as_ref(), ty),
              ),
              Span::new(self.file, decl.key_range),
            ));
          }
        } else {
          first_ty.insert(key, ty);
        }
      }
      if pushed {
        self.pop_class_type_param_scope();
      }
    }
  }

  /// Declared type of a class method when used as a property type (TS2717).
  ///
  /// Unannotated returns default to `void` (tsc method inference for empty /
  /// no-return bodies), matching synthesized class `this` shapes.
  fn class_method_property_type(&mut self, func: &Node<Func>) -> TypeId {
    let ty = self.function_type(func);
    if func.stx.return_type.is_some() {
      return ty;
    }
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::Callable { overloads } => {
        let Some(&sig_id) = overloads.first() else {
          return ty;
        };
        let mut sig = self.store.signature(sig_id);
        if sig.ret != prim.unknown {
          return ty;
        }
        sig.ret = prim.void;
        let new_sig = self.store.intern_signature(sig);
        self.store.intern_type(TypeKind::Callable {
          overloads: vec![new_sig],
        })
      }
      _ => ty,
    }
  }

  /// TS18012 / TS18028 — reserved `#constructor` and ES2015+ requirement for
  /// private class members (tsc binder + `checkGrammarProperty` /
  /// `checkGrammarMethod` / `checkGrammarAccessor`).
  pub(crate) fn check_class_private_name_grammar(&mut self) {
    use super::super::ast_index::PrivateMemberKind;
    let es2015_ok = !matches!(self.target, ScriptTarget::Es3 | ScriptTarget::Es5);
    // tsc: async generators require the global `AsyncIterableIterator` type
    // (lib es2018+). This is a *lib availability* check, not a target check:
    // `--target es2015 --lib esnext` accepts async generators (oracle:
    // `async *#baz() {}` errors only when the global is actually missing).
    if self.index.uses_async_generator {
      let has_async_iterable_iterator = self
        .type_resolver
        .as_ref()
        .and_then(|resolver| resolver.resolve_type_name(&["AsyncIterableIterator".to_string()]))
        .is_some();
      if !has_async_iterable_iterator {
        self.diagnostics.push(codes::CANNOT_FIND_GLOBAL_TYPE.error(
          "Cannot find global type 'AsyncIterableIterator'.",
          Span::new(FileId(u32::MAX), TextRange::new(0, 0)),
        ));
      }
    }
    for class in self.index.classes.iter() {
      for decl in class.private_name_decls.iter() {
        if decl.name == "#constructor" {
          self
            .diagnostics
            .push(codes::PRIVATE_CONSTRUCTOR_RESERVED.error(
              "'#constructor' is a reserved word.",
              Span::new(self.file, decl.key_range),
            ));
        }
        if !es2015_ok {
          self
            .diagnostics
            .push(codes::PRIVATE_IDENTIFIERS_REQUIRE_ES2015.error(
              "Private identifiers are only available when targeting ECMAScript 2015 and higher.",
              Span::new(self.file, decl.key_range),
            ));
        }
        // tsc `checkGrammarModifiers` private-identifier rules
        // (privateNamesIncompatibleModifiers). Primary span is the modifier
        // keyword (not `#name`).
        let keyword_span = |kw: &str| {
          Span::new(
            self.file,
            TextRange::new(
              decl.member_start,
              decl.member_start.saturating_add(kw.len() as u32),
            ),
          )
        };
        if let Some(kw) = decl.accessibility_keyword {
          self
            .diagnostics
            .push(codes::ACCESSIBILITY_WITH_PRIVATE_IDENTIFIER.error(
              "An accessibility modifier cannot be used with a private identifier.",
              keyword_span(kw),
            ));
        }
        if decl.declare_ {
          // Fields: TS18019; methods/accessors: TS1031 (declare cannot appear
          // on class elements of this kind) — tsc emits 1031 for non-fields.
          if matches!(decl.kind, PrivateMemberKind::Field) {
            self
              .diagnostics
              .push(codes::MODIFIER_WITH_PRIVATE_IDENTIFIER.error(
                "'declare' modifier cannot be used with a private identifier.",
                keyword_span("declare"),
              ));
          } else {
            self
              .diagnostics
              .push(codes::MODIFIER_ON_WRONG_CLASS_ELEMENT.error(
                "'declare' modifier cannot appear on class elements of this kind.",
                keyword_span("declare"),
              ));
          }
        }
        if decl.abstract_ {
          self
            .diagnostics
            .push(codes::MODIFIER_WITH_PRIVATE_IDENTIFIER.error(
              "'abstract' modifier cannot be used with a private identifier.",
              keyword_span("abstract"),
            ));
        }
        if decl.readonly && !matches!(decl.kind, PrivateMemberKind::Field) {
          self
            .diagnostics
            .push(codes::READONLY_MODIFIER_INVALID.error(
              "'readonly' modifier can only appear on a property declaration or index signature.",
              keyword_span("readonly"),
            ));
        }
        if decl.async_on_accessor {
          self
            .diagnostics
            .push(codes::MODIFIER_CANNOT_BE_USED_HERE.error(
              "'async' modifier cannot be used here.",
              keyword_span("async"),
            ));
        }
        // TS1029: `async static` (wrong order). Span is the `static` keyword.
        if decl.async_before_static {
          // `async` was recovered before `static`; underline `static` (6 chars)
          // which follows `async` (+ optional whitespace). Prefer scanning the
          // member prefix when source is available; otherwise member_start+6.
          let static_span = if let Some(source) = self.jsdoc_source {
            let start = decl.member_start as usize;
            let end = (decl.key_range.start as usize).min(source.len());
            let prefix = if start < end { &source[start..end] } else { "" };
            prefix
              .find("static")
              .map(|rel| {
                let s = decl.member_start.saturating_add(rel as u32);
                Span::new(self.file, TextRange::new(s, s.saturating_add(6)))
              })
              .unwrap_or_else(|| keyword_span("static"))
          } else {
            // member starts at `async`; `static` is typically at +6 (`async `).
            let s = decl.member_start.saturating_add(6);
            Span::new(self.file, TextRange::new(s, s.saturating_add(6)))
          };
          self.diagnostics.push(codes::MODIFIER_MUST_PRECEDE.error(
            "'static' modifier must precede 'async' modifier.",
            static_span,
          ));
        }
        // checkJs: `@public` / `@private` / `@protected` on `#` members → TS18010
        // (privateNamesIncompatibleModifiersJs). Span matches tsc: `@tag` … `*/`.
        if decl.accessibility_keyword.is_none() {
          if let Some(source) = self.jsdoc_source {
            if let Some(tags) = crate::jsdoc::leading_jsdoc_tags(source, decl.member_start) {
              if tags.accessibility.is_some() {
                let range = tags
                  .accessibility_span
                  .map(|(s, e)| TextRange::new(s, e))
                  .unwrap_or(decl.key_range);
                self
                  .diagnostics
                  .push(codes::ACCESSIBILITY_WITH_PRIVATE_IDENTIFIER.error(
                    "An accessibility modifier cannot be used with a private identifier.",
                    Span::new(self.file, range),
                  ));
              }
            }
          }
        }
      }
    }
  }

  /// TS18009 / TS18029 — private identifiers illegal in parameter / variable
  /// binding names (tsc parser diagnostics; parse-js recovers).
  pub(crate) fn check_private_name_in_binding_pat(&mut self, pat: &Node<AstPat>, as_param: bool) {
    match pat.stx.as_ref() {
      AstPat::Id(id) if id.stx.name.starts_with('#') => {
        let range = self.binding_name_range(pat);
        let span = Span::new(self.file, range);
        if as_param {
          self.diagnostics.push(
            codes::PRIVATE_IDENTIFIERS_AS_PARAMETERS
              .error("Private identifiers cannot be used as parameters.", span),
          );
        } else {
          self
            .diagnostics
            .push(codes::PRIVATE_IDENTIFIERS_IN_VARIABLE_DECLARATIONS.error(
              "Private identifiers are not allowed in variable declarations.",
              span,
            ));
        }
      }
      AstPat::Arr(arr) => {
        for elem in arr.stx.elements.iter().flatten() {
          self.check_private_name_in_binding_pat(&elem.target, as_param);
        }
        if let Some(rest) = &arr.stx.rest {
          self.check_private_name_in_binding_pat(rest, as_param);
        }
      }
      AstPat::Obj(obj) => {
        for prop in obj.stx.properties.iter() {
          self.check_private_name_in_binding_pat(&prop.stx.target, as_param);
        }
        if let Some(rest) = &obj.stx.rest {
          self.check_private_name_in_binding_pat(rest, as_param);
        }
      }
      AstPat::Id(_) | AstPat::AssignTarget(_) => {}
    }
  }

  /// TS18024 — private identifier enum member names.
  pub(crate) fn check_enum_private_member_names(&mut self, en: &Node<EnumDecl>) {
    for member in en.stx.members.iter() {
      if !member.stx.name.starts_with('#') {
        continue;
      }
      let range = loc_to_range(self.file, member.loc);
      let len = member.stx.name.len() as u32;
      let name_range = TextRange::new(range.start, range.start.saturating_add(len));
      self
        .diagnostics
        .push(codes::ENUM_MEMBER_PRIVATE_IDENTIFIER.error(
          "An enum member cannot be named with a private identifier.",
          Span::new(self.file, name_range),
        ));
    }
  }

  /// TS2300 / TS2804 — private-identifier uniqueness within each class body
  /// (tsc `checkClassForDuplicateDeclarations` + binder dual-report for
  /// conflicting symbol excludes).
  pub(crate) fn check_class_private_name_uniqueness(&mut self) {
    use super::super::ast_index::PrivateMemberKind;

    // DeclarationMeaning bits from tsc checker.ts.
    const GET: u8 = 1;
    const SET: u8 = 2;
    const METHOD: u8 = 8;
    const PRIVATE_STATIC: u8 = 16;
    const GET_OR_SET: u8 = GET | SET;

    let classes: Vec<Vec<_>> = self
      .index
      .classes
      .iter()
      .map(|c| c.private_name_decls.clone())
      .collect();

    for decls in classes {
      // name → (meaning, first key_range, first kind)
      let mut seen: HashMap<String, (u8, TextRange, PrivateMemberKind)> = HashMap::new();
      for decl in decls {
        let base = match decl.kind {
          PrivateMemberKind::Field => GET_OR_SET,
          PrivateMemberKind::Method => METHOD,
          PrivateMemberKind::Getter => GET,
          PrivateMemberKind::Setter => SET,
        };
        let meaning = if decl.is_static {
          base | PRIVATE_STATIC
        } else {
          base
        };
        let Some(&(prev, prev_range, prev_kind)) = seen.get(&decl.name) else {
          seen.insert(decl.name.clone(), (meaning, decl.key_range, decl.kind));
          continue;
        };
        if (prev & PRIVATE_STATIC) != (meaning & PRIVATE_STATIC) {
          self.diagnostics.push(codes::DUPLICATE_PRIVATE_STATIC_INSTANCE.error(
            format!(
              "Duplicate identifier '{}'. Static and instance elements cannot share the same private name.",
              decl.name
            ),
            Span::new(self.file, decl.key_range),
          ));
          continue;
        }
        let prev_is_method = (prev & METHOD) != 0;
        let is_method = (meaning & METHOD) != 0;
        let emit_2300 = if prev_is_method || is_method {
          // Method/method may be overloads (TS2393 later); method vs non-method
          // is a duplicate identifier.
          prev_is_method != is_method
        } else if (prev & meaning & !PRIVATE_STATIC) != 0 {
          true
        } else {
          // Compatible pair (e.g. getter + setter): merge meanings.
          seen.insert(decl.name.clone(), (prev | meaning, prev_range, prev_kind));
          false
        };
        if !emit_2300 {
          continue;
        }
        let msg = format!("Duplicate identifier '{}'.", decl.name);
        self.diagnostics.push(
          codes::DUPLICATE_IDENTIFIER.error(msg.clone(), Span::new(self.file, decl.key_range)),
        );
        // Binder dual-report when the new declaration's excludes would conflict
        // with the previous symbol (PropertyExcludes is None, so fields never
        // dual-report as the *new* declaration).
        let binder_dual = match decl.kind {
          PrivateMemberKind::Field => false,
          PrivateMemberKind::Method => !matches!(prev_kind, PrivateMemberKind::Method),
          PrivateMemberKind::Getter => !matches!(prev_kind, PrivateMemberKind::Setter),
          PrivateMemberKind::Setter => !matches!(prev_kind, PrivateMemberKind::Getter),
        };
        if binder_dual {
          self
            .diagnostics
            .push(codes::DUPLICATE_IDENTIFIER.error(msg, Span::new(self.file, prev_range)));
        }
      }
    }
  }

  pub(crate) fn check_class_field_overwrites_base_properties(&mut self) {
    if !self.use_define_for_class_fields {
      return;
    }
    for class in self.index.classes.iter() {
      let Some(base_name) = class.extends.as_deref() else {
        continue;
      };

      for field in class.instance_fields.iter() {
        if field.has_initializer || field.name.starts_with('#') || field.is_private {
          continue;
        }
        if !self
          .index
          .instance_data_prop_declared_in_base_chain(base_name, &field.name)
        {
          continue;
        }
        let end = field
          .key_range
          .start
          .saturating_add(field.name.len() as u32)
          .min(field.key_range.end);
        let range = TextRange::new(field.key_range.start, end);
        self
          .diagnostics
          .push(codes::PROPERTY_WILL_OVERWRITE_BASE_PROPERTY.error(
            format!(
              "Property '{}' will overwrite the base property in '{}'. If this is intentional, add an initializer. Otherwise, add a 'declare' modifier or remove the redundant declaration.",
              field.name, base_name
            ),
            Span::new(self.file, range),
          ));
      }
    }
  }

  pub(crate) fn check_property_not_used_before_initialization(
    &mut self,
    obj: &Node<AstExpr>,
    prop: &str,
    span: TextRange,
  ) {
    let Some(ctx) = self.class_field_initializer.as_ref() else {
      return;
    };
    let ctx_class_index = ctx.class_index;
    let ctx_is_static = ctx.is_static;
    let ctx_member_index = ctx.member_index;
    enum CheckObject {
      This,
      ClassName,
    }

    let obj_kind = match obj.stx.as_ref() {
      AstExpr::This(_) => CheckObject::This,
      AstExpr::Id(id) => {
        // TypeScript also reports TS2729 for `C.x` reads in class field initializers when
        // `C` is the current class name and `x` is a later-declared *static* field.
        //
        // Note: For instance field initializers, this check is only active when targeting
        // native class fields (ES2022/ESNext) with `useDefineForClassFields` enabled.
        let Some(name) = self
          .index
          .classes
          .get(ctx_class_index)
          .and_then(|info| info.name.as_deref())
        else {
          return;
        };
        if id.stx.name != name {
          return;
        }
        if !ctx_is_static && !self.native_define_class_fields {
          return;
        }
        CheckObject::ClassName
      }
      _ => return,
    };

    let check_static = match obj_kind {
      CheckObject::This => ctx_is_static,
      CheckObject::ClassName => true,
    };

    if !self
      .index
      .field_declared_not_before(ctx_class_index, ctx_member_index, prop, check_static)
    {
      return;
    }

    if !ctx_is_static
      && matches!(obj_kind, CheckObject::This)
      && !self.use_define_for_class_fields
      && !prop.starts_with('#')
      && self
        .index
        .instance_prop_declared_in_ancestor(ctx_class_index, prop)
    {
      return;
    }

    let prop_len = prop.len() as u32;
    let start = span.end.saturating_sub(prop_len);
    let prop_span = TextRange::new(start, span.end);
    self
      .diagnostics
      .push(codes::PROPERTY_USED_BEFORE_INITIALIZATION.error(
        format!("Property '{prop}' is used before its initialization."),
        Span::new(self.file, prop_span),
      ));
  }

  pub(crate) fn check_cancelled(&self) {
    if let Some(flag) = self.cancelled {
      if flag.load(Ordering::Relaxed) {
        panic_any(crate::FatalError::Cancelled);
      }
    }
  }

  pub(crate) fn seed_builtins(&mut self) {
    let prim = self.store.primitive_ids();
    self.insert_binding("undefined".to_string(), prim.undefined, Vec::new());
    self.insert_binding("NaN".to_string(), prim.number, Vec::new());
    self.insert_binding("Infinity".to_string(), prim.number, Vec::new());
  }

  pub(crate) fn insert_binding(
    &mut self,
    name: String,
    ty: TypeId,
    type_params: Vec<TypeParamDecl>,
  ) {
    if let Some(scope) = self.scopes.last_mut() {
      // Fresh binding: declared type matches the initial type. Later CFA
      // narrowing updates only `ty` (see assignment), never `declared_ty`.
      scope.bindings.insert(
        name,
        Binding {
          ty,
          declared_ty: ty,
          type_params,
        },
      );
    }
  }

  pub(crate) fn lookup(&self, name: &str) -> Option<Binding> {
    for scope in self.scopes.iter().rev() {
      if let Some(binding) = scope.bindings.get(name) {
        return Some(binding.clone());
      }
    }
    None
  }

  /// Update an existing binding's flow type in the scope where it was declared.
  /// Leaves [`Binding::declared_ty`] unchanged. Returns the previous flow type.
  pub(crate) fn update_binding_ty(&mut self, name: &str, ty: TypeId) -> Option<TypeId> {
    for scope in self.scopes.iter_mut().rev() {
      if let Some(binding) = scope.bindings.get_mut(name) {
        let prev = binding.ty;
        binding.ty = ty;
        return Some(prev);
      }
    }
    None
  }

  /// Parse `typeof id === "tag"` / `"tag" === typeof id` (and `!==`) from AST.
  /// Returns `(name, typeof_tag, negate)`.
  fn ast_typeof_equality(test: &Node<AstExpr>) -> Option<(String, String, bool)> {
    let AstExpr::Binary(bin) = test.stx.as_ref() else {
      return None;
    };
    let negate = match bin.stx.operator {
      OperatorName::StrictEquality | OperatorName::Equality => false,
      OperatorName::StrictInequality | OperatorName::Inequality => true,
      _ => return None,
    };
    // A no-substitution template literal (`` `string` ``) is a string tag.
    fn string_tag(expr: &AstExpr) -> Option<String> {
      match expr {
        AstExpr::LitStr(s) => Some(s.stx.value.clone()),
        AstExpr::LitTemplate(t) => {
          let mut out = String::new();
          for part in &t.stx.parts {
            match part {
              parse_js::ast::expr::lit::LitTemplatePart::String(s) => out.push_str(s),
              _ => return None,
            }
          }
          Some(out)
        }
        _ => None,
      }
    }
    let (typeof_operand, lit) = match (bin.stx.left.stx.as_ref(), bin.stx.right.stx.as_ref()) {
      (AstExpr::Unary(u), tag) if matches!(u.stx.operator, OperatorName::Typeof) => {
        (&u.stx.argument, string_tag(tag)?)
      }
      (tag, AstExpr::Unary(u)) if matches!(u.stx.operator, OperatorName::Typeof) => {
        (&u.stx.argument, string_tag(tag)?)
      }
      _ => return None,
    };
    let AstExpr::Id(id) = typeof_operand.stx.as_ref() else {
      return None;
    };
    Some((id.stx.name.clone(), lit, negate))
  }

  /// Apply / restore binding types for AST control-flow typeof narrowing.
  fn with_binding_ty_overrides<R>(
    &mut self,
    overrides: &[(String, TypeId)],
    f: impl FnOnce(&mut Self) -> R,
  ) -> R {
    let mut saved = Vec::new();
    for (name, ty) in overrides {
      if let Some(prev) = self.update_binding_ty(name, *ty) {
        saved.push((name.clone(), prev));
      }
    }
    let result = f(self);
    for (name, prev) in saved.into_iter().rev() {
      let _ = self.update_binding_ty(&name, prev);
    }
    result
  }

  pub(crate) fn check_enclosing_function(&mut self, body_range: TextRange) -> bool {
    let mut best: Option<FunctionInfo> = None;
    for (idx, func) in self.index.functions.iter().copied().enumerate() {
      if idx % 2048 == 0 {
        self.check_cancelled();
      }
      let contains =
        func.func_span.start <= body_range.start && func.func_span.end >= body_range.end;
      if !contains {
        continue;
      }
      let len = func.func_span.end.saturating_sub(func.func_span.start);
      let replace = match best {
        Some(existing) => {
          let existing_len = existing
            .func_span
            .end
            .saturating_sub(existing.func_span.start);
          len < existing_len
        }
        None => true,
      };
      if replace {
        best = Some(func);
      }
    }
    if let Some(func) = best {
      self.check_cancelled();
      let func_node = func.func;
      let prev_return = self.expected_return;
      let prev_return_defer = self.expected_return_defer_type_params;
      let prev_async = self.in_async_function;
      let prev_ctor_class = self.constructor_class_index;
      let prev_enclosing_class = self.enclosing_class_index;
      // Membership must be by exact `Func.loc` match: both maps are keyed by the
      // same span space, so this hits iff `func` *is* the class member. A
      // containment fallback would misidentify functions *nested inside* a
      // member as the member itself — tsc `isNodeUsedDuringClassInitialization`
      // quits at function boundaries, so an arrow inside a constructor must not
      // inherit `constructor_class_index` (false TS2715 on `this.prop` reads).
      let member_func = self
        .index
        .class_member_func_by_span
        .get(&func.func_span)
        .cloned();
      self.constructor_class_index = member_func
        .as_ref()
        .filter(|m| m.is_constructor)
        .map(|m| m.class_index);
      if let Some(info) = member_func.as_ref() {
        self.enclosing_class_index = Some(info.class_index);
      } else if let Some(idx) = self.class_index_containing_span(body_range) {
        // Nested function / arrow inside a class member: keep lexical private
        // access (TS18013) scoped to that enclosing class.
        self.enclosing_class_index = Some(idx);
      } else {
        // Class expression / declaration span as last resort (anonymous
        // `const C = class { … }` multiline methods).
        let mut best: Option<(u32, usize)> = None;
        for (idx, class) in self.index.classes.iter().enumerate() {
          if class.span.start <= body_range.start && class.span.end >= body_range.end {
            let len = class.span.end.saturating_sub(class.span.start);
            let replace = match best {
              Some((existing_len, _)) => len < existing_len,
              None => true,
            };
            if replace {
              best = Some((len, idx));
            }
          }
        }
        if let Some((_, idx)) = best {
          self.enclosing_class_index = Some(idx);
        }
      }
      // Class type params are in scope for member signatures / bodies
      // (`#bar(): T`, `constructor(t: T)`); push before function type params.
      // Nested arrows/functions inside class members need the same scope
      // (`typeParameterAssignability3.ts`: field-init arrow under `class C<T,U>`).
      let pushed_class_type_params = member_func
        .as_ref()
        .map(|info| info.class_index)
        .or(self.enclosing_class_index)
        .is_some_and(|idx| self.push_class_type_param_scope(idx));
      let mut type_param_decls = Vec::new();
      let mut has_type_params = false;
      if let Some(params) = func_node.stx.type_parameters.as_ref() {
        self.lowerer.push_type_param_scope();
        has_type_params = true;
        type_param_decls = self.lower_type_params(params);
        self.type_param_scopes.push(type_param_decls.clone());
      } else if let Some(templates) = self.jsdoc_templates_owned(func_node) {
        // checkJs: `@template T` when there is no TS type-parameter list.
        self.lowerer.push_type_param_scope();
        has_type_params = true;
        type_param_decls = self.register_jsdoc_templates(&templates);
        self.type_param_scopes.push(type_param_decls.clone());
      }
      // Assignment context first; checkJs `@type {function…}` / `(…) => T` on the
      // function itself fills in when there is no surrounding contextual type.
      let contextual_sig = self
        .contextual_signature()
        .or_else(|| self.jsdoc_type_signature(func_node));
      // Class setters with a paired getter: getter return types the setter
      // parameter (tsc accessor linking). Params only — do not drive
      // `expected_return` (setter "return" is not the getter type).
      let setter_param_sig = if contextual_sig.is_none() {
        member_func.as_ref().and_then(|info| {
          if !info.is_setter {
            return None;
          }
          let name = info.accessor_name.as_deref()?;
          self.setter_sig_from_paired_getter(info.class_index, info.is_static, name)
        })
      } else {
        None
      };
      // Prefer HIR `FunctionData.return_type`; AST TypeLowerer residual for
      // `typeof import(...)` / missing arenas / nested-function mismatch.
      let annotated_return = self.hir_return_annotation_ty(func_node).or_else(|| {
        func_node
          .stx
          .return_type
          .as_ref()
          .map(|ret| self.lowerer.lower_type_expr(ret))
      });
      // checkJs: `@returns {T}` fills in when there is no TS return annotation.
      let jsdoc_return = if annotated_return.is_none() {
        self.jsdoc_returns_type(func_node)
      } else {
        None
      };
      self.in_async_function = func_node.stx.async_;
      // Provenance matters for return checking: a return annotation (or JSDoc)
      // on this function is a *declared* target (nominal type-param rules), but
      // a contextual signature's return is an inference target — hard checks
      // against it are deferred until the call instantiates the type args.
      let expected_from_contextual =
        annotated_return.is_none() && jsdoc_return.is_none() && contextual_sig.is_some();
      let mut expected = annotated_return
        .or(jsdoc_return)
        .or_else(|| contextual_sig.as_ref().map(|sig| sig.ret));
      // Generators return through their generator type's `TReturn` argument,
      // not the generator object itself: `return a` in
      // `async function* f(): AsyncGenerator<T, T, T>` checks `a` against
      // `Awaited<T>`, never `Awaited<AsyncGenerator<…>>`
      // (`asyncGeneratorGenericNonWrappedReturn.ts`).
      if func_node.stx.generator {
        if let Some(ty) = expected {
          if let Some(ret_arg) = self.annotated_generator_return_arg(ty) {
            expected = Some(ret_arg);
          }
        }
      }
      if func_node.stx.async_ {
        expected = expected.map(|ty| awaited_type(self.store.as_ref(), ty, self.ref_expander));
      }
      self.expected_return = expected;
      self.expected_return_defer_type_params =
        expected_from_contextual && expected.is_some_and(|ty| self.type_mentions_type_param(ty));
      self.bind_params(
        func_node,
        &type_param_decls,
        contextual_sig.as_ref().or(setter_param_sig.as_ref()),
      );
      let prev_spi = self.spi_ctor.take();
      let prev_this = self.contextual_this_ty.take();
      let prev_this_is_static = self.contextual_this_is_static.take();
      if let Some(info) = member_func {
        self.contextual_this_ty = self.resolve_class_this_type(info.class_index, info.is_static);
        self.contextual_this_is_static = Some(info.is_static);
        // checkJs: an explicit `@this {…}` tag wins over the class-derived
        // `this` type (tsc `inferThis.ts`).
        if let Some(this_ty) = self.jsdoc_this_type(func_node) {
          self.contextual_this_ty = Some(this_ty);
        }
        if info.is_constructor {
          self.begin_spi_ctor(info.class_index);
          self.check_constructor_this_before_super(info.class_index, func_node);
        }
      } else if self.body.function.as_ref().is_some_and(|f| f.is_arrow) {
        // Nested arrows inherit `this` from the enclosing class member / field
        // initializer (`typeParameterAssignability3.ts`: `r = () => this.t = …`).
        // Function expressions do not.
        if let Some((class_index, is_static)) =
          self.enclosing_class_this_context(func.func_span, body_range)
        {
          self.contextual_this_ty = self.resolve_class_this_type(class_index, is_static);
          self.contextual_this_is_static = Some(is_static);
        }
      }
      self.check_function_body(func_node);
      self.end_spi_ctor();
      self.spi_ctor = prev_spi;
      self.contextual_this_ty = prev_this;
      self.contextual_this_is_static = prev_this_is_static;
      if has_type_params {
        self.type_param_scopes.pop();
        self.lowerer.pop_type_param_scope();
      }
      if pushed_class_type_params {
        self.pop_class_type_param_scope();
      }
      self.expected_return = prev_return;
      self.expected_return_defer_type_params = prev_return_defer;
      self.in_async_function = prev_async;
      self.constructor_class_index = prev_ctor_class;
      self.enclosing_class_index = prev_enclosing_class;
      return true;
    }
    false
  }

  /// Contextual signature for a class `set` accessor from its paired `get`.
  ///
  /// TypeScript types the setter parameter from the getter's return type when
  /// both exist; without that link, `--noImplicitAny` / checkJs falsely flags
  /// unannotated setter params (TC3000 / TS7006).
  pub(crate) fn setter_sig_from_paired_getter(
    &mut self,
    class_index: usize,
    is_static: bool,
    name: &str,
  ) -> Option<Signature> {
    let getter = {
      let class = self.index.classes.get(class_index)?;
      if is_static {
        class.static_getter_funcs.get(name).copied()
      } else {
        class.instance_getter_funcs.get(name).copied()
      }?
    };
    let ret = self.infer_getter_return_type(getter, class_index, is_static)?;
    let prim = self.store.primitive_ids();
    if ret == prim.unknown {
      return None;
    }
    Some(Signature {
      params: vec![Param {
        name: None,
        ty: ret,
        optional: false,
        rest: false,
      }],
      ret: prim.void,
      type_params: Vec::new(),
      this_param: None,
    })
  }

  /// Infer a getter's return type for setter-parameter contextual typing.
  ///
  /// Prefer annotations / JSDoc; otherwise peek the getter body (diagnostics
  /// discarded — the getter is checked as its own body).
  pub(crate) fn infer_getter_return_type(
    &mut self,
    getter: &Node<Func>,
    class_index: usize,
    is_static: bool,
  ) -> Option<TypeId> {
    if let Some(ret) = getter.stx.return_type.as_ref() {
      return Some(self.lowerer.lower_type_expr(ret));
    }
    if let Some(ty) = self.jsdoc_returns_type(getter) {
      return Some(ty);
    }
    let saved_diags = std::mem::take(&mut self.diagnostics);
    let saved_returns = std::mem::take(&mut self.return_types);
    let saved_nia_reported = std::mem::take(&mut self.implicit_any_reported);
    // The peek re-checks the getter body for inference only; its TS2403
    // bookkeeping must not leak into the enclosing (setter) body check —
    // otherwise the setter's own `var x = …` looks like a later redeclaration
    // and false-fires (`superPropertyAccessNoError.ts` accessors).
    let saved_established_vars = std::mem::take(&mut self.established_var_bindings);
    let saved_ns_established = std::mem::take(&mut self.namespace_established_vars);
    let saved_expected = self.expected_return.take();
    let saved_expected_defer = self.expected_return_defer_type_params;
    let saved_async = self.in_async_function;
    let saved_this = self.contextual_this_ty.take();
    let saved_this_is_static = self.contextual_this_is_static.take();
    let saved_field_init = self.class_field_initializer.take();
    let saved_ctor_class = self.constructor_class_index.take();
    let saved_spi = self.spi_ctor.take();
    let saved_enclosing = self.enclosing_class_index;

    self.in_async_function = getter.stx.async_;
    self.expected_return = None;
    self.expected_return_defer_type_params = false;
    self.enclosing_class_index = Some(class_index);
    self.contextual_this_ty = self.resolve_class_this_type(class_index, is_static);
    self.contextual_this_is_static = Some(is_static);
    self.scopes.push(Scope::default());
    // Getters are typically parameterless; bind without reporting implicit any
    // for any exotic params so the peek stays side-effect light.
    let prev_nia = self.no_implicit_any;
    self.no_implicit_any = false;
    self.bind_params(getter, &[], None);
    self.no_implicit_any = prev_nia;
    self.check_function_body(getter);
    self.scopes.pop();

    let prim = self.store.primitive_ids();
    let inferred = if self.return_types.is_empty() {
      None
    } else {
      let ty = self.store.union(self.return_types.clone());
      Some(if getter.stx.async_ {
        self.async_function_return_type(ty)
      } else {
        self.base_type(ty)
      })
    };

    self.diagnostics = saved_diags;
    self.return_types = saved_returns;
    self.implicit_any_reported = saved_nia_reported;
    self.established_var_bindings = saved_established_vars;
    self.namespace_established_vars = saved_ns_established;
    self.expected_return = saved_expected;
    self.expected_return_defer_type_params = saved_expected_defer;
    self.in_async_function = saved_async;
    self.contextual_this_ty = saved_this;
    self.contextual_this_is_static = saved_this_is_static;
    self.class_field_initializer = saved_field_init;
    self.constructor_class_index = saved_ctor_class;
    self.spi_ctor = saved_spi;
    self.enclosing_class_index = saved_enclosing;

    inferred.filter(|ty| *ty != prim.unknown)
  }

  /// TS2376 / TS17009 — `this` before `super()` in a derived constructor.
  /// TS2376 additionally requires initialized properties / parameter properties
  /// / private identifiers and is suppressed under native class-field semantics
  /// (`useDefineForClassFields` + ES2022/ESNext).
  pub(crate) fn check_constructor_this_before_super(
    &mut self,
    class_index: usize,
    func: &Node<Func>,
  ) {
    // Derived only: `ClassInfo.extends` is set for `extends Id` bases.
    if self
      .index
      .classes
      .get(class_index)
      .is_none_or(|c| c.extends.is_none())
    {
      return;
    }
    let Some(FuncBody::Block(body)) = func.stx.body.as_ref() else {
      return;
    };
    let mut this_before: Option<TextRange> = None;
    for stmt in body.iter() {
      if stmt_is_super_call(stmt) {
        break;
      }
      if let Some(range) = first_this_before_super_in_stmt(self.file, stmt) {
        this_before = Some(range);
        break;
      }
    }
    let Some(this_range) = this_before else {
      return;
    };
    // Emit TS2376 before TS17009 to match tsc order.
    if self.class_requires_super_call_first(class_index) && !self.native_define_class_fields {
      let ctor_range = self
        .index
        .classes
        .get(class_index)
        .and_then(|c| c.constructor_key_range)
        .unwrap_or(this_range);
      self
        .diagnostics
        .push(codes::SUPER_MUST_BE_FIRST_IN_CONSTRUCTOR.error(
          "A 'super' call must be the first statement in the constructor to refer to 'super' or 'this' when a derived class contains initialized properties, parameter properties, or private identifiers.",
          Span {
            file: self.file,
            range: ctor_range,
          },
        ));
    }
    self
      .diagnostics
      .push(codes::SUPER_MUST_BE_CALLED_BEFORE_THIS.error(
        "'super' must be called before accessing 'this' in the constructor of a derived class.",
        Span {
          file: self.file,
          range: this_range,
        },
      ));
  }

  fn class_requires_super_call_first(&self, class_index: usize) -> bool {
    let Some(class) = self.index.classes.get(class_index) else {
      return false;
    };
    if !class.private_name_decls.is_empty() {
      return true;
    }
    if class.instance_fields.iter().any(|f| f.has_initializer) {
      return true;
    }
    if !class.instance_param_props.is_empty() {
      return true;
    }
    false
  }

  /// Whether `ty` is a type parameter declared on an enclosing function scope.
  fn is_enclosing_type_param(&self, ty: TypeId) -> bool {
    let TypeKind::TypeParam(id) = self.store.type_kind(ty) else {
      return false;
    };
    self
      .type_param_scopes
      .iter()
      .flatten()
      .any(|decl| decl.id == id)
  }

  /// True when `ty` mentions any type parameter. Shallow structural walk over
  /// immediate interned children only (`Ref` args included, refs never
  /// expanded), so it terminates on arbitrary types; depth-capped defensively.
  pub(crate) fn type_mentions_type_param(&self, ty: TypeId) -> bool {
    const MAX_DEPTH: usize = 32;
    fn go(store: &TypeStore, ty: TypeId, depth: usize) -> bool {
      if depth > MAX_DEPTH {
        return false;
      }
      match store.type_kind(ty) {
        TypeKind::TypeParam(_) => true,
        TypeKind::Union(members) | TypeKind::Intersection(members) => {
          members.iter().any(|&m| go(store, m, depth + 1))
        }
        TypeKind::Array { ty, .. } => go(store, ty, depth + 1),
        TypeKind::Tuple(elems) => elems.iter().any(|e| go(store, e.ty, depth + 1)),
        TypeKind::Ref { args, .. } => args.iter().any(|&a| go(store, a, depth + 1)),
        TypeKind::Callable { overloads } => overloads.iter().any(|&sig_id| {
          let sig = store.signature(sig_id);
          sig.params.iter().any(|p| go(store, p.ty, depth + 1))
            || go(store, sig.ret, depth + 1)
            || sig
              .type_params
              .iter()
              .any(|tp| tp.constraint.is_some_and(|c| go(store, c, depth + 1)))
        }),
        TypeKind::Intrinsic { ty, .. } => go(store, ty, depth + 1),
        TypeKind::IndexedAccess { obj, index } => {
          go(store, obj, depth + 1) || go(store, index, depth + 1)
        }
        TypeKind::KeyOf(inner) => go(store, inner, depth + 1),
        _ => false,
      }
    }
    go(self.store.as_ref(), ty, 0)
  }

  /// Collect the free type-parameter ids mentioned by `ty` (bounded walk).
  pub(crate) fn collect_mentioned_type_params(&self, ty: TypeId, out: &mut HashSet<TypeParamId>) {
    const MAX_DEPTH: usize = 32;
    fn go(store: &TypeStore, ty: TypeId, out: &mut HashSet<TypeParamId>, depth: usize) {
      if depth > MAX_DEPTH {
        return;
      }
      match store.type_kind(ty) {
        TypeKind::TypeParam(id) => {
          out.insert(id);
        }
        TypeKind::Union(members) | TypeKind::Intersection(members) => {
          for m in members {
            go(store, m, out, depth + 1);
          }
        }
        TypeKind::Array { ty, .. } => go(store, ty, out, depth + 1),
        TypeKind::Tuple(elems) => {
          for e in elems {
            go(store, e.ty, out, depth + 1);
          }
        }
        TypeKind::Ref { args, .. } => {
          for a in args {
            go(store, a, out, depth + 1);
          }
        }
        TypeKind::Callable { overloads } => {
          for sig_id in overloads {
            let sig = store.signature(sig_id);
            for p in &sig.params {
              go(store, p.ty, out, depth + 1);
            }
            go(store, sig.ret, out, depth + 1);
            for tp in &sig.type_params {
              if let Some(c) = tp.constraint {
                go(store, c, out, depth + 1);
              }
            }
          }
        }
        TypeKind::Intrinsic { ty, .. } => go(store, ty, out, depth + 1),
        TypeKind::IndexedAccess { obj, index } => {
          go(store, obj, out, depth + 1);
          go(store, index, out, depth + 1);
        }
        TypeKind::KeyOf(inner) => go(store, inner, out, depth + 1),
        _ => {}
      }
    }
    go(self.store.as_ref(), ty, out, 0)
  }

  /// Assignability into an enclosing naked type parameter (return-position).
  fn assignable_to_enclosing_type_param(&self, src: TypeId, dst: TypeId) -> bool {
    let TypeKind::TypeParam(dst_tp) = self.store.type_kind(dst) else {
      return false;
    };
    match self.store.type_kind(src) {
      TypeKind::Any => true,
      TypeKind::TypeParam(src_tp) => src_tp == dst_tp,
      TypeKind::Null | TypeKind::Undefined if !self.strict_null_checks => true,
      _ => false,
    }
  }

  /// Tightest class whose member function / field initializer / static block
  /// lexically contains `span` (for nested functions inside class members).
  pub(crate) fn class_index_containing_span(&self, span: TextRange) -> Option<usize> {
    let mut best: Option<(u32, usize)> = None;
    let consider = |best: &mut Option<(u32, usize)>, outer: TextRange, class_index: usize| {
      if outer.start <= span.start && outer.end >= span.end {
        let len = outer.end.saturating_sub(outer.start);
        let replace = match *best {
          Some((existing_len, _)) => len < existing_len,
          None => true,
        };
        if replace {
          *best = Some((len, class_index));
        }
      }
    };
    for (member_span, info) in self.index.class_member_func_by_span.iter() {
      consider(&mut best, *member_span, info.class_index);
    }
    for (init_span, info) in self.index.class_field_initializers.iter() {
      consider(&mut best, *init_span, info.class_index);
    }
    for block in self.index.class_static_blocks.iter() {
      consider(&mut best, block.span, block.class_index);
    }
    best.map(|(_, idx)| idx)
  }

  /// Contextual `this` for a class member body (instance vs static side).
  pub(crate) fn resolve_class_this_type(
    &mut self,
    class_index: usize,
    is_static: bool,
  ) -> Option<TypeId> {
    if is_static {
      self.resolve_static_this_type(class_index)
    } else {
      self.resolve_instance_this_type(class_index)
    }
  }

  /// Class + static/instance side for a nested arrow whose body is lexically
  /// inside a field initializer or class member function.
  fn enclosing_class_this_context(
    &self,
    func_span: TextRange,
    body_range: TextRange,
  ) -> Option<(usize, bool)> {
    let covers = |outer: TextRange| {
      (outer.start <= func_span.start && outer.end >= func_span.end)
        || (outer.start <= body_range.start && outer.end >= body_range.end)
    };
    let mut best_field: Option<(u32, usize, bool)> = None;
    for (span, info) in self.index.class_field_initializers.iter() {
      if !covers(*span) {
        continue;
      }
      let len = span.end.saturating_sub(span.start);
      let replace = match best_field {
        Some((existing_len, _, _)) => len < existing_len,
        None => true,
      };
      if replace {
        best_field = Some((len, info.class_index, info.is_static));
      }
    }
    if let Some((_, class_index, is_static)) = best_field {
      return Some((class_index, is_static));
    }
    let mut best_member: Option<(u32, usize, bool)> = None;
    for (span, info) in self.index.class_member_func_by_span.iter() {
      if !covers(*span) {
        continue;
      }
      let len = span.end.saturating_sub(span.start);
      let replace = match best_member {
        Some((existing_len, _, _)) => len < existing_len,
        None => true,
      };
      if replace {
        best_member = Some((len, info.class_index, info.is_static));
      }
    }
    if let Some((_, class_index, is_static)) = best_member {
      return Some((class_index, is_static));
    }
    self.enclosing_class_index.map(|idx| (idx, false))
  }

  /// The `TReturn` argument of a `Generator<Y, R, N>` /
  /// `AsyncGenerator<Y, R, N>` return annotation — the type `return`
  /// statements are checked against. `None` when the annotation isn't a
  /// generator reference with at least two type arguments.
  fn annotated_generator_return_arg(&self, ty: TypeId) -> Option<TypeId> {
    let TypeKind::Ref { def, args } = self.store.type_kind(ty) else {
      return None;
    };
    if args.len() < 2 {
      return None;
    }
    let resolver = self.type_resolver.as_ref()?;
    let is_generator = ["Generator", "AsyncGenerator"].iter().any(|name| {
      resolver
        .resolve_type_name(&[name.to_string()])
        .is_some_and(|resolved| resolved == def)
    });
    is_generator.then_some(args[1])
  }

  /// Type of `super` in *member* position: the base class constructor in a
  /// static member context, the base instance otherwise (`super.x` /
  /// `super.x()`; `super()` calls are typed `void` by the call path). Falls
  /// back to `unknown` when the base cannot be resolved
  /// (`superPropertyAccessNoError.ts`).
  pub(crate) fn resolve_super_type(&mut self) -> TypeId {
    let prim = self.store.primitive_ids();
    let Some(class_index) = self.enclosing_class_index else {
      return prim.unknown;
    };
    let Some(class) = self.index.classes.get(class_index) else {
      return prim.unknown;
    };
    let Some(extends) = class.extends.clone() else {
      return prim.unknown;
    };
    let base_ctor = self.lookup(&extends).map(|b| b.ty).or_else(|| {
      // The body's scope chain may not carry the file-level class binding
      // (e.g. `type_of_def` on a method) — use the span-keyed declaration map
      // for same-file bases.
      self
        .index
        .classes
        .iter()
        .find(|c| c.name.as_deref() == Some(extends.as_str()))
        .and_then(|c| self.class_expr_value_tys.get(&c.span).copied())
    });
    let Some(base_ctor) = base_ctor else {
      return prim.unknown;
    };
    // Static context: member functions track it explicitly; field initializers
    // and static blocks carry it on the field-init context.
    let is_static = self
      .contextual_this_is_static
      .or_else(|| {
        self
          .class_field_initializer
          .as_ref()
          .map(|ctx| ctx.is_static)
      })
      .unwrap_or(false);
    if is_static {
      base_ctor
    } else {
      self
        .instance_type_from_constructor_value(base_ctor)
        .unwrap_or(prim.unknown)
    }
  }

  /// Instance type of `this` inside a constructor / instance method / instance
  /// field initializer.
  ///
  /// Prefer the HIR/class-expr value type for *this* `class_index` (span-keyed),
  /// then a unique name binding, then a structural shape from [`ClassInfo`].
  /// Name lookup is skipped when multiple classes share the same spelling
  /// (duplicate `class Inner` expressions) — otherwise `lookup("Inner")` returns
  /// the innermost binding and mis-brands foreign privates as TS18013.
  pub(crate) fn resolve_instance_this_type(&mut self, class_index: usize) -> Option<TypeId> {
    if let Some(ctor) = self.class_ctor_type_for_index(class_index) {
      if let Some(instance) = self.instance_type_from_constructor_value(ctor) {
        return Some(instance);
      }
    }
    self.synthesize_instance_type_from_class_info(class_index)
  }

  /// Static-side `this` (constructor object) for static methods / static field
  /// initializers / static blocks.
  pub(crate) fn resolve_static_this_type(&mut self, class_index: usize) -> Option<TypeId> {
    if let Some(ctor) = self.class_ctor_type_for_index(class_index) {
      return Some(ctor);
    }
    self.synthesize_static_type_from_class_info(class_index)
  }

  /// Constructor/value type for `class_index`, preferring span-keyed HIR types
  /// over ambiguous same-name bindings.
  fn class_ctor_type_for_index(&self, class_index: usize) -> Option<TypeId> {
    let class = self.index.classes.get(class_index)?;
    if let Some(&ty) = self.class_expr_value_tys.get(&class.span) {
      return Some(ty);
    }
    let name = class.name.as_ref()?;
    let homonyms = self
      .index
      .classes
      .iter()
      .filter(|c| c.name.as_deref() == Some(name.as_str()))
      .count();
    if homonyms > 1 {
      return None;
    }
    self.lookup(name).map(|b| b.ty)
  }

  pub(super) fn instance_type_from_constructor_value(&self, value_ty: TypeId) -> Option<TypeId> {
    let expanded = self.expand_ref(value_ty);
    match self.store.type_kind(expanded) {
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        shape
          .construct_signatures
          .first()
          .map(|sig_id| self.store.signature(*sig_id).ret)
      }
      TypeKind::Callable { overloads } => overloads
        .first()
        .map(|sig_id| self.store.signature(*sig_id).ret),
      _ => None,
    }
  }

  fn synthesize_fields_shape(
    &mut self,
    fields: &[(String, bool, Option<&Node<TypeExpr>>)],
    extra_unknown_names: &[String],
    method_names: &[String],
    private_origin: Option<u32>,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    let unknown = prim.unknown;
    let mut shape = Shape::new();
    let mut seen = HashSet::new();
    let brand = |name: &str| -> (Option<types_ts_interned::Accessibility>, Option<u32>) {
      if name.starts_with('#') {
        (
          Some(types_ts_interned::Accessibility::Private),
          private_origin,
        )
      } else {
        (None, None)
      }
    };
    // When synthesizing outside a member body, class-`T` field anns still need
    // scope (`#foo: T` on `class C<T>`).
    let pushed = private_origin
      .map(|idx| idx as usize)
      .is_some_and(|idx| self.push_class_type_param_scope(idx));
    for (name, optional, ann) in fields {
      seen.insert(name.clone());
      let ty = ann
        .map(|t| self.lowerer.lower_type_expr(t))
        .unwrap_or(unknown);
      let (accessibility, origin) = brand(name);
      shape.properties.push(types_ts_interned::Property {
        key: PropKey::String(self.store.intern_name(name.clone())),
        data: PropData {
          ty,
          optional: *optional,
          readonly: false,
          accessibility,
          is_method: false,
          origin,
          declared_on: None,
        },
      });
    }
    for name in extra_unknown_names {
      if !seen.insert(name.clone()) {
        continue;
      }
      let (accessibility, origin) = brand(name);
      shape.properties.push(types_ts_interned::Property {
        key: PropKey::String(self.store.intern_name(name.clone())),
        data: PropData {
          ty: unknown,
          optional: false,
          readonly: false,
          accessibility,
          is_method: false,
          origin,
          declared_on: None,
        },
      });
    }
    // Unannotated methods synthesize as `() => void` so assignment checks
    // (TS2322) see a real target type on anonymous / fallback class `this`.
    let method_callable = {
      let sig_id = self
        .store
        .intern_signature(Signature::new(Vec::new(), prim.void));
      self.store.intern_type(TypeKind::Callable {
        overloads: vec![sig_id],
      })
    };
    for name in method_names {
      if !seen.insert(name.clone()) {
        continue;
      }
      let (accessibility, origin) = brand(name);
      shape.properties.push(types_ts_interned::Property {
        key: PropKey::String(self.store.intern_name(name.clone())),
        data: PropData {
          ty: method_callable,
          optional: false,
          readonly: false,
          accessibility,
          is_method: true,
          origin,
          declared_on: None,
        },
      });
    }
    if pushed {
      self.pop_class_type_param_scope();
    }
    let shape_id = self.store.intern_shape(shape);
    let obj = self.store.intern_object(ObjectType { shape: shape_id });
    self.store.intern_type(TypeKind::Object(obj))
  }

  fn synthesize_instance_type_from_class_info(&mut self, class_index: usize) -> Option<TypeId> {
    let class = self.index.classes.get(class_index)?;
    let fields: Vec<(String, bool, Option<&Node<TypeExpr>>)> = class
      .instance_fields
      .iter()
      .map(|f| (f.name.clone(), f.optional, f.type_annotation))
      .collect();
    let param_props: Vec<String> = class.instance_param_props.clone();
    let mut methods: Vec<String> = class.instance_methods.iter().cloned().collect();
    methods.sort();
    Some(self.synthesize_fields_shape(&fields, &param_props, &methods, Some(class_index as u32)))
  }

  fn synthesize_static_type_from_class_info(&mut self, class_index: usize) -> Option<TypeId> {
    let class = self.index.classes.get(class_index)?;
    let fields: Vec<(String, bool, Option<&Node<TypeExpr>>)> = class
      .static_fields
      .iter()
      .map(|f| (f.name.clone(), f.optional, f.type_annotation))
      .collect();
    let mut methods: Vec<String> = class.static_methods.iter().cloned().collect();
    methods.sort();
    Some(self.synthesize_fields_shape(&fields, &[], &methods, Some(class_index as u32)))
  }

  /// Constructor value type for a class expression when HIR decl types are
  /// unavailable: static shape + construct signature returning the instance
  /// (both include private `#` members from [`ClassInfo`]).
  pub(crate) fn synthesize_class_expression_value_type(
    &mut self,
    class_index: usize,
  ) -> Option<TypeId> {
    let instance = self.synthesize_instance_type_from_class_info(class_index)?;
    let class = self.index.classes.get(class_index)?;
    let fields: Vec<(String, bool, Option<&Node<TypeExpr>>)> = class
      .static_fields
      .iter()
      .map(|f| (f.name.clone(), f.optional, f.type_annotation))
      .collect();
    let mut methods: Vec<String> = class.static_methods.iter().cloned().collect();
    methods.sort();
    // Build static props/methods, then attach a default construct signature.
    let prim = self.store.primitive_ids();
    let unknown = prim.unknown;
    let origin = Some(class_index as u32);
    let mut shape = Shape::new();
    let mut seen = HashSet::new();
    for (name, optional, ann) in fields {
      seen.insert(name.clone());
      let ty = ann
        .map(|t| self.lowerer.lower_type_expr(t))
        .unwrap_or(unknown);
      let (accessibility, prop_origin) = if name.starts_with('#') {
        (Some(types_ts_interned::Accessibility::Private), origin)
      } else {
        (None, None)
      };
      shape.properties.push(types_ts_interned::Property {
        key: PropKey::String(self.store.intern_name(name)),
        data: PropData {
          ty,
          optional,
          readonly: false,
          accessibility,
          is_method: false,
          origin: prop_origin,
          declared_on: None,
        },
      });
    }
    let method_callable = {
      let sig_id = self
        .store
        .intern_signature(Signature::new(Vec::new(), prim.void));
      self.store.intern_type(TypeKind::Callable {
        overloads: vec![sig_id],
      })
    };
    for name in methods {
      if !seen.insert(name.clone()) {
        continue;
      }
      let (accessibility, prop_origin) = if name.starts_with('#') {
        (Some(types_ts_interned::Accessibility::Private), origin)
      } else {
        (None, None)
      };
      shape.properties.push(types_ts_interned::Property {
        key: PropKey::String(self.store.intern_name(name)),
        data: PropData {
          ty: method_callable,
          optional: false,
          readonly: false,
          accessibility,
          is_method: true,
          origin: prop_origin,
          declared_on: None,
        },
      });
    }
    let ctor_sig = self.store.intern_signature(Signature {
      params: Vec::new(),
      ret: instance,
      type_params: Vec::new(),
      this_param: None,
    });
    shape.construct_signatures.push(ctor_sig);
    let shape_id = self.store.intern_shape(shape);
    let obj = self.store.intern_object(ObjectType { shape: shape_id });
    Some(self.store.intern_type(TypeKind::Object(obj)))
  }

  pub(crate) fn check_enclosing_class(&mut self, body_range: TextRange) -> bool {
    if body_range.start == body_range.end {
      // Empty class bodies (no static blocks) still count as checked.
      return true;
    }
    // Tightest class whose span covers this class-body HIR range (for computed
    // keys / decorators that are not field initializers).
    let body_class_index = self.tightest_class_index_covering(body_range);
    // Class-body HIR includes `extends Parent<T>` Instantiation exprs; push
    // class type params so those args do not emit false TC2008.
    let pushed_class_type_params =
      body_class_index.is_some_and(|idx| self.push_class_type_param_scope(idx));
    let mut matched_blocks: Vec<ClassStaticBlockInfo> = Vec::new();
    for (idx, block) in self.index.class_static_blocks.iter().copied().enumerate() {
      if idx % 256 == 0 {
        self.check_cancelled();
      }
      if ranges_overlap(body_range, block.span) || contains_range(block.span, body_range) {
        matched_blocks.push(block);
      }
    }
    matched_blocks.sort_by_key(|block| (block.span.start, block.span.end));
    matched_blocks.dedup_by_key(|block| {
      (
        block.span.start,
        block.span.end,
        block.block as *const Node<ClassStaticBlock>,
      )
    });
    let static_block_spans: Vec<TextRange> =
      matched_blocks.iter().map(|block| block.span).collect();

    for block in matched_blocks.iter() {
      self.check_cancelled();
      let block_node = block.block;
      let prev_ctx = self.class_field_initializer.clone();
      let prev_enclosing_class = self.enclosing_class_index;
      let prev_this = self.contextual_this_ty.take();
      self.class_field_initializer = Some(ClassFieldInitializerContext {
        class_index: block.class_index,
        member_index: block.member_index,
        is_static: true,
      });
      self.enclosing_class_index = Some(block.class_index);
      self.contextual_this_ty = self.resolve_class_this_type(block.class_index, true);
      self.check_block_body(&block_node.stx.body);
      self.class_field_initializer = prev_ctx;
      self.enclosing_class_index = prev_enclosing_class;
      self.contextual_this_ty = prev_this;
    }

    // Class bodies can contain additional evaluation expressions (e.g. decorators,
    // `extends` expressions, computed property names). These expressions are
    // lowered into the class body HIR but are not part of any static block.
    // Type-check them directly, skipping any spans that are covered by a static
    // block so we preserve static block scoping rules.
    let mut checked_any = !matched_blocks.is_empty();
    let expr_spans = self.expr_spans.clone();
    for span in expr_spans {
      if static_block_spans
        .iter()
        .any(|block_span| contains_range(*block_span, span))
      {
        continue;
      }
      // Nested pieces of a field initializer (e.g. `D.#method` inside
      // `D.#method()`) are checked via `check_expr` on the init root with
      // enclosing class set. Checking them alone here would leave
      // `enclosing_class_index` unset and emit false TS18013. They are
      // *covered* by the initializer's own body check, so they count as
      // checked for the missing-body decision (decorated class expressions
      // inside field initializers — `esDecorators-classExpression-
      // namedEvaluation.10.ts`).
      if self
        .index
        .class_field_initializers
        .iter()
        .any(|(init_span, _)| *init_span != span && contains_range(*init_span, span))
      {
        checked_any = true;
        continue;
      }
      let Some(expr) = self.index.exprs.get(&span).copied() else {
        continue;
      };
      self.check_cancelled();
      let prev_props = self.current_class_field_param_props;
      self.current_class_field_param_props = self
        .index
        .class_field_param_props
        .get(&span)
        .map(|props| props.as_slice());
      let prev_field_init = self.class_field_initializer.clone();
      let prev_enclosing_class = self.enclosing_class_index;
      let prev_this = self.contextual_this_ty.take();
      let field_info = self.index.class_field_initializer(span);
      self.class_field_initializer = field_info
        .as_ref()
        .map(|info| ClassFieldInitializerContext {
          class_index: info.class_index,
          member_index: info.member_index,
          is_static: info.is_static,
        });
      if let Some(info) = field_info.as_ref() {
        self.enclosing_class_index = Some(info.class_index);
        self.contextual_this_ty = self.resolve_class_this_type(info.class_index, info.is_static);
        if !info.prop_name.is_empty() {
          self
            .field_init_type_stack
            .push((info.class_index, info.prop_name.clone()));
        }
      } else if let Some(idx) =
        body_class_index.or_else(|| self.tightest_class_index_covering(span))
      {
        // Computed method keys / heritage / decorators are not field inits, but
        // still need lexical private access (e.g. `[obj.#name]()` nested in Foo).
        self.enclosing_class_index = Some(idx);
      }
      let expected = field_info.as_ref().and_then(|info| {
        let class = self.index.classes.get(info.class_index)?;
        let fields = if info.is_static {
          &class.static_fields
        } else {
          &class.instance_fields
        };
        fields
          .iter()
          .find(|f| f.name == info.prop_name)
          .and_then(|f| f.type_annotation)
          .map(|ann| self.lowerer.lower_type_expr(ann))
      });
      let _ = match expected {
        Some(expected) => self.check_expr_with_expected(expr, expected),
        None => self.check_expr(expr),
      };
      if let Some(info) = field_info.as_ref() {
        if !info.prop_name.is_empty() {
          let _ = self.field_init_type_stack.pop();
        }
      }
      self.class_field_initializer = prev_field_init;
      self.enclosing_class_index = prev_enclosing_class;
      self.contextual_this_ty = prev_this;
      self.current_class_field_param_props = prev_props;
      checked_any = true;
    }

    if pushed_class_type_params {
      self.pop_class_type_param_scope();
    }

    checked_any
  }

  /// Tightest AstIndex class whose span covers `range`.
  fn tightest_class_index_covering(&self, range: TextRange) -> Option<usize> {
    let mut best: Option<(u32, usize)> = None;
    for (idx, class) in self.index.classes.iter().enumerate() {
      if class.span.start <= range.start && class.span.end >= range.end {
        let len = class.span.end.saturating_sub(class.span.start);
        let replace = match best {
          Some((existing_len, _)) => len < existing_len,
          None => true,
        };
        if replace {
          best = Some((len, idx));
        }
      }
    }
    best.map(|(_, idx)| idx)
  }

  pub(crate) fn check_matching_initializer(&mut self, body_range: TextRange) -> bool {
    // Class-field initializer bodies must be matched before var declarators.
    // Otherwise `const C = class { static #f = D.#m() }` steals the field body
    // (class-expr init contains the field span) and checks without
    // `enclosing_class_index`, emitting a false TS18013 on `D.#m()`.
    if self.index.class_field_initializer(body_range).is_some() {
      return self.check_class_field_initializer_body(body_range);
    }

    // Prefer the var declarator this HIR body was lowered from
    // (`lower_var_body` sets `body.span` to the pattern loc). Without this,
    // expanded `body_range` (pat ∪ init) for `const C = class { … }` overlaps
    // nested `const b = this.#priv` and the smallest-init heuristic steals it,
    // checking private access with no enclosing class (false TS2571/TS18016).
    if let Some(info) = self.index.vars.get(&self.body.span).copied() {
      return self.check_var_initializer_decl(self.body.span, info);
    }

    // Own init span from HIR (ClassExpr / field expr) — reject nested vars
    // whose inits live strictly inside it.
    let own_init_span = self.hir_own_initializer_expr_span();

    let mut best: Option<(u32, TextRange, VarInfo)> = None;
    for (span, info) in self.index.vars.iter() {
      if let Some(init) = info.initializer {
        let init_range = loc_to_range(self.file, init.loc);
        if !ranges_overlap(init_range, body_range) && !contains_range(body_range, init_range) {
          continue;
        }
        // Nested bodies (class fields inside `const C = class { … }`) are strict
        // subranges of the outer var's initializer — never claim those here.
        if contains_range(init_range, body_range) && init_range != body_range {
          continue;
        }
        if let Some(own) = own_init_span {
          if contains_range(own, init_range) && init_range != own {
            continue;
          }
        }
        let len = init_range.end.saturating_sub(init_range.start);
        let replace = match best {
          Some((best_len, best_span, _)) => {
            len < best_len || (len == best_len && span.start < best_span.start)
          }
          None => true,
        };
        if replace {
          best = Some((len, *span, *info));
        }
      }
    }
    if let Some((_len, pat_span, info)) = best {
      return self.check_var_initializer_decl(pat_span, info);
    }

    // Fallback for initializer bodies that are not var declarators (e.g. class
    // field initializers whose span did not hit the exact map key above).
    self.check_class_field_initializer_body(body_range)
  }

  /// Init expression span for this HIR initializer body, when present.
  fn hir_own_initializer_expr_span(&self) -> Option<TextRange> {
    for &stmt_id in &self.body.root_stmts {
      let stmt = self.body.stmts.get(stmt_id.0 as usize)?;
      match &stmt.kind {
        hir_js::StmtKind::Var(var) => {
          for decl in &var.declarators {
            if let Some(init) = decl.init {
              return self.body.exprs.get(init.0 as usize).map(|e| e.span);
            }
          }
        }
        hir_js::StmtKind::Expr(expr) => {
          return self.body.exprs.get(expr.0 as usize).map(|e| e.span);
        }
        _ => {}
      }
    }
    None
  }

  fn check_var_initializer_decl(&mut self, pat_span: TextRange, info: VarInfo<'_>) -> bool {
    self.check_cancelled();
    let mut has_type_params = false;
    if let Some(init) = info.initializer {
      // Initializer bodies can be nested inside functions. Bind any enclosing
      // function parameters so references like `const x = param;` do not emit
      // spurious `unknown identifier` diagnostics when the initializer is
      // type-checked in isolation.
      has_type_params = self.bind_enclosing_params(loc_to_range(self.file, init.loc));
      // HIR-only when present: `VarDeclarator.type_annotation` via TypeExprId.
      // AstIndex `type_annotation` is residual (complex types / no arenas / JSDoc).
      let annotation = self.var_annotation_ty(pat_span, info.type_annotation, info.decl_loc);
      let init_ty = match annotation {
        Some(expected) => self.check_expr_with_expected(init, expected),
        None => self.check_expr(init),
      };
      if let Some(annotation) = annotation {
        // Mirror `check_var_decl`: anchor assignment diagnostics on the binding
        // name/pattern to match tsc and dedupe with the top-level var check.
        let range_override = self
          .index
          .pats
          .get(&pat_span)
          .copied()
          .map(|pat| self.binding_name_range(pat))
          .unwrap_or(pat_span);
        self.check_assignable(init, init_ty, annotation, Some(range_override));
      }
      let prim = self.store.primitive_ids();
      let binding_ty = match info.mode {
        VarDeclMode::Const | VarDeclMode::Using | VarDeclMode::AwaitUsing => init_ty,
        _ => self.base_type(init_ty),
      };
      let mut ty = annotation.unwrap_or(binding_ty);
      let empty_array_init = matches!(
        init.stx.as_ref(),
        AstExpr::LitArr(arr) if arr.stx.elements.is_empty()
      );
      if self.no_implicit_any && annotation.is_none() && empty_array_init {
        // Mirror `check_var_decl` / tsc `autoArrayType`.
        ty = self.store.intern_type(TypeKind::Array {
          ty: prim.any,
          readonly: false,
        });
      } else if self.no_implicit_any && annotation.is_none() && ty == prim.unknown {
        if let Some(pat) = self.index.pats.get(&pat_span).copied() {
          self.report_implicit_any_in_pat(pat);
        } else {
          self.report_implicit_any(pat_span, None);
        }
        ty = prim.any;
      }
      if let Some(pat) = self.index.pats.get(&pat_span).copied() {
        self.bind_pattern(pat, ty);
      }
    }
    if has_type_params {
      self.type_param_scopes.pop();
      self.lowerer.pop_type_param_scope();
    }
    true
  }

  /// Type-check a class-field initializer body, setting lexical class context
  /// for private-identifier access (TS18013/TS18014).
  fn check_class_field_initializer_body(&mut self, body_range: TextRange) -> bool {
    let mut best_expr: Option<(u32, TextRange, &Node<AstExpr>)> = None;
    for (span, expr) in self.index.exprs.iter() {
      let span = *span;
      if !contains_range(span, body_range) {
        continue;
      }
      let len = span.end.saturating_sub(span.start);
      let replace = match best_expr {
        Some((best_len, best_span, _)) => {
          len < best_len || (len == best_len && span.start < best_span.start)
        }
        None => true,
      };
      if replace {
        best_expr = Some((len, span, *expr));
      }
    }
    let Some((_len, expr_span, expr)) = best_expr else {
      return false;
    };
    self.check_cancelled();
    let prev_props = self.current_class_field_param_props;
    self.current_class_field_param_props = self
      .index
      .class_field_param_props
      .get(&expr_span)
      .or_else(|| self.index.class_field_param_props.get(&body_range))
      .map(|props| props.as_slice());
    let prev_field_init = self.class_field_initializer.clone();
    let prev_enclosing_class = self.enclosing_class_index;
    let prev_this = self.contextual_this_ty.take();
    let field_info = self
      .index
      .class_field_initializer(expr_span)
      .or_else(|| self.index.class_field_initializer(body_range));
    self.class_field_initializer = field_info
      .as_ref()
      .map(|info| ClassFieldInitializerContext {
        class_index: info.class_index,
        member_index: info.member_index,
        is_static: info.is_static,
      });
    if let Some(info) = field_info.as_ref() {
      // Needed for private-identifier lexical lookup (TS18013/TS18014) on
      // `D.#method()` inside static field initializers.
      self.enclosing_class_index = Some(info.class_index);
      self.contextual_this_ty = self.resolve_class_this_type(info.class_index, info.is_static);
      if !info.prop_name.is_empty() {
        self
          .field_init_type_stack
          .push((info.class_index, info.prop_name.clone()));
      }
    }
    // Contextual-type the initializer from the field's type annotation
    // (tsc: assertion-function / callable field inits — avoids false TC3000
    // on unannotated arrow params).
    let expected = field_info.as_ref().and_then(|info| {
      let class = self.index.classes.get(info.class_index)?;
      let fields = if info.is_static {
        &class.static_fields
      } else {
        &class.instance_fields
      };
      fields
        .iter()
        .find(|f| f.name == info.prop_name)
        .and_then(|f| f.type_annotation)
        .map(|ann| self.lowerer.lower_type_expr(ann))
    });
    let _ = match expected {
      Some(expected) => self.check_expr_with_expected(expr, expected),
      None => self.check_expr(expr),
    };
    if let Some(info) = field_info.as_ref() {
      if !info.prop_name.is_empty() {
        let _ = self.field_init_type_stack.pop();
      }
    }
    self.class_field_initializer = prev_field_init;
    self.enclosing_class_index = prev_enclosing_class;
    self.contextual_this_ty = prev_this;
    self.current_class_field_param_props = prev_props;
    true
  }

  /// Bind the closest enclosing function's parameters into the current scope.
  ///
  /// Returns `true` when a type parameter scope was pushed and must be popped by
  /// the caller.
  pub(crate) fn bind_enclosing_params(&mut self, span: TextRange) -> bool {
    let mut best: Option<FunctionInfo> = None;
    for (idx, func) in self.index.functions.iter().copied().enumerate() {
      if idx % 2048 == 0 {
        self.check_cancelled();
      }
      let strictly_contains = func.func_span.start < span.start && func.func_span.end > span.end;
      if !strictly_contains {
        continue;
      }
      let len = func.func_span.end.saturating_sub(func.func_span.start);
      let replace = match best {
        Some(existing) => {
          let existing_len = existing
            .func_span
            .end
            .saturating_sub(existing.func_span.start);
          len < existing_len
        }
        None => true,
      };
      if replace {
        best = Some(func);
      }
    }

    let Some(func) = best else {
      return false;
    };
    let func_node = func.func;
    let prim = self.store.primitive_ids();

    let mut type_param_decls = Vec::new();
    let mut has_type_params = false;
    if let Some(params) = func_node.stx.type_parameters.as_ref() {
      self.lowerer.push_type_param_scope();
      has_type_params = true;
      type_param_decls = self.lower_type_params(params);
      self.type_param_scopes.push(type_param_decls.clone());
    } else if let Some(templates) = self.jsdoc_templates_owned(func_node) {
      self.lowerer.push_type_param_scope();
      has_type_params = true;
      type_param_decls = self.register_jsdoc_templates(&templates);
      self.type_param_scopes.push(type_param_decls.clone());
    }
    pub(crate) fn bind_missing(
      checker: &mut Checker<'_>,
      pat: &Node<AstPat>,
      ty: TypeId,
      type_params: &[TypeParamDecl],
    ) {
      match pat.stx.as_ref() {
        AstPat::Id(id) => {
          if checker.lookup(&id.stx.name).is_none() {
            checker.insert_binding(id.stx.name.clone(), ty, type_params.to_vec());
          }
        }
        AstPat::Arr(arr) => {
          for elem in arr.stx.elements.iter().flatten() {
            bind_missing(checker, &elem.target, ty, type_params);
          }
          if let Some(rest) = &arr.stx.rest {
            bind_missing(checker, rest, ty, type_params);
          }
        }
        AstPat::Obj(obj) => {
          for prop in obj.stx.properties.iter() {
            bind_missing(checker, &prop.stx.target, ty, type_params);
          }
          if let Some(rest) = &obj.stx.rest {
            bind_missing(checker, rest, ty, type_params);
          }
        }
        AstPat::AssignTarget(_) => {}
      }
    }
    for param in func_node.stx.parameters.iter() {
      bind_missing(
        self,
        &param.stx.pattern.stx.pat,
        prim.unknown,
        &type_param_decls,
      );
    }
    has_type_params
  }

  pub(crate) fn bind_params(
    &mut self,
    func: &Node<Func>,
    type_param_decls: &[TypeParamDecl],
    contextual_sig: Option<&Signature>,
  ) {
    let prim = self.store.primitive_ids();
    // Resolve JSDoc `@param` (incl. nested `opts.x` folding) before the
    // mutable per-param loop so we do not borrow `jsdoc_source` across it.
    // Report TS8032 here (once per body) rather than from signature synthesis.
    let jsdoc_params = self.jsdoc_resolved_param_types(func, true);
    for (idx, param) in func.stx.parameters.iter().enumerate() {
      if idx % 64 == 0 {
        self.check_cancelled();
      }
      self.check_private_name_in_binding_pat(&param.stx.pattern.stx.pat, true);
      // Prefer HIR `FunctionData.params[idx].type_annotation` when this AST
      // function is the body being checked. Residual AST: nested refine /
      // `typeof import(...)` / missing arenas / JSDoc `@param`.
      let annotation = self.hir_param_annotation_ty(func, idx).or_else(|| {
        param
          .stx
          .type_annotation
          .as_ref()
          .map(|ann| self.lowerer.lower_type_expr(ann))
      });
      let param_name = match param.stx.pattern.stx.pat.stx.as_ref() {
        AstPat::Id(id) => Some(id.stx.name.as_str()),
        _ => None,
      };
      // checkJs: `@param {T} name` / nested `opts.x` fills in when there is no
      // TypeScript annotation.
      let jsdoc_param_ty = if annotation.is_none() {
        param_name.and_then(|name| jsdoc_params.get(name).map(|p| p.ty))
      } else {
        None
      };
      let default_ty = param.stx.default_value.as_ref().map(|d| self.check_expr(d));
      // A parameter initializer lets TypeScript infer the parameter's type from
      // the (widened) initializer, so `--noImplicitAny` does not flag it and the
      // parameter is *not* treated as implicitly `any` (see tsc's
      // `nullishCoalescingOperator6.ts`). We only treat the default as an
      // inferred type when it widens to something other than `any`/`unknown`.
      let inferred_default_ty = default_ty.map(|d| self.base_type(d)).filter(|ty| {
        let prim = self.store.primitive_ids();
        *ty != prim.any && *ty != prim.unknown
      });
      let contextual_param_ty = contextual_sig
        .and_then(|sig| {
          if let Some(param_sig) = sig.params.get(idx) {
            if param_sig.rest && !param.stx.rest {
              let elem_ty = self.spread_element_type(param_sig.ty);
              return Some(elem_ty);
            }
            return Some(param_sig.ty);
          }

          let rest = sig
            .params
            .iter()
            .enumerate()
            .find(|(_, param)| param.rest)
            .filter(|(rest_idx, _)| idx >= *rest_idx);
          rest.map(|(_, rest_param)| {
            if param.stx.rest {
              rest_param.ty
            } else {
              self.spread_element_type(rest_param.ty)
            }
          })
        })
        // Treat `unknown` contextual parameter types as absent so `--noImplicitAny`
        // still reports implicit `any` for untyped parameters when the surrounding
        // context doesn't provide a real type (e.g. uncontextualized arrow
        // functions).
        .filter(|ty| *ty != prim.unknown);
      let is_this = idx == 0
        && matches!(
          param.stx.pattern.stx.pat.stx.as_ref(),
          AstPat::Id(id) if id.stx.name == "this"
        );
      let implicit_any = self.no_implicit_any
        && !is_this
        && annotation.is_none()
        && jsdoc_param_ty.is_none()
        && contextual_param_ty.is_none()
        && inferred_default_ty.is_none();
      let mut ty = annotation
        .or(jsdoc_param_ty)
        .or(contextual_param_ty)
        .or(inferred_default_ty)
        .unwrap_or(if implicit_any { prim.any } else { prim.unknown });
      if implicit_any {
        let range = loc_to_range(self.file, param.stx.pattern.stx.pat.loc);
        self.report_implicit_any(range, param_name);
      }
      if let Some(default) = default_ty {
        ty = self.store.union(vec![ty, default]);
      }
      // Bind parameters directly from the AST node. Function parameters must be
      // in scope for identifier resolution while checking the body; relying on
      // `AstIndex` span lookups here can be brittle when spans differ between
      // HIR lowering and parse-js nodes.
      self.bind_pattern_with_type_params(&param.stx.pattern.stx.pat, ty, type_param_decls.to_vec());
    }
  }

  pub(crate) fn lower_type_params(
    &mut self,
    params: &[Node<parse_js::ast::type_expr::TypeParameter>],
  ) -> Vec<TypeParamDecl> {
    self.lowerer.register_type_params(params)
  }

  pub(crate) fn check_function_body(&mut self, func: &Node<Func>) {
    match &func.stx.body {
      Some(FuncBody::Block(block)) => {
        self.check_stmt_list(block);
      }
      Some(FuncBody::Expression(expr)) => {
        let expr_ty = match self.expected_return {
          Some(expected) if matches!(self.store.type_kind(expected), TypeKind::Void) => {
            self.check_expr(expr)
          }
          Some(expected) => self.check_expr_with_expected(expr, expected),
          None => self.check_expr(expr),
        };
        let ty = if self.in_async_function {
          awaited_type(self.store.as_ref(), expr_ty, self.ref_expander)
        } else {
          expr_ty
        };
        if let Some(expected) = self.expected_return {
          if !matches!(self.store.type_kind(expected), TypeKind::Void)
            && !self.expected_return_defer_type_params
          {
            if self.is_enclosing_type_param(expected) {
              if !self.assignable_to_enclosing_type_param(ty, expected) {
                self.diagnostics.push(codes::TYPE_MISMATCH.error(
                  format!(
                    "Type '{}' is not assignable to type '{}'.",
                    TypeDisplay::new(self.store.as_ref(), ty),
                    TypeDisplay::new(self.store.as_ref(), expected),
                  ),
                  Span {
                    file: self.file,
                    range: loc_to_range(self.file, expr.loc),
                  },
                ));
              }
            } else {
              self.check_assignable(expr, ty, expected, None);
            }
          }
        }
        self.return_types.push(ty);
      }
      None => {}
    }
  }

  pub(crate) fn contextual_signature(&self) -> Option<Signature> {
    let ty = self.contextual_fn_ty?;
    match self.store.type_kind(ty) {
      TypeKind::Callable { overloads } => overloads.first().map(|sig| self.store.signature(*sig)),
      _ => None,
    }
  }

  pub(crate) fn check_stmt_list(&mut self, stmts: &[Node<Stmt>]) {
    for (idx, stmt) in stmts.iter().enumerate() {
      if idx % 128 == 0 {
        self.check_cancelled();
      }
      self.check_stmt(stmt);
    }
  }

  /// Iterated element type for `for…of` (tsc). `any` iterates as `any` (not
  /// `unknown`) so downstream assignment checks are not poisoned.
  pub(crate) fn for_of_element_type(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::Any => prim.any,
      TypeKind::Union(members) => self.store.union(
        members
          .iter()
          .map(|m| self.for_of_element_type(*m))
          .collect(),
      ),
      TypeKind::Intersection(members) => self.store.intersection(
        members
          .iter()
          .map(|m| self.for_of_element_type(*m))
          .collect(),
      ),
      TypeKind::Array { ty, .. } => ty,
      TypeKind::Tuple(elems) => self.store.union(elems.iter().map(|e| e.ty).collect()),
      TypeKind::String | TypeKind::StringLiteral(_) => prim.string,
      _ => super::flow_ops::iterable_protocol_element(&self.store, self.ref_expander, ty)
        .unwrap_or(prim.unknown),
    }
  }

  /// Iterated element type for `for await…of` (tsc): the async-iterable
  /// protocol (`[Symbol.asyncIterator]`) when present, else the sync
  /// protocol — the element is then awaited (`for await (y of
  /// iterableOfPromise)` unwraps `Promise<number>` → `number`;
  /// `types.forAwait.es2018.1.ts`).
  pub(crate) fn for_await_element_type(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    let ty = self.expand_ref(ty);
    let elem = match self.store.type_kind(ty) {
      TypeKind::Any => prim.any,
      TypeKind::Union(members) => self.store.union(
        members
          .iter()
          .map(|m| self.for_await_element_type(*m))
          .collect(),
      ),
      TypeKind::Array { .. }
      | TypeKind::Tuple(_)
      | TypeKind::String
      | TypeKind::StringLiteral(_) => self.for_of_element_type(ty),
      _ => super::flow_ops::iterable_protocol_element_for(
        &self.store,
        self.ref_expander,
        ty,
        "asyncIterator",
      )
      .or_else(|| {
        super::flow_ops::iterable_protocol_element_for(
          &self.store,
          self.ref_expander,
          ty,
          "iterator",
        )
      })
      .unwrap_or(prim.unknown),
    };
    awaited_type(self.store.as_ref(), elem, self.ref_expander)
  }

  /// For-in/of LHS assignment to an existing binding: the loop writes into the
  /// declared variable — check the element type against its *declared* type
  /// and narrow only the flow type. Plain `check_pat` would rebind the name
  /// with `declared_ty = element`, turning later writes into false TS2322s
  /// (`controlFlowForOfStatement.ts`: `for (x of obj) { x = x.toExponential() }`
  /// with `x: string | number | boolean | RegExp`).
  pub(crate) fn check_for_in_of_assign_lhs(&mut self, pat: &Node<AstPat>, loop_var_ty: TypeId) {
    if let AstPat::Id(id) = pat.stx.as_ref() {
      if let Some(binding) = self.lookup(&id.stx.name) {
        let declared = binding.declared_ty;
        // tsc skips the element-vs-declared check when the variable's type is
        // a type parameter (`let k1: K; for (k1 in obj)` with `K extends
        // string` is clean — `keyofAndForIn.ts`).
        let skip_check = matches!(
          self.store.type_kind(self.store.canon(declared)),
          TypeKind::TypeParam(_)
        );
        if !skip_check && !self.is_assignable_for_check(loop_var_ty, declared) {
          let code = self.assignability_mismatch_code(loop_var_ty, declared, &codes::TYPE_MISMATCH);
          self.diagnostics.push(code.error(
            "assignment type mismatch",
            Span {
              file: self.file,
              range: loc_to_range(self.file, pat.loc),
            },
          ));
        }
        let _ = self.update_binding_ty(&id.stx.name, loop_var_ty);
        self.record_pat_type(pat.loc, loop_var_ty);
        return;
      }
    }
    self.check_pat(pat, loop_var_ty);
  }

  pub(crate) fn check_stmt(&mut self, stmt: &Node<Stmt>) {
    match stmt.stx.as_ref() {
      Stmt::Expr(expr_stmt) => {
        self.check_expr(&expr_stmt.stx.expr);
      }
      Stmt::ExportDefaultExpr(default_expr) => {
        self.check_expr(&default_expr.stx.expression);
      }
      Stmt::Return(ret) => {
        let prim = self.store.primitive_ids();
        let expr_ty = match (self.expected_return, ret.stx.value.as_ref()) {
          // Void expected: still synthesize the expression, but do not push
          // the return type as a contextual check target (tsc ignores values
          // returned from `() => void` callbacks).
          (Some(expected), Some(value))
            if matches!(self.store.type_kind(expected), TypeKind::Void) =>
          {
            self.check_expr(value)
          }
          (Some(expected), Some(value)) => self.check_expr_with_expected(value, expected),
          (None, Some(value)) => self.check_expr(value),
          (_, None) => prim.undefined,
        };
        let ty = if self.in_async_function {
          awaited_type(self.store.as_ref(), expr_ty, self.ref_expander)
        } else {
          expr_ty
        };
        if let (Some(expected), Some(value)) = (self.expected_return, ret.stx.value.as_ref()) {
          if !matches!(self.store.type_kind(expected), TypeKind::Void)
            && !self.expected_return_defer_type_params
          {
            if self.is_enclosing_type_param(expected) {
              // Naked enclosing type parameter as return: only `any` / same
              // param (and nullish when `strictNullChecks` is off). Do not use
              // `RelateCtx`'s permissive TypeParam-as-unknown rule here — that
              // would silence `return null` in `<T>(): T`. Keep contextual
              // lambda checks against uninstantiated params via relate.
              if !self.assignable_to_enclosing_type_param(ty, expected) {
                let range = loc_to_range(self.file, ret.loc);
                // tsc anchors on the `return` keyword (not the whole statement).
                let start = range.start;
                let end = start.saturating_add("return".len() as u32).min(range.end);
                self.diagnostics.push(codes::TYPE_MISMATCH.error(
                  format!(
                    "Type '{}' is not assignable to type '{}'.",
                    TypeDisplay::new(self.store.as_ref(), ty),
                    TypeDisplay::new(self.store.as_ref(), expected),
                  ),
                  Span {
                    file: self.file,
                    range: TextRange::new(start, end),
                  },
                ));
              }
            } else {
              self.check_assignable(value, ty, expected, None);
            }
          }
        }
        self.return_types.push(ty);
      }
      Stmt::Block(block) => {
        self.scopes.push(Scope::default());
        self.check_stmt_list(&block.stx.body);
        self.scopes.pop();
      }
      Stmt::If(if_stmt) => {
        self.check_expr(&if_stmt.stx.test);
        // AST pass runs before HIR CFA merges expr_types, so apply typeof
        // binding overrides here for subsequent-`var` TS2403 / branch types
        // (`TypeGuardWithEnumUnion.ts`).
        let typeof_narrow =
          Self::ast_typeof_equality(&if_stmt.stx.test).and_then(|(name, tag, negate)| {
            let binding = self.lookup(&name)?;
            let (yes, no) = narrow_by_typeof(binding.ty, &tag, &self.store, self.ref_expander);
            let (then_ty, else_ty) = if negate { (no, yes) } else { (yes, no) };
            Some((name, then_ty, else_ty))
          });
        let then_overrides = typeof_narrow
          .as_ref()
          .map(|(name, then_ty, _)| vec![(name.clone(), *then_ty)])
          .unwrap_or_default();
        let else_overrides = typeof_narrow
          .as_ref()
          .map(|(name, _, else_ty)| vec![(name.clone(), *else_ty)])
          .unwrap_or_default();
        let spi_before = self.spi_ctor.as_ref().map(|s| s.assigned.clone());
        self.with_binding_ty_overrides(&then_overrides, |this| {
          this.scopes.push(Scope::default());
          this.check_stmt(&if_stmt.stx.consequent);
          this.scopes.pop();
        });
        let spi_then = self.spi_ctor.as_ref().map(|s| s.assigned.clone());
        if let Some(before) = spi_before.clone() {
          if let Some(state) = self.spi_ctor.as_mut() {
            state.assigned = before;
          }
        }
        if let Some(alt) = &if_stmt.stx.alternate {
          self.with_binding_ty_overrides(&else_overrides, |this| {
            this.scopes.push(Scope::default());
            this.check_stmt(alt);
            this.scopes.pop();
          });
        }
        // Continuing after if: intersection of then/else assigned sets.
        if let (Some(then_set), Some(state)) = (spi_then, self.spi_ctor.as_mut()) {
          let else_set = state.assigned.clone();
          state.assigned = then_set.intersection(&else_set).cloned().collect();
        }
      }
      Stmt::While(while_stmt) => {
        self.check_expr(&while_stmt.stx.condition);
        self.scopes.push(Scope::default());
        self.check_stmt(&while_stmt.stx.body);
        self.scopes.pop();
      }
      Stmt::DoWhile(do_while) => {
        self.scopes.push(Scope::default());
        self.check_stmt(&do_while.stx.body);
        self.scopes.pop();
        self.check_expr(&do_while.stx.condition);
      }
      Stmt::ForTriple(for_stmt) => {
        use parse_js::ast::stmt::ForTripleStmtInit;
        self.scopes.push(Scope::default());
        match &for_stmt.stx.init {
          ForTripleStmtInit::Expr(expr) => {
            self.check_expr(expr);
          }
          ForTripleStmtInit::Decl(decl) => {
            self.check_var_decl(decl);
          }
          ForTripleStmtInit::None => {}
        }
        if let Some(cond) = &for_stmt.stx.cond {
          self.check_expr(cond);
        }
        if let Some(post) = &for_stmt.stx.post {
          self.check_expr(post);
        }
        self.check_block_body(&for_stmt.stx.body.stx.body);
        self.scopes.pop();
      }
      Stmt::ForIn(for_in) => {
        use parse_js::ast::stmt::ForInOfLhs;
        self.scopes.push(Scope::default());
        // tsc types the for-in loop variable as `string` unconditionally.
        // Binding `unknown` here poisons downstream assignment checks
        // (`x = y` → unknown ↛ declared — `controlFlowForInStatement.ts`).
        let loop_var_ty = self.store.primitive_ids().string;
        match &for_in.stx.lhs {
          ForInOfLhs::Assign(pat) => {
            // `for (#field in v)` — bare private is not a legal for-in LHS (TS2406).
            if let AstPat::Id(id) = pat.stx.as_ref() {
              if id.stx.name.starts_with('#') {
                self.diagnostics.push(codes::FOR_IN_LHS_INVALID.error(
                  "The left-hand side of a 'for...in' statement must be a variable or a property access.",
                  Span {
                    file: self.file,
                    range: loc_to_range(self.file, pat.loc),
                  },
                ));
              }
            }
            self.check_for_in_of_assign_lhs(pat, loop_var_ty);
          }
          ForInOfLhs::Decl((_, pat_decl)) => {
            self.check_pat(&pat_decl.stx.pat, loop_var_ty);
          }
        }
        let rhs_ty = self.check_expr(&for_in.stx.rhs);
        // `for (let d in #field in v)` — RHS is boolean from `#field in v` (TS2407).
        let expanded = self.expand_ref(rhs_ty);
        let prim = self.store.primitive_ids();
        let rhs_ok = matches!(
          self.store.type_kind(expanded),
          TypeKind::Any
            | TypeKind::Object(_)
            | TypeKind::EmptyObject
            | TypeKind::Array { .. }
            | TypeKind::Tuple(_)
            | TypeKind::Callable { .. }
            | TypeKind::TypeParam(_)
            | TypeKind::Ref { .. }
            // Mapped types are object types (`for (k in obj)` with
            // `obj: { [P in K]: T }` — `keyofAndForIn.ts`).
            | TypeKind::Mapped(_)
            | TypeKind::Never
        ) || expanded == prim.unknown;
        if !rhs_ok {
          self.diagnostics.push(codes::FOR_IN_RHS_INVALID.error(
            format!(
              "The right-hand side of a 'for...in' statement must be of type 'any', an object type or a type parameter, but here has type '{}'.",
              TypeDisplay::new(self.store.as_ref(), rhs_ty)
            ),
            Span {
              file: self.file,
              range: loc_to_range(self.file, for_in.stx.rhs.loc),
            },
          ));
        }
        self.check_block_body(&for_in.stx.body.stx.body);
        self.scopes.pop();
      }
      Stmt::ForOf(for_of) => {
        use parse_js::ast::stmt::ForInOfLhs;
        self.scopes.push(Scope::default());
        // The loop variable's type is the iterated element type (tsc), which
        // downstream assignment checks need (`ES5For-of34.ts`: `string`
        // elements assigned to `foo().x: number` is TS2322). For `using`/
        // `await using` heads, bind the LHS pattern (TDZ) *before* evaluating
        // the RHS so the iterable resolves the loop variable itself —
        // `for await (await using of of of)` is TS2448 (TDZ), not TS2304
        // (`awaitUsingDeclarationsInForAwaitOf.2.ts`, tsc issue #55555).
        if let ForInOfLhs::Decl((_, pat_decl)) = &for_of.stx.lhs {
          let _ = self.seed_hoisted_var_pat(&pat_decl.stx.pat, self.store.primitive_ids().unknown);
        }
        let rhs_ty = self.check_expr(&for_of.stx.rhs);
        let loop_var_ty = if for_of.stx.await_ {
          self.for_await_element_type(rhs_ty)
        } else {
          self.for_of_element_type(rhs_ty)
        };
        match &for_of.stx.lhs {
          ForInOfLhs::Assign(pat) => {
            self.check_for_in_of_assign_lhs(pat, loop_var_ty);
          }
          ForInOfLhs::Decl((_, pat_decl)) => {
            self.check_pat(&pat_decl.stx.pat, loop_var_ty);
          }
        }
        self.check_block_body(&for_of.stx.body.stx.body);
        self.scopes.pop();
      }
      Stmt::Switch(sw) => {
        let _ = self.check_expr(&sw.stx.test);
        for branch in sw.stx.branches.iter() {
          if let Some(case) = &branch.stx.case {
            self.check_expr(case);
          }
          self.scopes.push(Scope::default());
          self.check_stmt_list(&branch.stx.body);
          self.scopes.pop();
        }
      }
      Stmt::Try(tr) => {
        self.check_block_body(&tr.stx.wrapped.stx.body);
        if let Some(catch) = &tr.stx.catch {
          self.scopes.push(Scope::default());
          if let Some(param) = &catch.stx.parameter {
            self.check_pat(&param.stx.pat, self.store.primitive_ids().unknown);
          }
          self.check_block_body(&catch.stx.body);
          self.scopes.pop();
        }
        if let Some(finally) = &tr.stx.finally {
          self.check_block_body(&finally.stx.body);
        }
      }
      Stmt::Throw(th) => {
        self.check_expr(&th.stx.value);
      }
      Stmt::Label(label) => {
        self.check_stmt(&label.stx.statement);
      }
      Stmt::With(w) => {
        self.check_expr(&w.stx.object);
        self.scopes.push(Scope::default());
        self.check_stmt(&w.stx.body);
        self.scopes.pop();
      }
      Stmt::VarDecl(decl) => self.check_var_decl(decl),
      Stmt::EnumDecl(en) => self.check_enum_private_member_names(en),
      Stmt::FunctionDecl(func) => {
        // Function declarations are handled by separate bodies; bind the name for call sites in
        // this body, but preserve any pre-seeded binding (e.g. merged namespace + value types)
        // by intersecting rather than overwriting.
        if let Some(name) = func.stx.name.as_ref() {
          let name_str = name.stx.name.clone();
          let fn_ty = self.function_type(&func.stx.function);
          if let Some(existing) = self.lookup(&name_str) {
            let has_callables = !callable_signatures(self.store.as_ref(), existing.ty).is_empty();
            let ty = if has_callables {
              existing.ty
            } else {
              self.store.intersection(vec![existing.ty, fn_ty])
            };
            self.insert_binding(name_str, ty, Vec::new());
          } else {
            self.insert_binding(name_str, fn_ty, Vec::new());
          }
        }
      }
      Stmt::ClassDecl(class_decl) => {
        // Nested class declarations are checked as separate bodies; bind the
        // class name here so later `new B()` / `B.#x` in this body resolve
        // (tsc block-scoped class binding after the declaration). Do **not**
        // overwrite pre-seeded top-level class value types — a synthesized
        // shape is lossy for private accessors (TS18013 → false TS2339).
        //
        // Push class type parameters before checking `extends Parent<T>` so
        // Instantiation type args do not emit false TC2008.
        let mut pushed_type_params = false;
        if let Some(params) = class_decl.stx.type_parameters.as_ref() {
          self.lowerer.push_type_param_scope();
          let decls = self.lower_type_params(params);
          self.type_param_scopes.push(decls);
          pushed_type_params = true;
        }
        if let Some(extends) = class_decl.stx.extends.as_ref() {
          let _ = self.check_expr(extends);
        }
        if pushed_type_params {
          self.type_param_scopes.pop();
          self.lowerer.pop_type_param_scope();
        }
        if let Some(name) = class_decl.stx.name.as_ref() {
          let name_str = name.stx.name.clone();
          if self.lookup(&name_str).is_none() {
            let range = loc_to_range(self.file, class_decl.loc);
            let ty = if let Some(&class_index) = self.index.classes_by_span.get(&range) {
              self
                .synthesize_class_expression_value_type(class_index)
                .unwrap_or_else(|| self.store.primitive_ids().unknown)
            } else {
              self.store.primitive_ids().unknown
            };
            self.insert_binding(name_str, ty, Vec::new());
          }
        }
      }
      Stmt::NamespaceDecl(ns) => self.check_namespace(ns),
      Stmt::ModuleDecl(module) => {
        // `declare module "name"` (string-literal name) is an ambient
        // *external module* declaration: its body is a separate module scope
        // whose declarations never merge with the enclosing globals
        // (`ambientDeclarations.ts` — `var q` inside `declare module
        // 'external1'` is not a redeclaration of the global `var q`).
        if let Some(body) = &module.stx.body {
          let name = match &module.stx.name {
            parse_js::ast::ts_stmt::ModuleName::Identifier(name) => name.clone(),
            parse_js::ast::ts_stmt::ModuleName::String(name) => name.clone(),
          };
          let key = format!("module:{name}");
          let mut scope = self.namespace_scopes.remove(&key).unwrap_or_default();
          let established = self
            .namespace_established_vars
            .remove(&key)
            .unwrap_or_default();
          let outer_established =
            std::mem::replace(&mut self.established_var_bindings, established);
          self.scopes.push(scope);
          self.check_stmt_list(body);
          scope = self.scopes.pop().unwrap_or_default();
          let established =
            std::mem::replace(&mut self.established_var_bindings, outer_established);
          self.namespace_scopes.insert(key.clone(), scope);
          self.namespace_established_vars.insert(key, established);
        }
      }
      Stmt::GlobalDecl(global) => self.check_stmt_list(&global.stx.body),
      _ => {}
    }
  }

  pub(crate) fn check_block_body(&mut self, stmts: &[Node<Stmt>]) {
    self.scopes.push(Scope::default());
    self.check_stmt_list(stmts);
    self.scopes.pop();
  }

  pub(crate) fn check_var_decl(&mut self, decl: &Node<VarDecl>) {
    let prim = self.store.primitive_ids();
    if self.check_var_assignments
      && matches!(decl.stx.mode, VarDeclMode::AwaitUsing)
      && !self.in_async_function
      && !matches!(self.body_kind, BodyKind::TopLevel)
    {
      let range = loc_to_range(self.file, decl.loc);
      let start = range.start;
      let end = start.saturating_add("await".len() as u32);
      self.diagnostics.push(codes::AWAIT_USING_REQUIRES_ASYNC_CONTEXT.error(
        "'await using' statements are only allowed within async functions and at the top levels of modules.",
        Span::new(self.file, TextRange::new(start, end)),
      ));
    }
    for declarator in decl.stx.declarators.iter() {
      self.check_private_name_in_binding_pat(&declarator.pattern.stx.pat, false);
      let pat_span = loc_to_range(self.file, declarator.pattern.stx.pat.loc);
      // HIR-only when present: prefer `VarDeclarator.type_annotation` (TypeExprId).
      // Residual AST `TypeLowerer` / JSDoc `@type` for `import(...)` / no arenas.
      let annot_ty =
        self.var_annotation_ty(pat_span, declarator.type_annotation.as_ref(), decl.loc);
      // `var` is function-scoped and hoisted: the binding is visible in its own
      // initializer (`var x = f(x)`, `` var x = `a${x}` ``). Seed before checking
      // the initializer so nested template/call checking does not emit false TS2304.
      if matches!(decl.stx.mode, VarDeclMode::Var) {
        let _ = self.seed_hoisted_var_pat(&declarator.pattern.stx.pat, prim.undefined);
      }
      let init_ty = if self.check_var_assignments {
        declarator
          .initializer
          .as_ref()
          .map(|init| {
            if let AstPat::Obj(obj) = declarator.pattern.stx.pat.stx.as_ref() {
              self.check_abstract_props_destructured_from_this(obj, init);
            }
            match annot_ty {
              Some(expected) => self.check_expr_with_expected(init, expected),
              None => self.check_expr(init),
            }
          })
          .unwrap_or(prim.unknown)
      } else {
        prim.unknown
      };

      if matches!(decl.stx.mode, VarDeclMode::Using | VarDeclMode::AwaitUsing)
        && !matches!(declarator.pattern.stx.pat.stx.as_ref(), AstPat::Id(_))
      {
        self.diagnostics.push(codes::USING_BINDING_PATTERN.error(
          "'using' declarations may not have binding patterns.",
          Span::new(
            self.file,
            loc_to_range(self.file, declarator.pattern.stx.pat.loc),
          ),
        ));
      }

      if self.check_var_assignments {
        if let Some(init) = declarator.initializer.as_ref() {
          match decl.stx.mode {
            VarDeclMode::Using => self.check_using_initializer(init, init_ty, "Disposable"),
            VarDeclMode::AwaitUsing => {
              self.check_using_initializer(init, init_ty, "AsyncDisposable")
            }
            _ => {}
          }
        }
      }
      let binding_ty = match decl.stx.mode {
        VarDeclMode::Const | VarDeclMode::Using | VarDeclMode::AwaitUsing => init_ty,
        _ => self.base_type(init_ty),
      };
      let mut final_ty = annot_ty.unwrap_or(binding_ty);
      // tsc: a non-ambient empty-array initializer binds as `any[]` when
      //   1. `--noImplicitAny` is on (control-flow `autoArrayType`; ours does
      //      not evolve per-push, staying `any[]`), or
      //   2. `--strictNullChecks` is off (`checkArrayLiteral` synthesizes
      //      `undefinedWideningType[]`, and `getWidenedType` for a variable
      //      declaration widens `undefinedWideningType` to `any`).
      // Otherwise (strictNullChecks on, noImplicitAny off) the binding keeps
      // the synthesized `never[]` and `push` errors TS2345 (tsc).
      let empty_array_init = declarator.initializer.as_ref().is_some_and(|init| {
        matches!(
          init.stx.as_ref(),
          AstExpr::LitArr(arr) if arr.stx.elements.is_empty()
        )
      });
      if (self.no_implicit_any || !self.strict_null_checks)
        && annot_ty.is_none()
        && empty_array_init
      {
        final_ty = self.store.intern_type(TypeKind::Array {
          ty: prim.any,
          readonly: false,
        });
      } else if self.no_implicit_any && annot_ty.is_none() && final_ty == prim.unknown {
        // Like TypeScript `--noImplicitAny`, report untyped bindings that
        // would otherwise become `any`. Use `any` for recovery to keep
        // type checking resilient.
        self.report_implicit_any_in_pat(&declarator.pattern.stx.pat);
        final_ty = prim.any;
      }
      // JS expando container (`var Outer = {}` with registered `Outer.X = …`
      // members): tsc binds the expando members onto the var's own type, so
      // keep the seeded member-augmented binding instead of the bare `{}`
      // initializer type.
      if self.jsdoc_source.is_some() && annot_ty.is_none() {
        if let AstPat::Id(id) = declarator.pattern.stx.pat.stx.as_ref() {
          if let Some(seeded) = self.js_expando_seeded_outer_type(&id.stx.name) {
            final_ty = seeded;
          }
        }
      }
      if self.check_var_assignments {
        if let (Some(ann), Some(init)) = (annot_ty, declarator.initializer.as_ref()) {
          // TypeScript anchors assignment diagnostics for variable initializers
          // on the binding name/pattern (e.g. `const x: T = ...` points at `x`,
          // `const [x]: T = ...` points at `[x]`).
          self.check_assignable(
            init,
            init_ty,
            ann,
            Some(self.binding_name_range(&declarator.pattern.stx.pat)),
          );
        }
      }
      if matches!(decl.stx.mode, VarDeclMode::Var) {
        // tsc keeps the first declarator's type for the binding and for TS2403
        // (`'r4' was also declared here`). Capture before `check_pat` overwrites.
        let first_tys = self.capture_established_var_declared_tys(&declarator.pattern.stx.pat);
        self.report_subsequent_var_type_mismatch(&declarator.pattern.stx.pat, final_ty);
        self.check_pat(&declarator.pattern.stx.pat, final_ty);
        self.restore_established_var_declared_tys(first_tys);
        self.mark_established_var_bindings(&declarator.pattern.stx.pat);
      } else {
        self.check_pat(&declarator.pattern.stx.pat, final_ty);
      }
    }
  }

  /// Capture first-declarator types for names already established in this body.
  fn capture_established_var_declared_tys(&self, pat: &Node<AstPat>) -> Vec<(String, TypeId)> {
    let mut out = Vec::new();
    self.collect_established_var_declared_tys(pat, &mut out);
    out
  }

  fn collect_established_var_declared_tys(
    &self,
    pat: &Node<AstPat>,
    out: &mut Vec<(String, TypeId)>,
  ) {
    match pat.stx.as_ref() {
      AstPat::Id(id) => {
        if self.established_var_bindings.contains(&id.stx.name) {
          if let Some(existing) = self.lookup(&id.stx.name) {
            out.push((id.stx.name.clone(), existing.declared_ty));
          }
        }
      }
      AstPat::Arr(arr) => {
        for elem in arr.stx.elements.iter().flatten() {
          self.collect_established_var_declared_tys(&elem.target, out);
        }
        if let Some(rest) = &arr.stx.rest {
          self.collect_established_var_declared_tys(rest, out);
        }
      }
      AstPat::Obj(obj) => {
        for prop in obj.stx.properties.iter() {
          self.collect_established_var_declared_tys(&prop.stx.target, out);
        }
        if let Some(rest) = &obj.stx.rest {
          self.collect_established_var_declared_tys(rest, out);
        }
      }
      AstPat::AssignTarget(_) => {}
    }
  }

  fn restore_established_var_declared_tys(&mut self, first_tys: Vec<(String, TypeId)>) {
    for (name, declared_ty) in first_tys {
      for scope in self.scopes.iter_mut().rev() {
        if let Some(binding) = scope.bindings.get_mut(&name) {
          binding.declared_ty = declared_ty;
          binding.ty = declared_ty;
          break;
        }
      }
    }
  }

  /// TS2403 when a later `var` merges with an earlier binding of a different type.
  ///
  /// Only fires when this body check already established the name via a prior
  /// declarator — binder/pre-seed types alone must not produce a false first
  /// TS2403 (e.g. annotated `var a9a: {}` seeded before `var a9a = …`).
  ///
  /// Compares against the first declarator's `declared_ty` (not the latest flow
  /// type): tsc reports every later mismatch against the original declaration.
  fn report_subsequent_var_type_mismatch(&mut self, pat: &Node<AstPat>, next_ty: TypeId) {
    match pat.stx.as_ref() {
      AstPat::Id(id) => {
        if !self.established_var_bindings.contains(&id.stx.name) {
          return;
        }
        let Some(existing) = self.lookup(&id.stx.name) else {
          return;
        };
        let prev = self.store.canon(existing.declared_ty);
        let next = self.store.canon(next_ty);
        if prev == next {
          return;
        }
        // tsc compares with `isTypeIdenticalTo` (structural identity): a class
        // instance and a structurally equal object type are "the same type"
        // (`AmbientModuleAndAmbientWithSameNameAndCommonRoot`). Approximate:
        // mutual assignability, except when either side is `any` (tsc
        // identity treats `any` strictly — `any` is only identical to `any`,
        // so `var a: any; var a: string` still fires).
        let prim = self.store.primitive_ids();
        let structural_identical = prev != prim.any
          && next != prim.any
          && self.relate.is_assignable(prev, next)
          && self.relate.is_assignable(next, prev);
        if structural_identical {
          return;
        }
        self.diagnostics.push(codes::SUBSEQUENT_VARIABLE_DECLARATIONS.error(
          format!(
            "Subsequent variable declarations must have the same type.  Variable '{}' must be of type '{}', but here has type '{}'.",
            id.stx.name,
            TypeDisplay::new(self.store.as_ref(), prev),
            TypeDisplay::new(self.store.as_ref(), next),
          ),
          Span::new(self.file, loc_to_range(self.file, id.loc)),
        ));
      }
      AstPat::Arr(arr) => {
        for elem in arr.stx.elements.iter().flatten() {
          self.report_subsequent_var_type_mismatch(&elem.target, next_ty);
        }
        if let Some(rest) = &arr.stx.rest {
          self.report_subsequent_var_type_mismatch(rest, next_ty);
        }
      }
      AstPat::Obj(obj) => {
        for prop in obj.stx.properties.iter() {
          self.report_subsequent_var_type_mismatch(&prop.stx.target, next_ty);
        }
        if let Some(rest) = &obj.stx.rest {
          self.report_subsequent_var_type_mismatch(rest, next_ty);
        }
      }
      AstPat::AssignTarget(_) => {}
    }
  }

  fn mark_established_var_bindings(&mut self, pat: &Node<AstPat>) {
    match pat.stx.as_ref() {
      AstPat::Id(id) => {
        self.established_var_bindings.insert(id.stx.name.clone());
      }
      AstPat::Arr(arr) => {
        for elem in arr.stx.elements.iter().flatten() {
          self.mark_established_var_bindings(&elem.target);
        }
        if let Some(rest) = &arr.stx.rest {
          self.mark_established_var_bindings(rest);
        }
      }
      AstPat::Obj(obj) => {
        for prop in obj.stx.properties.iter() {
          self.mark_established_var_bindings(&prop.stx.target);
        }
        if let Some(rest) = &obj.stx.rest {
          self.mark_established_var_bindings(rest);
        }
      }
      AstPat::AssignTarget(_) => {}
    }
  }

  /// Seed `var` pattern names before initializer checking (function-scoped hoist).
  ///
  /// Returns whether any new provisional binding was inserted (used to suppress
  /// false TS2403 when the real declarator type overwrites the seed).
  fn seed_hoisted_var_pat(&mut self, pat: &Node<AstPat>, ty: TypeId) -> bool {
    match pat.stx.as_ref() {
      AstPat::Id(id) => {
        if self.lookup(&id.stx.name).is_none() {
          self.insert_binding(id.stx.name.clone(), ty, Vec::new());
          true
        } else {
          false
        }
      }
      AstPat::Arr(arr) => {
        let mut seeded = false;
        for elem in arr.stx.elements.iter().flatten() {
          seeded |= self.seed_hoisted_var_pat(&elem.target, ty);
        }
        if let Some(rest) = &arr.stx.rest {
          seeded |= self.seed_hoisted_var_pat(rest, ty);
        }
        seeded
      }
      AstPat::Obj(obj) => {
        let mut seeded = false;
        for prop in obj.stx.properties.iter() {
          seeded |= self.seed_hoisted_var_pat(&prop.stx.target, ty);
        }
        if let Some(rest) = &obj.stx.rest {
          seeded |= self.seed_hoisted_var_pat(rest, ty);
        }
        seeded
      }
      AstPat::AssignTarget(_) => false,
    }
  }

  /// Lower a JSDoc type string with file typedefs and in-scope type params.
  pub(crate) fn lower_jsdoc_ty(&self, raw: &str) -> TypeId {
    let tp_map = self.lowerer.type_param_map();
    let typedefs = (!self.jsdoc_typedefs.is_empty()).then_some(&self.jsdoc_typedefs);
    let type_params = (!tp_map.is_empty()).then_some(&tp_map);
    let env = crate::jsdoc::JsdocLowerEnv::new()
      .with_resolver(self.type_resolver.as_deref())
      .with_typedefs(typedefs)
      .with_type_params(type_params);
    crate::jsdoc::lower_jsdoc_type_with(&self.store, raw, &env)
  }

  /// Emit TS2694 when a JSDoc type is an unresolved dotted namepath.
  pub(crate) fn report_unresolved_jsdoc_qualified(
    &mut self,
    source: &str,
    decl_offset: u32,
    raw: &str,
  ) {
    let qualified = {
      let tp_map = self.lowerer.type_param_map();
      let typedefs = (!self.jsdoc_typedefs.is_empty()).then_some(&self.jsdoc_typedefs);
      let type_params = (!tp_map.is_empty()).then_some(&tp_map);
      let env = crate::jsdoc::JsdocLowerEnv::new()
        .with_resolver(self.type_resolver.as_deref())
        .with_typedefs(typedefs)
        .with_type_params(type_params);
      crate::jsdoc::unresolved_jsdoc_qualified_name(raw, &env).map(str::to_owned)
    };
    let Some(qualified) = qualified else {
      return;
    };
    let Some((start, end)) =
      crate::jsdoc::leading_type_tag_member_range(source, decl_offset, &qualified)
    else {
      return;
    };
    let member = qualified.rsplit('.').next().unwrap_or(&qualified);
    let namespace = qualified
      .strip_suffix(member)
      .and_then(|s| s.strip_suffix('.'))
      .unwrap_or(&qualified);
    self
      .diagnostics
      .push(codes::NAMESPACE_NO_EXPORTED_MEMBER.error(
        codes::namespace_no_exported_member_message(namespace, member),
        Span {
          file: self.file,
          range: TextRange::new(start, end),
        },
      ));
  }

  /// Lower a leading JSDoc `@type {…}` for `loc` when checkJs source is available.
  pub(crate) fn jsdoc_declared_type(&mut self, loc: parse_js::loc::Loc) -> Option<TypeId> {
    let source = self.jsdoc_source?;
    let offset = loc_to_range(self.file, loc).start;
    let tag = crate::jsdoc::leading_type_tag(source, offset)?;
    self.report_unresolved_jsdoc_qualified(source, offset, tag);
    Some(self.lower_jsdoc_ty(tag))
  }

  /// Owned leading `@type {…}` string for a function (decl / expr / arrow).
  pub(crate) fn jsdoc_type_tag_owned(&self, func: &Node<Func>) -> Option<String> {
    self
      .jsdoc_tags_for_function(func)?
      .type_tag
      .map(str::to_owned)
  }

  /// First callable signature from a leading JSDoc `@type` on `func`, if any.
  pub(crate) fn jsdoc_type_signature(&self, func: &Node<Func>) -> Option<Signature> {
    let raw = self.jsdoc_type_tag_owned(func)?;
    let ty = self.lower_jsdoc_ty(&raw);
    match self.store.type_kind(ty) {
      TypeKind::Callable { overloads } => overloads
        .first()
        .map(|sig_id| self.store.signature(*sig_id)),
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        shape
          .call_signatures
          .first()
          .map(|sig_id| self.store.signature(*sig_id))
      }
      _ => None,
    }
  }

  /// Leading JSDoc tags for a function: comment before `function`/`=>`, or
  /// (for function/arrow initializers) the enclosing `var`/`let`/`const` decl.
  pub(crate) fn jsdoc_tags_for_function(
    &self,
    func: &Node<Func>,
  ) -> Option<crate::jsdoc::JsdocTags<'_>> {
    let source = self.jsdoc_source?;
    // Prefer the indexed `jsdoc_loc` (FunctionDecl starts at `function`; bare
    // `Func.loc` for decls starts at the parameter list).
    let offset = self
      .index
      .functions
      .iter()
      .find(|info| std::ptr::eq(info.func, func))
      .map(|info| loc_to_range(self.file, info.jsdoc_loc).start)
      .unwrap_or_else(|| loc_to_range(self.file, func.loc).start);
    if let Some(tags) = crate::jsdoc::leading_jsdoc_tags(source, offset) {
      if tags.has_callable_tags() {
        return Some(tags);
      }
    }
    // Fallback: `/** @param/@returns */ var f = function…` / `const f = () => …`
    for info in self.index.vars.values() {
      let Some(init) = info.initializer else {
        continue;
      };
      let init_func = match init.stx.as_ref() {
        AstExpr::Func(f) => &f.stx.func,
        AstExpr::ArrowFunc(f) => &f.stx.func,
        _ => continue,
      };
      if !std::ptr::eq(init_func, func) {
        continue;
      }
      let offset = loc_to_range(self.file, info.decl_loc).start;
      let tags = crate::jsdoc::leading_jsdoc_tags(source, offset)?;
      if tags.has_callable_tags() {
        return Some(tags);
      }
      break;
    }
    None
  }

  /// Resolved `@param` types keyed by root parameter name (folds nested
  /// `opts.x` / `name.prop` sugar). When `report_errors` is true, emits
  /// TS8032 for unqualified nests and TS8024 for unmatched root names
  /// (call from `bind_params` only to avoid duplicates with signature synthesis).
  pub(crate) fn jsdoc_resolved_param_types(
    &mut self,
    func: &Node<Func>,
    report_errors: bool,
  ) -> std::collections::HashMap<String, crate::jsdoc::ResolvedJsdocParam> {
    let Some(tags) = self.jsdoc_tags_for_function(func) else {
      return std::collections::HashMap::new();
    };
    if tags.params.is_empty() {
      return std::collections::HashMap::new();
    }
    let owned: Vec<crate::jsdoc::OwnedJsdocParam> = tags
      .params
      .iter()
      .map(|p| crate::jsdoc::OwnedJsdocParam {
        ty: p.ty.to_owned(),
        name: p.name.map(str::to_owned),
        optional: p.optional,
      })
      .collect();
    let jsdoc_offset = self
      .index
      .functions
      .iter()
      .find(|info| std::ptr::eq(info.func, func))
      .map(|info| loc_to_range(self.file, info.jsdoc_loc).start)
      .unwrap_or_else(|| loc_to_range(self.file, func.loc).start);
    // Prefer statement-level offset for `var f = function…` so TS8024/TS8032
    // spans land in the leading comment (same as `jsdoc_tags_for_function`).
    let jsdoc_offset = self
      .index
      .vars
      .values()
      .find(|info| {
        let Some(init) = info.initializer else {
          return false;
        };
        let init_func = match init.stx.as_ref() {
          AstExpr::Func(f) => &f.stx.func,
          AstExpr::ArrowFunc(f) => &f.stx.func,
          _ => return false,
        };
        std::ptr::eq(init_func, func)
      })
      .map(|info| loc_to_range(self.file, info.decl_loc).start)
      .unwrap_or(jsdoc_offset);
    let (resolved, nested_errors) = {
      let tp_map = self.lowerer.type_param_map();
      let typedefs = (!self.jsdoc_typedefs.is_empty()).then_some(&self.jsdoc_typedefs);
      let type_params = (!tp_map.is_empty()).then_some(&tp_map);
      let env = crate::jsdoc::JsdocLowerEnv::new()
        .with_resolver(self.type_resolver.as_deref())
        .with_typedefs(typedefs)
        .with_type_params(type_params);
      crate::jsdoc::resolve_jsdoc_params(&self.store, &owned, &env)
    };
    if report_errors {
      if let Some(source) = self.jsdoc_source {
        for err in nested_errors {
          let Some((start, end)) =
            crate::jsdoc::leading_param_name_range(source, jsdoc_offset, &err.qualified_name)
          else {
            continue;
          };
          self
            .diagnostics
            .push(codes::JSDOC_QUALIFIED_PARAM_MISSING_PARENT.error(
              codes::jsdoc_qualified_param_missing_parent_message(
                &err.qualified_name,
                &err.parent_path,
              ),
              Span {
                file: self.file,
                range: TextRange::new(start, end),
              },
            ));
        }
        let fn_param_names: Vec<Option<&str>> = func
          .stx
          .parameters
          .iter()
          .map(|p| match p.stx.pattern.stx.pat.stx.as_ref() {
            AstPat::Id(id) => Some(id.stx.name.as_str()),
            _ => None,
          })
          .collect();
        let unmatched = crate::jsdoc::find_unmatched_root_jsdoc_params(&owned, &fn_param_names);
        for err in unmatched {
          let Some((start, end)) =
            crate::jsdoc::leading_param_name_range(source, jsdoc_offset, &err.name)
          else {
            continue;
          };
          self.diagnostics.push(codes::JSDOC_PARAM_TAG_UNUSED.error(
            codes::jsdoc_param_tag_unused_message(&err.name),
            Span {
              file: self.file,
              range: TextRange::new(start, end),
            },
          ));
        }
      }
    }
    resolved
  }

  /// Owned `@returns` type string, if present.
  pub(crate) fn jsdoc_returns_owned(&self, func: &Node<Func>) -> Option<String> {
    self
      .jsdoc_tags_for_function(func)?
      .returns
      .map(|s| s.to_string())
  }

  /// Lower `@returns {…}` for `func` when checkJs source is available.
  pub(crate) fn jsdoc_returns_type(&self, func: &Node<Func>) -> Option<TypeId> {
    let raw = self.jsdoc_returns_owned(func)?;
    Some(self.lower_jsdoc_ty(&raw))
  }

  /// Lower `@this {…}` for `func` when checkJs source is available (tsc
  /// `inferThis.ts`: an explicit `@this` tag wins over the class-derived
  /// `this` type inside the method body).
  pub(crate) fn jsdoc_this_type(&self, func: &Node<Func>) -> Option<TypeId> {
    let raw = self.jsdoc_tags_for_function(func)?.this_type?;
    Some(self.lower_jsdoc_ty(raw))
  }

  /// Owned `@template` entries for `func`, if present.
  pub(crate) fn jsdoc_templates_owned(
    &self,
    func: &Node<Func>,
  ) -> Option<Vec<crate::jsdoc::OwnedJsdocTemplate>> {
    let tags = self.jsdoc_tags_for_function(func)?;
    if tags.templates.is_empty() {
      return None;
    }
    Some(
      tags
        .templates
        .iter()
        .map(|t| crate::jsdoc::OwnedJsdocTemplate {
          name: t.name.to_owned(),
          constraint: t.constraint.map(str::to_owned),
        })
        .collect(),
    )
  }

  /// Register JSDoc `@template` names into the current type-param scope.
  pub(crate) fn register_jsdoc_templates(
    &mut self,
    templates: &[crate::jsdoc::OwnedJsdocTemplate],
  ) -> Vec<TypeParamDecl> {
    // Two-pass: allocate names first so constraints may reference siblings.
    let mut decls = Vec::with_capacity(templates.len());
    for t in templates {
      decls.push(self.lowerer.register_jsdoc_type_param(t.name.clone(), None));
    }
    for (decl, t) in decls.iter_mut().zip(templates.iter()) {
      if let Some(raw) = t.constraint.as_deref() {
        decl.constraint = Some(self.lower_jsdoc_ty(raw));
      }
    }
    decls
  }

  pub(crate) fn lookup_typeof_query_binding(
    &self,
    ty: &Node<parse_js::ast::type_expr::TypeExpr>,
  ) -> Option<TypeId> {
    let parse_js::ast::type_expr::TypeExpr::TypeQuery(query) = ty.stx.as_ref() else {
      return None;
    };
    match &query.stx.expr_name {
      parse_js::ast::type_expr::TypeEntityName::Identifier(name) => {
        self.lookup(name.as_str()).map(|binding| binding.ty)
      }
      _ => None,
    }
  }

  pub(crate) fn check_using_initializer(
    &mut self,
    init: &Node<AstExpr>,
    init_ty: TypeId,
    required: &str,
  ) {
    let prim = self.store.primitive_ids();
    if matches!(
      self.store.type_kind(init_ty),
      TypeKind::Any | TypeKind::Unknown
    ) {
      return;
    }
    let Some(resolver) = self.type_resolver.as_ref() else {
      return;
    };
    let Some(def) = resolver.resolve_type_name(&[required.to_string()]) else {
      return;
    };
    let required_ty = self.store.intern_type(TypeKind::Ref {
      def,
      args: Vec::new(),
    });
    // `using`/`await using` declarations ignore nullish values at runtime.
    let required_ty = self
      .store
      .union(vec![required_ty, prim.null, prim.undefined]);
    if self.relate.is_assignable(init_ty, required_ty) {
      return;
    }
    let mut range = loc_to_range(self.file, init.loc);
    if let AstExpr::Unary(unary) = init.stx.as_ref() {
      if matches!(unary.stx.operator, OperatorName::New) {
        let arg_end = unary.stx.argument.loc.end_u32();
        range.end = range.end.min(arg_end);
      }
    }
    self
      .diagnostics
      .push(codes::INVALID_USING_INITIALIZER.error(
        format!("initializer must be assignable to `{required}`"),
        Span::new(self.file, range),
      ));
  }

  pub(crate) fn check_namespace(&mut self, ns: &Node<NamespaceDecl>) {
    pub(crate) fn namespace_key(path: &[String]) -> String {
      path.join(".")
    }

    pub(crate) fn check_ns(
      checker: &mut Checker<'_>,
      ns: &Node<NamespaceDecl>,
      path: &mut Vec<String>,
    ) {
      let name = ns.stx.name.clone();
      path.push(name.clone());
      let key = namespace_key(path);

      let mut scope = checker.namespace_scopes.remove(&key).unwrap_or_default();
      if let Some(binding) = checker.lookup(&name) {
        scope.bindings.insert(name.clone(), binding);
      }
      let established = checker
        .namespace_established_vars
        .remove(&key)
        .unwrap_or_default();
      let outer_established = std::mem::replace(&mut checker.established_var_bindings, established);

      checker.scopes.push(scope);
      match &ns.stx.body {
        NamespaceBody::Block(stmts) => checker.check_stmt_list(stmts),
        NamespaceBody::Namespace(inner) => check_ns(checker, inner, path),
      }
      let scope = checker.scopes.pop().unwrap_or_default();
      let established = std::mem::replace(&mut checker.established_var_bindings, outer_established);
      checker.namespace_scopes.insert(key.clone(), scope);
      checker.namespace_established_vars.insert(key, established);
      path.pop();
    }

    let mut path = Vec::new();
    check_ns(self, ns, &mut path);
  }

  pub(crate) fn check_pat(&mut self, pat: &Node<AstPat>, value_ty: TypeId) {
    self.bind_pattern(pat, value_ty);
  }

  pub(crate) fn bind_pattern(&mut self, pat: &Node<AstPat>, value: TypeId) {
    self.bind_pattern_with_type_params(pat, value, Vec::new());
  }

  pub(crate) fn bind_pattern_with_type_params(
    &mut self,
    pat: &Node<AstPat>,
    value: TypeId,
    type_params: Vec<TypeParamDecl>,
  ) {
    self.record_pat_type(pat.loc, value);
    match pat.stx.as_ref() {
      AstPat::Id(id) => {
        // Destructuring *assignment* to an existing binding: check the value
        // against the declared type and narrow the flow type — the declared
        // type is never replaced by the pattern value's type
        // (`assignmentTypeNarrowing.ts`).
        if self.destructuring_assignment {
          if let Some(existing) = self.lookup(&id.stx.name) {
            let declared = existing.declared_ty;
            if !self.is_assignable_for_check(value, declared) {
              let code = self.assignability_mismatch_code(value, declared, &codes::TYPE_MISMATCH);
              self.diagnostics.push(code.error(
                "assignment type mismatch",
                Span {
                  file: self.file,
                  range: loc_to_range(self.file, id.loc),
                },
              ));
            }
            let _ = self.update_binding_ty(&id.stx.name, value);
            return;
          }
        }
        self.insert_binding(id.stx.name.clone(), value, type_params);
      }
      AstPat::Arr(arr) => self.bind_array_pattern(arr, value, type_params),
      AstPat::Obj(obj) => self.bind_object_pattern(obj, value, type_params),
      AstPat::AssignTarget(expr) => {
        // Definite write target (destructuring / for-of LHS). Do not treat a
        // top-level private member as a read (TS2806); nested object reads still
        // go through `check_expr` inside `check_assign_target_expr`.
        let target_ty = self.check_assign_target_expr(expr);
        if !self.relate.is_assignable(value, target_ty) {
          let code = self.assignability_mismatch_code(value, target_ty, &codes::TYPE_MISMATCH);
          self.diagnostics.push(code.error(
            "assignment type mismatch",
            Span {
              file: self.file,
              range: loc_to_range(self.file, pat.loc),
            },
          ));
        }
      }
    }
  }

  pub(crate) fn bind_array_pattern(
    &mut self,
    arr: &Node<ArrPat>,
    value: TypeId,
    type_params: Vec<TypeParamDecl>,
  ) {
    let prim = self.store.primitive_ids();
    let element_ty = match self.store.type_kind(value) {
      TypeKind::Array { ty, .. } => ty,
      TypeKind::Tuple(elems) => elems.first().map(|e| e.ty).unwrap_or(prim.unknown),
      TypeKind::Any => prim.any,
      // Non-array object types use the iterable protocol
      // (`[a, ...b] = new FooIterator` — `iterableArrayPattern4.ts`).
      _ => self.for_of_element_type(value),
    };
    for (idx, elem) in arr.stx.elements.iter().enumerate() {
      if let Some(elem) = elem {
        let mut target_ty = match self.store.type_kind(value) {
          TypeKind::Tuple(elems) => elems.get(idx).map(|e| e.ty).unwrap_or(element_ty),
          _ => element_ty,
        };
        if let Some(default) = &elem.default_value {
          let default_ty = self.check_expr(default);
          // Destructuring defaults replace a missing/`undefined` slot with the
          // default's type (tsc): `union(unknown, T)` would absorb to
          // `unknown` and poison the target check — never the default.
          let (non_nullish, _) = narrow_non_nullish(target_ty, &self.store);
          let effective = if non_nullish == prim.unknown {
            default_ty
          } else {
            non_nullish
          };
          target_ty = self.store.union(vec![effective, default_ty]);
        }
        self.bind_pattern(&elem.target, target_ty);
      }
    }
    if let Some(rest) = &arr.stx.rest {
      let rest_ty = match self.store.type_kind(value) {
        TypeKind::Array { ty, readonly } => {
          self.store.intern_type(TypeKind::Array { ty, readonly })
        }
        TypeKind::Any => self.store.intern_type(TypeKind::Array {
          ty: prim.any,
          readonly: false,
        }),
        TypeKind::Tuple(elems) => {
          // Rest of a tuple stays positional when the remaining elements are
          // all required: `[...[a, b = 0]] = ["", 1]` binds the inner array
          // pattern against the tuple `[string, number]`, not the union
          // `string | number` (`restElementWithAssignmentPattern1.ts`).
          let consumed = arr.stx.elements.len();
          let tail: Vec<types_ts_interned::TupleElem> = elems.into_iter().skip(consumed).collect();
          let all_required = tail.iter().all(|e| !e.optional && !e.rest);
          if !tail.is_empty() && all_required {
            self.store.intern_type(TypeKind::Tuple(tail))
          } else {
            let tys: Vec<TypeId> = tail.into_iter().map(|e| e.ty).collect();
            let elem_ty = if tys.is_empty() {
              prim.unknown
            } else {
              self.store.union(tys)
            };
            self.store.intern_type(TypeKind::Array {
              ty: elem_ty,
              readonly: false,
            })
          }
        }
        _ => {
          // Non-array object sources use the iterable protocol for the rest
          // (`[...b] = new FooIterator` → `Foo[]` — `iterableArrayPattern4.ts`).
          self.store.intern_type(TypeKind::Array {
            ty: self.for_of_element_type(value),
            readonly: false,
          })
        }
      };
      self.bind_pattern_with_type_params(rest, rest_ty, type_params.clone());
    }
  }

  pub(crate) fn bind_object_pattern(
    &mut self,
    obj: &Node<ObjPat>,
    value: TypeId,
    type_params: Vec<TypeParamDecl>,
  ) {
    let prim = self.store.primitive_ids();
    let value_is_any = matches!(self.store.type_kind(value), TypeKind::Any);
    for prop in obj.stx.properties.iter() {
      let mut prop_ty = if value_is_any { prim.any } else { prim.unknown };
      if !value_is_any {
        if let ClassOrObjKey::Direct(direct) = &prop.stx.key {
          prop_ty = self.member_type(value, &direct.stx.key);
        }
      }
      if let Some(default) = &prop.stx.default_value {
        let default_ty = self.check_expr(default);
        // Destructuring defaults replace a missing/`undefined` prop with the
        // default's type (tsc): `union(unknown, T)` would absorb to `unknown`
        // and poison the target check — never the default.
        let (non_nullish, _) = narrow_non_nullish(prop_ty, &self.store);
        let effective = if non_nullish == prim.unknown {
          default_ty
        } else {
          non_nullish
        };
        prop_ty = self.store.union(vec![effective, default_ty]);
      }
      self.bind_pattern(&prop.stx.target, prop_ty);
    }
    if let Some(rest) = &obj.stx.rest {
      // Object rest/spread never copies private identifiers (tsc getRestType /
      // spread of class values). Binding `rest` to the full class type would
      // incorrectly allow `rest.#prop`. Build a non-nominal public-only shape
      // (and omit explicitly destructured keys).
      let omitted: Vec<String> = obj
        .stx
        .properties
        .iter()
        .filter_map(|prop| match &prop.stx.key {
          ClassOrObjKey::Direct(direct) => Some(direct.stx.key.clone()),
          ClassOrObjKey::Computed(_) => None,
        })
        .collect();
      let rest_ty = self.object_rest_binding_type(value, &omitted);
      self.bind_pattern_with_type_params(rest, rest_ty, type_params);
    }
  }

  /// Merge enumerable own properties from an object-spread source into `shape`.
  ///
  /// Later members (including subsequent spreads / explicit props) overwrite
  /// earlier keys. Private `#` names are skipped (same as object rest).
  pub(crate) fn append_object_spread_properties(&mut self, shape: &mut Shape, source: TypeId) {
    let source = self.expand_ref(source);
    match self.store.type_kind(source) {
      TypeKind::Object(obj_id) => {
        let src_shape = self.store.shape(self.store.object(obj_id).shape);
        for prop in src_shape.properties.iter() {
          let is_private = match &prop.key {
            PropKey::String(n) | PropKey::Symbol(n) => self.store.name(*n).starts_with('#'),
            PropKey::Number(_) => false,
          };
          if is_private {
            continue;
          }
          let mut data = prop.data.clone();
          // Spread yields a fresh structural object — drop class brand metadata.
          data.origin = None;
          data.accessibility = None;
          upsert_shape_property(
            shape,
            types_ts_interned::Property {
              key: prop.key.clone(),
              data,
            },
          );
        }
      }
      TypeKind::Intersection(members) => {
        for member in members {
          self.append_object_spread_properties(shape, member);
        }
      }
      TypeKind::Union(members) => {
        // Approximate: properties present on *any* constituent, optional when
        // not on all (enough for common spread assignability).
        if members.is_empty() {
          return;
        }
        let mut merged: Vec<(PropKey, PropData, usize)> = Vec::new();
        let n = members.len();
        for member in members.iter().copied() {
          let mut part = Shape::new();
          self.append_object_spread_properties(&mut part, member);
          for prop in part.properties {
            if let Some((_, data, count)) = merged.iter_mut().find(|(k, _, _)| *k == prop.key) {
              *count += 1;
              data.ty = self.store.union(vec![data.ty, prop.data.ty]);
              data.optional = data.optional || prop.data.optional;
            } else {
              merged.push((prop.key, prop.data, 1));
            }
          }
        }
        for (key, mut data, count) in merged {
          if count < n {
            data.optional = true;
          }
          upsert_shape_property(shape, types_ts_interned::Property { key, data });
        }
      }
      // `any`/`unknown` spreads do not add known named props (indexers omitted).
      _ => {
        // Class / other refs: reuse rest-binding's public-field projection.
        let projected = self.object_rest_binding_type(source, &[]);
        if !matches!(
          self.store.type_kind(projected),
          TypeKind::EmptyObject | TypeKind::Any | TypeKind::Unknown
        ) {
          self.append_object_spread_properties(shape, projected);
        }
      }
    }
  }

  /// Type of `...rest` in an object binding pattern.
  ///
  /// Matches tsc: private `#` members are dropped, explicitly bound keys are
  /// omitted, and the result is a fresh structural object (no class nominal
  /// identity — so `rest.#x` is TS2339, not a same-class private access).
  pub(crate) fn object_rest_binding_type(&mut self, value: TypeId, omitted: &[String]) -> TypeId {
    let prim = self.store.primitive_ids();
    let value = self.expand_ref(value);
    match self.store.type_kind(value) {
      TypeKind::Any => prim.any,
      TypeKind::Unknown => prim.unknown,
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        let mut out = Shape::new();
        for prop in shape.properties.iter() {
          let name = match &prop.key {
            PropKey::String(n) | PropKey::Symbol(n) => self.store.name(*n).to_string(),
            PropKey::Number(_) => continue,
          };
          if name.starts_with('#') || omitted.iter().any(|o| o == &name) {
            continue;
          }
          // Drop construct/call signatures by copying properties only; also
          // strip class-origin metadata so the rest type is not nominal.
          let mut data = prop.data.clone();
          data.origin = None;
          data.accessibility = None;
          out.properties.push(types_ts_interned::Property {
            key: prop.key.clone(),
            data,
          });
        }
        if out.properties.is_empty() {
          return self.store.intern_type(TypeKind::EmptyObject);
        }
        let shape_id = self.store.intern_shape(out);
        let obj = self.store.intern_object(ObjectType { shape: shape_id });
        self.store.intern_type(TypeKind::Object(obj))
      }
      TypeKind::Union(members) => {
        let parts: Vec<_> = members
          .into_iter()
          .map(|m| self.object_rest_binding_type(m, omitted))
          .collect();
        self.store.union(parts)
      }
      TypeKind::Intersection(members) => {
        let parts: Vec<_> = members
          .into_iter()
          .map(|m| self.object_rest_binding_type(m, omitted))
          .collect();
        self.store.intersection(parts)
      }
      _ => {
        // Nominal class refs / other kinds: public fields only via ClassInfo,
        // else empty object (private access must fail).
        if let Some(idx) = self.nominal_class_index_for_type(value) {
          let ty_canon = self.store.canon(value);
          let is_static = self
            .resolve_static_this_type(idx)
            .is_some_and(|st| self.store.canon(st) == ty_canon)
            || self
              .index
              .classes
              .get(idx)
              .and_then(|c| c.name.as_ref())
              .and_then(|name| self.lookup(name))
              .is_some_and(|b| self.store.canon(b.ty) == ty_canon);
          let fields: Vec<(String, bool, Option<&Node<TypeExpr>>)> = if is_static {
            self
              .index
              .classes
              .get(idx)
              .map(|c| {
                c.static_fields
                  .iter()
                  .filter(|f| !f.name.starts_with('#') && !omitted.iter().any(|o| o == &f.name))
                  .map(|f| (f.name.clone(), f.optional, f.type_annotation))
                  .collect()
              })
              .unwrap_or_default()
          } else {
            self
              .index
              .classes
              .get(idx)
              .map(|c| {
                c.instance_fields
                  .iter()
                  .filter(|f| !f.name.starts_with('#') && !omitted.iter().any(|o| o == &f.name))
                  .map(|f| (f.name.clone(), f.optional, f.type_annotation))
                  .collect()
              })
              .unwrap_or_default()
          };
          if fields.is_empty() && !is_static {
            return self.store.intern_type(TypeKind::EmptyObject);
          }
          // Static side: tsc keeps `prototype` on typeof-class rest; approximate
          // with public static fields only (enough for private-name TS2339).
          return self.synthesize_fields_shape(&fields, &[], &[], None);
        }
        self.store.intern_type(TypeKind::EmptyObject)
      }
    }
  }
}

/// Result of path-sensitive `this.prop = …` analysis in a constructor body.
struct SpiCtorAnalysis {
  /// Intersection of assigned sets at every exit (return / fall-through).
  /// `None` if the body has no reachable exit (e.g. always throws) — treat as
  /// fully assigned vacuously by leaving required props unchecked via empty
  /// intersection semantics at the call site (`unwrap_or(seed)`).
  exit_assigned: Option<HashSet<String>>,
}

#[derive(Clone)]
struct SpiPath {
  assigned: HashSet<String>,
  /// Whether this path still reaches subsequent statements.
  completes: bool,
}

fn spi_analyze_stmts(stmts: &[Node<Stmt>], seed: &HashSet<String>) -> SpiCtorAnalysis {
  let mut path = SpiPath {
    assigned: seed.clone(),
    completes: true,
  };
  let mut exit_assigned: Option<HashSet<String>> = None;
  spi_walk_stmts(stmts, &mut path, &mut exit_assigned);
  if path.completes {
    spi_record_exit(&mut exit_assigned, &path.assigned);
  }
  SpiCtorAnalysis { exit_assigned }
}

fn spi_record_exit(exit: &mut Option<HashSet<String>>, assigned: &HashSet<String>) {
  match exit {
    None => *exit = Some(assigned.clone()),
    Some(existing) => {
      *existing = existing.intersection(assigned).cloned().collect();
    }
  }
}

fn spi_walk_stmts(
  stmts: &[Node<Stmt>],
  path: &mut SpiPath,
  exit_assigned: &mut Option<HashSet<String>>,
) {
  for stmt in stmts {
    if !path.completes {
      break;
    }
    spi_walk_stmt(stmt, path, exit_assigned);
  }
}

fn spi_walk_stmt(
  stmt: &Node<Stmt>,
  path: &mut SpiPath,
  exit_assigned: &mut Option<HashSet<String>>,
) {
  match stmt.stx.as_ref() {
    Stmt::Return(_) | Stmt::Throw(_) => {
      spi_record_exit(exit_assigned, &path.assigned);
      path.completes = false;
    }
    Stmt::Block(block) => spi_walk_stmts(&block.stx.body, path, exit_assigned),
    Stmt::If(if_stmt) => {
      let mut then_path = path.clone();
      spi_walk_stmt(&if_stmt.stx.consequent, &mut then_path, exit_assigned);
      let mut else_path = path.clone();
      if let Some(alt) = &if_stmt.stx.alternate {
        spi_walk_stmt(alt, &mut else_path, exit_assigned);
      }
      match (then_path.completes, else_path.completes) {
        (false, false) => {
          path.completes = false;
        }
        (true, false) => {
          path.assigned = then_path.assigned;
        }
        (false, true) => {
          path.assigned = else_path.assigned;
        }
        (true, true) => {
          path.assigned = then_path
            .assigned
            .intersection(&else_path.assigned)
            .cloned()
            .collect();
        }
      }
    }
    Stmt::Expr(expr_stmt) => {
      spi_note_assignments_in_expr(&expr_stmt.stx.expr, &mut path.assigned);
    }
    // Nested functions do not contribute definite assignment (tsc flow).
    Stmt::FunctionDecl(_) => {}
    Stmt::Label(label) => spi_walk_stmt(&label.stx.statement, path, exit_assigned),
    Stmt::Try(tr) => {
      // Conservative: only count assignments that occur in try and (if present)
      // also on the catch completion path when catch exists; finally always runs
      // but we union its assignments after.
      let mut try_path = path.clone();
      spi_walk_stmts(&tr.stx.wrapped.stx.body, &mut try_path, exit_assigned);
      if let Some(catch) = &tr.stx.catch {
        let mut catch_path = path.clone();
        spi_walk_stmts(&catch.stx.body, &mut catch_path, exit_assigned);
        match (try_path.completes, catch_path.completes) {
          (false, false) => path.completes = false,
          (true, false) => path.assigned = try_path.assigned,
          (false, true) => path.assigned = catch_path.assigned,
          (true, true) => {
            path.assigned = try_path
              .assigned
              .intersection(&catch_path.assigned)
              .cloned()
              .collect();
          }
        }
      } else {
        *path = try_path;
      }
      if let Some(finally) = &tr.stx.finally {
        if path.completes {
          spi_walk_stmts(&finally.stx.body, path, exit_assigned);
        }
      }
    }
    // Loops: ignore body assignments for definite assignment (may not run).
    Stmt::While(_) | Stmt::DoWhile(_) | Stmt::ForTriple(_) | Stmt::ForIn(_) | Stmt::ForOf(_) => {}
    Stmt::Switch(_) => {
      // Conservative: do not count switch-case assignments as definite.
    }
    Stmt::VarDecl(decl) => {
      for d in decl.stx.declarators.iter() {
        if let Some(init) = &d.initializer {
          spi_note_assignments_in_expr(init, &mut path.assigned);
        }
      }
    }
    _ => {}
  }
}

fn spi_note_assignments_in_expr(expr: &Node<AstExpr>, assigned: &mut HashSet<String>) {
  match expr.stx.as_ref() {
    AstExpr::Binary(bin) if bin.stx.operator.is_assignment() => {
      // Evaluate RHS first (reads), then record the write.
      spi_note_assignments_in_expr(&bin.stx.right, assigned);
      if let AstExpr::Member(mem) = bin.stx.left.stx.as_ref() {
        if matches!(mem.stx.left.stx.as_ref(), AstExpr::This(_)) {
          assigned.insert(mem.stx.right.clone());
        }
      } else {
        spi_note_assignments_in_expr(&bin.stx.left, assigned);
      }
    }
    AstExpr::Binary(bin) => {
      spi_note_assignments_in_expr(&bin.stx.left, assigned);
      spi_note_assignments_in_expr(&bin.stx.right, assigned);
    }
    AstExpr::Unary(un) => spi_note_assignments_in_expr(&un.stx.argument, assigned),
    AstExpr::Cond(cond) => {
      spi_note_assignments_in_expr(&cond.stx.test, assigned);
      // Conservative: only count assignments common to both arms.
      let mut then_set = assigned.clone();
      let mut else_set = assigned.clone();
      spi_note_assignments_in_expr(&cond.stx.consequent, &mut then_set);
      spi_note_assignments_in_expr(&cond.stx.alternate, &mut else_set);
      *assigned = then_set.intersection(&else_set).cloned().collect();
    }
    AstExpr::Call(call) => {
      spi_note_assignments_in_expr(&call.stx.callee, assigned);
      for arg in call.stx.arguments.iter() {
        spi_note_assignments_in_expr(&arg.stx.value, assigned);
      }
    }
    AstExpr::Member(mem) => spi_note_assignments_in_expr(&mem.stx.left, assigned),
    AstExpr::ComputedMember(mem) => {
      spi_note_assignments_in_expr(&mem.stx.object, assigned);
      spi_note_assignments_in_expr(&mem.stx.member, assigned);
    }
    // Nested function expressions do not contribute.
    AstExpr::Func(_) | AstExpr::ArrowFunc(_) | AstExpr::Class(_) => {}
    _ => {}
  }
}

/// `super(...);` as an expression statement (tsc `getSuperCallFromStatement`).
fn stmt_is_super_call(stmt: &Node<Stmt>) -> bool {
  match stmt.stx.as_ref() {
    Stmt::Expr(expr_stmt) => expr_is_super_call(&expr_stmt.stx.expr),
    _ => false,
  }
}

fn expr_is_super_call(expr: &Node<AstExpr>) -> bool {
  matches!(
    expr.stx.as_ref(),
    AstExpr::Call(call) if matches!(call.stx.callee.stx.as_ref(), AstExpr::Super(_))
  )
}

/// First `this` expression lexically before a nested function/class boundary.
fn first_this_before_super_in_stmt(file: FileId, stmt: &Node<Stmt>) -> Option<TextRange> {
  match stmt.stx.as_ref() {
    Stmt::Expr(expr_stmt) => first_this_in_expr(file, &expr_stmt.stx.expr),
    Stmt::Return(ret) => ret
      .stx
      .value
      .as_ref()
      .and_then(|v| first_this_in_expr(file, v)),
    Stmt::Throw(th) => first_this_in_expr(file, &th.stx.value),
    Stmt::Block(block) => {
      for child in block.stx.body.iter() {
        if let Some(r) = first_this_before_super_in_stmt(file, child) {
          return Some(r);
        }
      }
      None
    }
    Stmt::If(if_stmt) => first_this_in_expr(file, &if_stmt.stx.test)
      .or_else(|| first_this_before_super_in_stmt(file, &if_stmt.stx.consequent))
      .or_else(|| {
        if_stmt
          .stx
          .alternate
          .as_ref()
          .and_then(|alt| first_this_before_super_in_stmt(file, alt))
      }),
    Stmt::VarDecl(decl) => {
      for declarator in decl.stx.declarators.iter() {
        if let Some(init) = declarator.initializer.as_ref() {
          if let Some(r) = first_this_in_expr(file, init) {
            return Some(r);
          }
        }
      }
      None
    }
    // Nested functions / classes do not contribute (tsc skips them).
    Stmt::FunctionDecl(_) | Stmt::ClassDecl(_) => None,
    _ => None,
  }
}

fn first_this_in_expr(file: FileId, expr: &Node<AstExpr>) -> Option<TextRange> {
  match expr.stx.as_ref() {
    AstExpr::This(_) => Some(loc_to_range(file, expr.loc)),
    AstExpr::Unary(un) => first_this_in_expr(file, &un.stx.argument),
    AstExpr::Binary(bin) => {
      first_this_in_expr(file, &bin.stx.left).or_else(|| first_this_in_expr(file, &bin.stx.right))
    }
    AstExpr::Cond(cond) => first_this_in_expr(file, &cond.stx.test)
      .or_else(|| first_this_in_expr(file, &cond.stx.consequent))
      .or_else(|| first_this_in_expr(file, &cond.stx.alternate)),
    AstExpr::Call(call) => first_this_in_expr(file, &call.stx.callee).or_else(|| {
      for arg in call.stx.arguments.iter() {
        if let Some(r) = first_this_in_expr(file, &arg.stx.value) {
          return Some(r);
        }
      }
      None
    }),
    AstExpr::Member(mem) => first_this_in_expr(file, &mem.stx.left),
    AstExpr::ComputedMember(mem) => first_this_in_expr(file, &mem.stx.object)
      .or_else(|| first_this_in_expr(file, &mem.stx.member)),
    AstExpr::LitArr(arr) => {
      use parse_js::ast::expr::lit::LitArrElem;
      for elem in arr.stx.elements.iter() {
        if let LitArrElem::Single(v) = elem {
          if let Some(r) = first_this_in_expr(file, v) {
            return Some(r);
          }
        }
      }
      None
    }
    AstExpr::LitObj(obj) => {
      use parse_js::ast::class_or_object::{ClassOrObjVal, ObjMemberType};
      for member in obj.stx.members.iter() {
        match &member.stx.typ {
          ObjMemberType::Valued { val, .. } => match val {
            ClassOrObjVal::Prop(Some(init)) => {
              if let Some(r) = first_this_in_expr(file, init) {
                return Some(r);
              }
            }
            ClassOrObjVal::Prop(None)
            | ClassOrObjVal::Method(_)
            | ClassOrObjVal::Getter(_)
            | ClassOrObjVal::Setter(_)
            | ClassOrObjVal::IndexSignature(_)
            | ClassOrObjVal::StaticBlock(_) => {}
          },
          ObjMemberType::Shorthand { .. } => {}
          ObjMemberType::Rest { val } => {
            if let Some(r) = first_this_in_expr(file, val) {
              return Some(r);
            }
          }
        }
      }
      None
    }
    // Nested functions / class expressions do not contribute.
    AstExpr::Func(_) | AstExpr::ArrowFunc(_) | AstExpr::Class(_) => None,
    AstExpr::TypeAssertion(assert) => first_this_in_expr(file, &assert.stx.expression),
    AstExpr::NonNullAssertion(assert) => first_this_in_expr(file, &assert.stx.expression),
    AstExpr::SatisfiesExpr(sat) => first_this_in_expr(file, &sat.stx.expression),
    AstExpr::Instantiation(inst) => first_this_in_expr(file, &inst.stx.expression),
    _ => None,
  }
}

pub(crate) fn upsert_shape_property(shape: &mut Shape, prop: types_ts_interned::Property) {
  if let Some(existing) = shape.properties.iter_mut().find(|p| p.key == prop.key) {
    *existing = prop;
  } else {
    shape.properties.push(prop);
  }
}
