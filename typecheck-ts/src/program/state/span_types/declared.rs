use super::*;
use crate::class_typing::hir_class_member_type_at_span;
use crate::program::check::decls::{HirDeclLowerer, LocalDefIndex};
use parse_js::ast::type_expr::TypeParameter;

impl ProgramState {
  pub(in super::super) fn type_from_type_expr(&mut self, expr: &Node<TypeExpr>) -> TypeId {
    let Some(file) = self.current_file else {
      return self.store.primitive_ids().unknown;
    };
    self.lower_type_expr_in_file(file, None, expr)
  }

  /// Lower [`hir_js::DefData::declared_type`] for a definition when present.
  ///
  /// Value-side annotations (class fields, module/ambient vars) store their
  /// annotations here rather than on `VarData.typ`; `type_of_def` and related
  /// paths consult this before any residual binder AST lowering.
  pub(in super::super) fn hir_declared_type_for_def(&mut self, def: DefId) -> Option<TypeId> {
    let file = self.def_data.get(&def)?.file;
    let lowered = self.hir_lowered.get(&file)?.clone();
    let hir_def = lowered.def(def)?;
    let type_expr = hir_def.declared_type?;
    Some(self.lower_hir_declared_type(file, &lowered, hir_def.id, type_expr))
  }

  fn hir_declared_type_for_span(&mut self, file: FileId, target: TextRange) -> Option<TypeId> {
    let lowered = self.hir_lowered.get(&file)?.clone();
    let mut candidates: Vec<_> = lowered
      .defs
      .iter()
      .filter(|def| def.span == target && def.declared_type.is_some())
      .collect();
    candidates.sort_by_key(|def| def.id.0);
    if let Some(hir_def) = candidates.first() {
      let type_expr = hir_def.declared_type?;
      return Some(self.lower_hir_declared_type(file, &lowered, hir_def.id, type_expr));
    }

    // Ambient class properties / constructor parameter properties: annotation
    // lives on `DefTypeInfo::Class` `ClassMemberSig` (class arenas), not on a
    // per-field `DefData.declared_type`.
    let (owner, type_expr) = hir_class_member_type_at_span(&lowered, target)?;
    Some(self.lower_hir_declared_type(file, &lowered, owner, type_expr))
  }

  fn lower_hir_declared_type(
    &mut self,
    file: FileId,
    lowered: &hir_js::LowerResult,
    owner: hir_js::DefId,
    type_expr: hir_js::TypeExprId,
  ) -> TypeId {
    let store = Arc::clone(&self.store);
    let mut diagnostics = Vec::new();
    let local_defs = LocalDefIndex::from_lowered(lowered);
    let mut binding_defs = HashMap::new();
    if let Some(state) = self.files.get(&file) {
      for (name, binding) in state.bindings.iter() {
        if let Some(def) = binding.def {
          binding_defs.insert(name.clone(), def);
        }
      }
    }
    let prev_file = self.current_file;
    self.current_file = Some(file);
    let program_resolver = self.build_type_resolver(&binding_defs);
    let resolve_name = |path: &[String]| -> Option<DefId> {
      program_resolver
        .as_ref()
        .and_then(|r| r.resolve_type_name(path))
    };
    let mut lowerer = HirDeclLowerer::new(
      store,
      &lowered.types,
      self.semantics.as_deref(),
      HashMap::new(),
      file,
      self.file_key_for_id(file),
      local_defs,
      &mut diagnostics,
      None,
      None,
      None,
      None,
      Some(&self.module_namespace_defs),
      Some(&self.value_defs),
    )
    .with_type_name_resolver(&resolve_name);
    // Class fields own their annotation arenas but class-`T` lives on the
    // enclosing class def — seed those params so `#foo: T` is not TC2008.
    let enclosing_class = crate::class_typing::enclosing_class_type_params(lowered, owner);
    let ty = match enclosing_class.as_ref() {
      Some((class_id, params)) => lowerer.lower_declared_type_with_class_params(
        owner,
        type_expr,
        Some((*class_id, params.as_slice())),
        &lowered.names,
      ),
      None => lowerer.lower_declared_type(owner, type_expr, &lowered.names),
    };
    self.current_file = prev_file;
    if self.semantics.is_some() {
      self.diagnostics.extend(diagnostics);
    }
    ty
  }

  pub(in super::super) fn declared_type_for_span(
    &mut self,
    file: FileId,
    target: TextRange,
  ) -> Option<TypeId> {
    // HIR-only: class fields / ambient+param-prop via ClassMemberSig; module and
    // ambient vars via DefData.declared_type. No AST statement walk.
    self.hir_declared_type_for_span(file, target)
  }

  fn lower_type_expr_in_file(
    &mut self,
    file: FileId,
    type_params: Option<&[Node<TypeParameter>]>,
    expr: &Node<TypeExpr>,
  ) -> TypeId {
    let store = Arc::clone(&self.store);
    let has_semantics = self.semantics.is_some();

    let prev_file = self.current_file;
    self.current_file = Some(file);

    let mut lowerer = TypeLowerer::new(Arc::clone(&store));
    lowerer.set_file(file);
    if has_semantics {
      let mut binding_defs = HashMap::new();
      if let Some(state) = self.files.get(&file) {
        for (name, binding) in state.bindings.iter() {
          if let Some(def) = binding.def {
            binding_defs.insert(name.clone(), def);
          }
        }
      }
      let resolver = self.build_type_resolver(&binding_defs);
      lowerer.set_resolver(resolver);
    } else {
      // During the initial binding pass we do not have `semantic-js` program
      // semantics yet, which means name resolution for type references (including
      // global library declarations) is incomplete.
      //
      // We still want to preserve simple annotation shapes like `string` so that
      // functions and variables with primitive annotations produce useful
      // signatures before the full program semantics are available. Lower the
      // expression without a resolver, but if lowering produced diagnostics (e.g.
      // due to an unresolved type reference) discard the result and fall back to
      // `unknown` to avoid emitting spurious diagnostics.
      lowerer.set_resolver(None);
    }
    if let Some(params) = type_params {
      lowerer.register_type_params(params);
    }
    let ty = store.canon(lowerer.lower_type_expr(expr));
    let diagnostics = lowerer.take_diagnostics();
    if has_semantics {
      self.diagnostics.extend(diagnostics);
    } else if !diagnostics.is_empty() {
      self.current_file = prev_file;
      return store.primitive_ids().unknown;
    }

    self.current_file = prev_file;
    ty
  }

  /// Recompute a type-alias body from HIR when the binder left `unknown`.
  pub(in super::super) fn type_alias_type_for_span(
    &mut self,
    file: FileId,
    target: TextRange,
    name: &str,
  ) -> Option<TypeId> {
    let lowered = self.hir_lowered.get(&file)?.clone();
    let mut candidates: Vec<_> = lowered
      .defs
      .iter()
      .filter(|def| {
        matches!(
          def.type_info.as_ref(),
          Some(hir_js::DefTypeInfo::TypeAlias { .. })
        ) && (def.span == target || lowered.names.resolve(def.name) == Some(name))
      })
      .collect();
    candidates.sort_by_key(|def| def.id.0);
    let hir_def = candidates.first()?;
    let info = hir_def.type_info.as_ref()?;
    let store = Arc::clone(&self.store);
    let mut diagnostics = Vec::new();
    let local_defs = LocalDefIndex::from_lowered(&lowered);
    let mut binding_defs = HashMap::new();
    if let Some(state) = self.files.get(&file) {
      for (name, binding) in state.bindings.iter() {
        if let Some(def) = binding.def {
          binding_defs.insert(name.clone(), def);
        }
      }
    }
    let prev_file = self.current_file;
    self.current_file = Some(file);
    let program_resolver = self.build_type_resolver(&binding_defs);
    let resolve_name = |path: &[String]| -> Option<DefId> {
      program_resolver
        .as_ref()
        .and_then(|r| r.resolve_type_name(path))
    };
    let mut lowerer = HirDeclLowerer::new(
      store,
      &lowered.types,
      self.semantics.as_deref(),
      HashMap::new(),
      file,
      self.file_key_for_id(file),
      local_defs,
      &mut diagnostics,
      None,
      None,
      None,
      None,
      Some(&self.module_namespace_defs),
      Some(&self.value_defs),
    )
    .with_type_name_resolver(&resolve_name);
    let (ty, _) = lowerer.lower_type_info(hir_def.id, info, &lowered.names);
    self.current_file = prev_file;
    if self.semantics.is_some() {
      self.diagnostics.extend(diagnostics);
    }
    Some(ty)
  }
}
