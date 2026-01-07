use super::*;

impl ProgramState {
  pub(in super::super) fn build_type_resolver(
    &self,
    binding_defs: &HashMap<String, DefId>,
  ) -> Option<Arc<dyn TypeResolver>> {
    if let Some(semantics) = self.semantics.as_ref() {
      let def_kinds = Arc::new(
        self
          .def_data
          .iter()
          .map(|(id, data)| (*id, data.kind.clone()))
          .collect(),
      );
      let def_files = Arc::new(
        self
          .def_data
          .iter()
          .map(|(id, data)| (*id, data.file))
          .collect(),
      );
      let def_spans = Arc::new(
        self
          .def_data
          .iter()
          .map(|(id, data)| (*id, data.span))
          .collect(),
      );
      let exports = Arc::new(
        self
          .files
          .iter()
          .map(|(file, state)| (*file, state.exports.clone()))
          .collect(),
      );
      let current_file = self.current_file.unwrap_or(FileId(u32::MAX));
      let namespace_members = self
        .namespace_member_index
        .clone()
        .unwrap_or_else(|| Arc::new(NamespaceMemberIndex::default()));
      return Some(Arc::new(ProgramTypeResolver::new(
        Arc::clone(&self.host),
        Arc::clone(semantics),
        def_kinds,
        def_files,
        def_spans,
        Arc::new(self.file_registry.clone()),
        current_file,
        binding_defs.clone(),
        exports,
        Arc::new(self.module_namespace_defs.clone()),
        namespace_members,
        Arc::clone(&self.qualified_def_members),
      )) as Arc<_>);
    }
    if binding_defs.is_empty() {
      return None;
    }
    Some(Arc::new(check::hir_body::BindingTypeResolver::new(
      binding_defs.clone(),
    )) as Arc<_>)
  }

  pub(super) fn function_expr_span(&self, body_id: BodyId) -> Option<TextRange> {
    let mut visited = HashSet::new();
    let mut current = self.body_parents.get(&body_id).copied();
    while let Some(parent) = current {
      if !visited.insert(parent) {
        break;
      }
      let Some(meta) = self.body_map.get(&parent) else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(hir_body_id) = meta.hir else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(lowered) = self.hir_lowered.get(&meta.file) else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(parent_body) = lowered.body(hir_body_id) else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      for expr in parent_body.exprs.iter() {
        if let HirExprKind::FunctionExpr { body, .. } = expr.kind {
          if body == body_id {
            return Some(expr.span);
          }
        }
      }
      current = self.body_parents.get(&parent).copied();
    }
    None
  }

  pub(super) fn contextual_callable_for_body(
    &mut self,
    body_id: BodyId,
    func_span: TextRange,
    store: &Arc<tti::TypeStore>,
  ) -> Result<Option<TypeId>, FatalError> {
    let mut visited = HashSet::new();
    let mut current = self.body_parents.get(&body_id).copied();
    while let Some(parent) = current {
      if !visited.insert(parent) {
        break;
      }
      let parent_result = self.check_body(parent)?;
      for (idx, span) in parent_result.expr_spans.iter().enumerate() {
        if *span != func_span {
          continue;
        }
        if let Some(ty) = parent_result.expr_types.get(idx).copied() {
          if store.contains_type_id(ty)
            && matches!(store.type_kind(ty), tti::TypeKind::Callable { .. })
          {
            return Ok(Some(ty));
          }
        }
      }
      current = self.body_parents.get(&parent).copied();
    }
    Ok(None)
  }

}
