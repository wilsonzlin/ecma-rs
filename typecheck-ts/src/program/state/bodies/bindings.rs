use super::*;

impl ProgramState {
  pub(super) fn collect_parent_bindings(
    &mut self,
    body_id: BodyId,
    bindings: &mut HashMap<String, TypeId>,
    binding_defs: &mut HashMap<String, DefId>,
  ) -> Result<(), FatalError> {
    self.check_cancelled()?;
    let store = Arc::clone(&self.store);
    let unknown = store.primitive_ids().unknown;
    fn record_pat(
      state: &mut ProgramState,
      pat_id: HirPatId,
      body: &hir_js::Body,
      names: &hir_js::NameInterner,
      result: &BodyCheckResult,
      bindings: &mut HashMap<String, TypeId>,
      binding_defs: &mut HashMap<String, DefId>,
      file: FileId,
      store: &Arc<tti::TypeStore>,
      unknown: TypeId,
      seen: &mut HashSet<String>,
    ) {
      let Some(pat) = body.pats.get(pat_id.0 as usize) else {
        return;
      };
      let mut ty = result.pat_type(PatId(pat_id.0)).unwrap_or(unknown);
      if !store.contains_type_id(ty) {
        ty = store.primitive_ids().unknown;
      }
      match &pat.kind {
        HirPatKind::Ident(name_id) => {
          if let Some(name) = names.resolve(*name_id) {
            let name = name.to_string();
            if !seen.insert(name.clone()) {
              return;
            }

            let def_id = state
              .def_data
              .iter()
              .filter_map(|(id, data)| {
                if data.file != file || data.name != name {
                  return None;
                }
                if matches!(data.kind, DefKind::VarDeclarator(_)) {
                  return None;
                }
                if data.span == pat.span {
                  return Some((0_u8, data.span.len(), data.span.start, data.span.end, *id));
                }
                if data.span.start <= pat.span.start && data.span.end >= pat.span.end {
                  return Some((1_u8, data.span.len(), data.span.start, data.span.end, *id));
                }
                None
              })
              .min_by_key(|key| *key)
              .map(|(_, _, _, _, id)| id);

            if let Some(def_id) = def_id {
              binding_defs.insert(name.clone(), def_id);
            }

            // If this binding has an explicit type annotation, prefer the declared
            // type over the (possibly literal-inferred) pattern type from the parent
            // body. This matches TypeScript's behavior for e.g.
            // `const x: string = ""` where `x` should be `string`, not `""`.
            let should_prefer_declared = matches!(
              store.type_kind(ty),
              tti::TypeKind::Unknown
                | tti::TypeKind::StringLiteral(_)
                | tti::TypeKind::NumberLiteral(_)
                | tti::TypeKind::BooleanLiteral(_)
                | tti::TypeKind::BigIntLiteral(_)
            );
            if should_prefer_declared {
              let declared = state.declared_type_for_span(file, pat.span);
              if let Some(declared) = declared {
                if store.contains_type_id(declared) {
                  ty = store.canon(declared);
                }
              }
            }
            let replace = match bindings.get(&name) {
              None => true,
              Some(existing) => {
                if !store.contains_type_id(*existing)
                  || matches!(store.type_kind(*existing), tti::TypeKind::Unknown)
                {
                  true
                } else {
                  matches!(
                    (store.type_kind(*existing), store.type_kind(ty)),
                    (tti::TypeKind::StringLiteral(_), tti::TypeKind::String)
                      | (tti::TypeKind::NumberLiteral(_), tti::TypeKind::Number)
                      | (tti::TypeKind::BooleanLiteral(_), tti::TypeKind::Boolean)
                      | (tti::TypeKind::BigIntLiteral(_), tti::TypeKind::BigInt)
                  )
                }
              }
            };
            if replace {
              bindings.insert(name, ty);
            }
          }
        }
        HirPatKind::Array(arr) => {
          for elem in arr.elements.iter().flatten() {
            record_pat(
              state,
              elem.pat,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
              store,
              unknown,
              seen,
            );
          }
          if let Some(rest) = arr.rest {
            record_pat(
              state,
              rest,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
              store,
              unknown,
              seen,
            );
          }
        }
        HirPatKind::Object(obj) => {
          for prop in obj.props.iter() {
            record_pat(
              state,
              prop.value,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
              store,
              unknown,
              seen,
            );
          }
          if let Some(rest) = obj.rest {
            record_pat(
              state,
              rest,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
              store,
              unknown,
              seen,
            );
          }
        }
        HirPatKind::Rest(inner) => {
          record_pat(
            state,
            **inner,
            body,
            names,
            result,
            bindings,
            binding_defs,
            file,
            store,
            unknown,
            seen,
          );
        }
        HirPatKind::Assign { target, .. } => {
          record_pat(
            state,
            *target,
            body,
            names,
            result,
            bindings,
            binding_defs,
            file,
            store,
            unknown,
            seen,
          );
        }
        HirPatKind::AssignTarget(_) => {}
      }
    }

    let mut visited = HashSet::new();
    let mut seen_names = HashSet::new();
    let mut current = self.body_parents.get(&body_id).copied();
    if let Some(meta) = self.body_map.get(&body_id).copied() {
      if matches!(meta.kind, HirBodyKind::Initializer) {
        if let (Some(hir_id), Some(lowered)) = (meta.hir, self.hir_lowered.get(&meta.file)) {
          if let Some(hir_body) = lowered.body(hir_id) {
            if let Some(owner_def) = lowered.def(hir_body.owner) {
              if let Some(parent_def) = owner_def.parent {
                if let Some(parent_body) = lowered.def(parent_def).and_then(|def| def.body) {
                  if parent_body != body_id {
                    self.body_parents.insert(body_id, parent_body);
                    current = Some(parent_body);
                  }
                }
              }
            }
          }
        }
      }
    }
    while let Some(parent) = current {
      self.check_cancelled()?;
      if !visited.insert(parent) {
        break;
      }
      let Some(meta) = self.body_map.get(&parent).copied() else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      if matches!(meta.kind, HirBodyKind::TopLevel)
        && self.files.get(&meta.file).and_then(|state| state.top_body) == Some(parent)
      {
        break;
      }
      let parent_result = self.check_body(parent)?;
      let Some(hir_body_id) = meta.hir else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(lowered) = self.hir_lowered.get(&meta.file).cloned() else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(body) = lowered.body(hir_body_id) else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      for pat in body.pats.iter().enumerate() {
        record_pat(
          self,
          HirPatId(pat.0 as u32),
          body,
          &lowered.names,
          &parent_result,
          bindings,
          binding_defs,
          meta.file,
          &store,
          unknown,
          &mut seen_names,
        );
      }
      if parent_result.pat_types.is_empty() && matches!(meta.kind, HirBodyKind::Function) {
        // If we're checking a nested body while the parent is still being checked, `check_body`
        // returns an empty result to break cycles. Seed parameter bindings directly from the
        // owning function's annotations so initializer bodies can still resolve captured params.
        if let Some(owner) = self.owner_of_body(parent) {
          if let Some(DefData {
            kind: DefKind::Function(func),
            ..
          }) = self.def_data.get(&owner)
          {
            for param in func.params.iter() {
              if param.name.starts_with("<pattern") {
                continue;
              }
              let mapped = param
                .typ
                .filter(|ty| store.contains_type_id(*ty))
                .map(|ty| store.canon(ty))
                .unwrap_or_else(|| store.primitive_ids().unknown);
              bindings
                .entry(param.name.clone())
                .and_modify(|existing| {
                  let existing_unknown = !store.contains_type_id(*existing)
                    || matches!(store.type_kind(*existing), tti::TypeKind::Unknown);
                  if existing_unknown {
                    *existing = mapped;
                  }
                })
                .or_insert(mapped);
            }
          }
        }
      }
      current = self.body_parents.get(&parent).copied();
    }
    Ok(())
  }
}
