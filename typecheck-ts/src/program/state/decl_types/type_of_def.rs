use super::*;

impl ProgramState {
  pub(in super::super) fn type_of_def(&mut self, def: DefId) -> Result<TypeId, FatalError> {
    self.check_cancelled()?;
    let store = Arc::clone(&self.store);
    let prim = store.primitive_ids();

    let cache_hit = self.interned_def_types.contains_key(&def);
    let mut span = QuerySpan::enter(
      QueryKind::TypeOfDef,
      query_span!(
        "typecheck_ts.type_of_def",
        self.def_data.get(&def).map(|d| d.file.0),
        Some(def.0),
        self.body_of_def(def).map(|b| b.0),
        cache_hit
      ),
      self.interned_def_types.get(&def).copied(),
      cache_hit,
      Some(self.query_stats.clone()),
    );

    let def_data = match self.def_data.get(&def).cloned() {
      Some(data) => data,
      None => {
        if let Some(span) = span.take() {
          span.finish(Some(prim.unknown));
        }
        return Ok(prim.unknown);
      }
    };

    let synthetic_value_def = matches!(def_data.kind, DefKind::Var(_))
      && self.value_defs.values().any(|value_def| *value_def == def);

    if matches!(def_data.kind, DefKind::Interface(_)) {
      self.merge_interface_symbol_types(def)?;
    }

    if let Some(existing) = self.interned_def_types.get(&def).copied() {
      let skip_cache = matches!(def_data.kind, DefKind::Var(_)) && !synthetic_value_def;
      let mut ty = if store.contains_type_id(existing) {
        store.canon(existing)
      } else {
        prim.unknown
      };

      if matches!(store.type_kind(ty), tti::TypeKind::Unknown) || skip_cache {
        self.interned_def_types.remove(&def);
      } else {
        if let DefKind::Function(func) = &def_data.kind {
          if !self.function_has_return_annotation(def, func)
            && func.body.is_some()
            && callable_return_is_unknown(&store, ty)
          {
            let has_overloads = self.def_data.iter().any(|(other, data)| {
              *other != def
                && data.symbol == def_data.symbol
                && matches!(data.kind, DefKind::Function(_))
            });
            if !has_overloads {
              let old_ty = ty;
              let (callable_ty, intersection_members, callable_index) = match store.type_kind(ty) {
                tti::TypeKind::Callable { .. } => (ty, None, None),
                tti::TypeKind::Intersection(members) => {
                  let prim = store.primitive_ids();
                  let idx = members
                    .iter()
                    .position(|member| match store.type_kind(*member) {
                      tti::TypeKind::Callable { overloads } => overloads
                        .iter()
                        .any(|sig_id| store.signature(*sig_id).ret == prim.unknown),
                      _ => false,
                    });
                  if let Some(idx) = idx {
                    (members[idx], Some(members.clone()), Some(idx))
                  } else {
                    (ty, None, None)
                  }
                }
                _ => (ty, None, None),
              };

              if intersection_members.is_some()
                || matches!(store.type_kind(callable_ty), tti::TypeKind::Callable { .. })
              {
                if let Some(updated_callable) =
                  self.infer_cached_callable_return_type(func, &store, callable_ty)?
                {
                  let updated_ty = if let (Some(mut members), Some(idx)) =
                    (intersection_members, callable_index)
                  {
                    members[idx] = updated_callable;
                    store.intersection(members)
                  } else {
                    updated_callable
                  };

                  let update_binding = |state: &mut ProgramState, def: DefId, ty: TypeId| {
                    state.interned_def_types.insert(def, ty);
                    if let Some(def_data) = state.def_data.get(&def) {
                      if let Some(file_state) = state.files.get_mut(&def_data.file) {
                        if let Some(binding) = file_state.bindings.get_mut(&def_data.name) {
                          if binding.def == Some(def) {
                            binding.type_id = Some(ty);
                          }
                        }
                      }
                    }
                  };

                  let mut defs_to_update = vec![def];
                  for (other, data) in self.def_data.iter() {
                    if *other == def {
                      continue;
                    }
                    if data.file != def_data.file
                      || data.name != def_data.name
                      || !matches!(data.kind, DefKind::Namespace(_) | DefKind::Module(_))
                    {
                      continue;
                    }
                    let Some(existing) = self.interned_def_types.get(other).copied() else {
                      continue;
                    };
                    if store.contains_type_id(existing) && store.canon(existing) == old_ty {
                      defs_to_update.push(*other);
                    }
                  }
                  defs_to_update.sort_by_key(|id| id.0);
                  defs_to_update.dedup();
                  for def in defs_to_update {
                    update_binding(self, def, updated_ty);
                  }

                  ty = updated_ty;
                }
              }
            }
          }
        }

        if let Some(span) = span.take() {
          span.finish(Some(ty));
        }
        return Ok(ty);
      }
    }

    let prev_file = self.current_file;
    self.current_file = Some(def_data.file);

    if self.type_stack.contains(&def) {
      // Match tsc `reportCircularityError`: under `--noImplicitAny`, unannotated
      // bindings referenced in their own initializer become `any` + TS7022.
      // Report on the re-entered def and the waiter currently resolving (stack
      // top) so mutual cycles (`#foo`/`#bar`) get both diagnostics.
      self.report_circular_initializer_implicit_any(def);
      if let Some(waiter) = self.type_stack.last().copied() {
        if waiter != def {
          self.report_circular_initializer_implicit_any(waiter);
        }
      }
      // Return `any` to the re-entrant caller, but do NOT insert it into
      // `interned_def_types`: for genuine self-cycles the outer completion
      // computes and lands the same `any`, while for re-entrant lookups during
      // an in-flight resolution (e.g. `import Alias = N.x` resolving `N.x`
      // while `x`'s initializer is being checked) the insert would poison the
      // completion's replace check and stick `any` on a def whose real type is
      // about to land.
      let ty = prim.any;
      if let Some(span) = span.take() {
        span.finish(Some(ty));
      }
      self.current_file = prev_file;
      return Ok(ty);
    }

    let ns_ty = self
      .namespace_object_types
      .get(&(def_data.file, def_data.name.clone()))
      .copied();

    self.type_stack.push(def);
    let result = (|| -> Result<TypeId, FatalError> {
      self.check_cancelled()?;
      let ty = match def_data.kind.clone() {
        DefKind::Function(func) => self.function_type(def, func)?,
        DefKind::Var(var) => {
          // Body-local params/vars are LocalId-only (no DefKind::Param /
          // body-local DefKind::Var). Their types live in body check side
          // tables / `type_of_local` / `type_at`, not type_of_def.
          // This arm covers module-level and namespace/module member vars.

          fn pat_for_span(state: &ProgramState, body_id: BodyId, span: TextRange) -> Option<PatId> {
            let meta = state.body_map.get(&body_id)?;
            let hir_id = meta.hir?;
            let lowered = state.hir_lowered.get(&meta.file)?;
            let body = lowered.body(hir_id)?;
            body
              .pats
              .iter()
              .enumerate()
              .find_map(|(idx, pat)| (pat.span == span).then_some(PatId(idx as u32)))
          }

          let mode_decl_kind = match var.mode {
            VarDeclMode::Var => HirVarDeclKind::Var,
            VarDeclMode::Let => HirVarDeclKind::Let,
            VarDeclMode::Const => HirVarDeclKind::Const,
            VarDeclMode::Using => HirVarDeclKind::Using,
            VarDeclMode::AwaitUsing => HirVarDeclKind::AwaitUsing,
          };

          let init = self.var_initializer(def).or_else(|| {
            if var.body == MISSING_BODY {
              return None;
            }
            let expr = var.init?;
            Some(VarInit {
              body: var.body,
              expr,
              decl_kind: mode_decl_kind,
              pat: pat_for_span(self, var.body, def_data.span),
              span: Some(def_data.span),
            })
          });

          let decl_kind = init
            .as_ref()
            .map(|init| init.decl_kind)
            .unwrap_or(mode_decl_kind);

          let const_like = matches!(
            decl_kind,
            HirVarDeclKind::Const | HirVarDeclKind::Using | HirVarDeclKind::AwaitUsing
          );

          let mut init_span_for_const = None;
          let mut init_pat_is_root = true;

          // Prefer HIR `DefData.declared_type` (class fields) when the DefId is
          // known; fall back to span-based AST/HIR lookup, then `VarData.typ`.
          let declared_ann = self
            .hir_declared_type_for_def(def)
            .or_else(|| self.declared_type_for_span(def_data.file, def_data.span));
          let annotated_raw = declared_ann.or(var.typ);
          let annotated = match annotated_raw {
            Some(ty) => Some(self.resolve_value_ref_type(ty)?),
            None => None,
          };

          let mut skip_implicit_any = false;
          let mut inferred = if let Some(t) = annotated {
            t
          } else if let Some(init) = init {
            if self
              .checking_bodies
              .lock()
              .unwrap_or_else(|err| err.into_inner())
              .contains(&init.body)
            {
              skip_implicit_any = true;
              prim.unknown
            } else {
              if !self.snapshot_loaded {
                self.local_body_results.remove(&init.body);
              }
              let res = self.check_body(init.body)?;
              init_span_for_const = res.expr_span(init.expr);

              init_pat_is_root = init
                .pat
                .map(|pat| {
                  let meta = match self.body_map.get(&init.body) {
                    Some(meta) => meta,
                    None => return false,
                  };
                  let hir_id = match meta.hir {
                    Some(id) => id,
                    None => return false,
                  };
                  let lowered = match self.hir_lowered.get(&meta.file) {
                    Some(lowered) => lowered,
                    None => return false,
                  };
                  let hir_body = match lowered.body(hir_id) {
                    Some(body) => body,
                    None => return false,
                  };
                  for stmt in hir_body.stmts.iter() {
                    if let hir_js::StmtKind::Var(decl) = &stmt.kind {
                      for declarator in decl.declarators.iter() {
                        if declarator.init == Some(init.expr) {
                          return declarator.pat == pat;
                        }
                      }
                    }
                  }
                  false
                })
                .unwrap_or(true);

              let init_ty_from_pat = init
                .pat
                .and_then(|pat| res.pat_type(pat))
                .filter(|ty| !matches!(store.type_kind(store.canon(*ty)), tti::TypeKind::Unknown));

              let init_ty = init_ty_from_pat.or_else(|| res.expr_type(init.expr));
              if let Some(init_ty) = init_ty {
                let init_ty = self.resolve_value_ref_type(init_ty)?;
                store.canon(init_ty)
              } else {
                prim.unknown
              }
            }
          } else if let Some(ns_ty) = ns_ty {
            ns_ty
          } else {
            prim.unknown
          };

          if const_like && init_pat_is_root {
            if let Some(init_span) = init_span_for_const {
              if let Some(file_body) = self.files.get(&def_data.file).and_then(|f| f.top_body) {
                if let Some(res) = self.local_body_results.get(&file_body).cloned() {
                  let top_ty = res
                    .expr_spans()
                    .iter()
                    .enumerate()
                    .find(|(_, span)| **span == init_span)
                    .and_then(|(idx, _)| res.expr_type(ExprId(idx as u32)));

                  if let Some(top_ty) = top_ty {
                    let has_readonly = match store.type_kind(top_ty) {
                      tti::TypeKind::Object(obj) => {
                        let shape = store.shape(store.object(obj).shape);
                        shape.properties.iter().any(|p| p.data.readonly)
                      }
                      tti::TypeKind::Tuple(elems) => elems.iter().any(|e| e.readonly),
                      _ => false,
                    };

                    if has_readonly {
                      inferred = store.canon(top_ty);
                    }
                  }
                }
              }
            }
          }

          if self.compiler_options.no_implicit_any
            && !skip_implicit_any
            && annotated.is_none()
            && matches!(
              store.type_kind(store.canon(inferred)),
              tti::TypeKind::Unknown
            )
          {
            // Like TypeScript with `--noImplicitAny`, flag unannotated bindings
            // that could not be inferred. Use `any` for recovery so later checks
            // don't cascade. Class fields use TS7008 ("Member '…'"); other
            // bindings keep our TC3000 placeholder until they gain stable tsc
            // codes.
            let is_class_field = self
              .hir_lowered
              .get(&def_data.file)
              .and_then(|lowered| lowered.def(HirDefId(def.0)))
              .is_some_and(|d| d.path.kind == HirDefKind::Field);
            let (name_span, display_name) = self.binding_name_span_and_display(def, &def_data);
            if is_class_field {
              self.push_program_diagnostic(codes::MEMBER_IMPLICIT_ANY.error(
                format!("Member '{display_name}' implicitly has an 'any' type."),
                Span::new(def_data.file, name_span),
              ));
            } else {
              self.push_program_diagnostic(codes::IMPLICIT_ANY.error(
                codes::implicit_any_message(Some(&display_name)),
                Span::new(def_data.file, name_span),
              ));
            }
            inferred = prim.any;
          }

          let init_is_satisfies = init
            .map(|init| self.init_is_satisfies(init.body, init.expr))
            .unwrap_or(false);

          if annotated.is_none() && !init_is_satisfies {
            inferred = crate::check::widen::widen_array_elements(store.as_ref(), inferred);
          }
          if annotated.is_none() && !init_is_satisfies {
            inferred = crate::check::widen::widen_object_literal_props(store.as_ref(), inferred);
          }

          if const_like {
            inferred
          } else {
            crate::check::widen::widen_literal(store.as_ref(), inferred)
          }
        }
        DefKind::VarDeclarator(_) => prim.unknown,
        DefKind::Class(class) => class.static_type.unwrap_or(prim.unknown),
        DefKind::Enum(en) => en.value_type.unwrap_or(prim.unknown),
        DefKind::Namespace(ns) => {
          if let Some(ns_ty) = ns_ty {
            if let Some(data) = self.def_data.get_mut(&def) {
              if let DefKind::Namespace(ns_data) = &mut data.kind {
                ns_data.value_type = Some(ns_ty);
                ns_data.type_type = Some(ns_ty);
              }
            }
            ns_ty
          } else {
            ns.value_type.unwrap_or(prim.unknown)
          }
        }
        DefKind::Module(ns) => {
          if let Some(ns_ty) = ns_ty {
            if let Some(data) = self.def_data.get_mut(&def) {
              if let DefKind::Module(ns_data) = &mut data.kind {
                ns_data.value_type = Some(ns_ty);
                ns_data.type_type = Some(ns_ty);
              }
            }
            ns_ty
          } else {
            ns.value_type.unwrap_or(prim.unknown)
          }
        }
        DefKind::Import(import) => {
          if import.original == "*" {
            match import.target {
              ImportTarget::File(file) => {
                if let Some(target) = self.export_assignment_target_def(file) {
                  self
                    .export_type_for_def(target)?
                    .unwrap_or(self.type_of_def(target)?)
                } else {
                  self.module_namespace_type(file)?
                }
              }
              ImportTarget::Unresolved { ref specifier } => {
                let exports = self.exports_of_ambient_module(specifier)?;
                if exports.is_empty() {
                  prim.unknown
                } else if let Some(entry) = exports.get("export=") {
                  if let Some(def) = entry.def {
                    self
                      .export_type_for_def(def)?
                      .unwrap_or(self.type_of_def(def)?)
                  } else if let Some(ty) = entry.type_id {
                    let unknown = !store.contains_type_id(ty)
                      || matches!(store.type_kind(store.canon(ty)), tti::TypeKind::Unknown);
                    if unknown {
                      prim.unknown
                    } else {
                      store.canon(ty)
                    }
                  } else {
                    prim.unknown
                  }
                } else {
                  self.module_namespace_object_type(&exports)?
                }
              }
            }
          } else {
            let exports = self.exports_for_import(&import)?;
            if let Some(entry) = exports.get(&import.original) {
              if let Some(def) = entry.def {
                if let Some(ty) = self.export_type_for_def(def)? {
                  ty
                } else {
                  self.type_of_def(def)?
                }
              } else if let Some(ty) = entry.type_id {
                let unknown = !store.contains_type_id(ty)
                  || matches!(store.type_kind(store.canon(ty)), tti::TypeKind::Unknown);
                if unknown {
                  prim.unknown
                } else {
                  store.canon(ty)
                }
              } else {
                prim.unknown
              }
            } else {
              prim.unknown
            }
          }
        }
        DefKind::ImportAlias(alias) => {
          match self.resolve_import_alias_target(def_data.file, &alias.path) {
            Some(target) if target != def => self.type_of_def(target)?,
            _ => prim.unknown,
          }
        }
        DefKind::Interface(interface) => self
          .interned_def_types
          .get(&def)
          .copied()
          .unwrap_or(interface.typ),
        DefKind::TypeAlias(alias) => {
          let mut typ = alias.typ;
          if store.contains_type_id(typ)
            && matches!(store.type_kind(store.canon(typ)), tti::TypeKind::Unknown)
          {
            if let Some(recomputed) =
              self.type_alias_type_for_span(def_data.file, def_data.span, &def_data.name)
            {
              typ = recomputed;
              if let Some(data) = self.def_data.get_mut(&def) {
                if let DefKind::TypeAlias(existing) = &mut data.kind {
                  existing.typ = typ;
                }
              }
            }
          }
          typ = self.resolve_value_ref_type(typ)?;
          if let Some(data) = self.def_data.get_mut(&def) {
            if let DefKind::TypeAlias(existing) = &mut data.kind {
              existing.typ = typ;
            }
          }
          typ
        }
      };
      self.check_cancelled()?;
      Ok(ty)
    })();

    self.type_stack.pop();
    self.current_file = prev_file;

    match result {
      Ok(mut ty) => {
        ty = if store.contains_type_id(ty) {
          store.canon(ty)
        } else {
          prim.unknown
        };

        let replace = self
          .interned_def_types
          .get(&def)
          .copied()
          .map(|existing| match store.type_kind(existing) {
            tti::TypeKind::Unknown => true,
            tti::TypeKind::Ref { def: ref_def, args } => {
              ref_def == tti::DefId(def.0) && args.is_empty()
            }
            _ => false,
          })
          .unwrap_or(true);

        if replace {
          self.interned_def_types.insert(def, ty);
        }

        if let Some(ns_ty) = ns_ty {
          match def_data.kind {
            DefKind::Function(_) | DefKind::Var(_) | DefKind::Class(_) | DefKind::Enum(_) => {
              let merged = if let Some(existing) = self.interned_def_types.get(&def).copied() {
                store.intersection(vec![existing, ns_ty])
              } else {
                ns_ty
              };
              self.interned_def_types.insert(def, merged);
            }
            _ => {}
          }
        }

        let ret_ty = self.interned_def_types.get(&def).copied().unwrap_or(ty);

        if let Some(file_state) = self.files.get_mut(&def_data.file) {
          if let Some(binding) = file_state.bindings.get_mut(&def_data.name) {
            if binding.def == Some(def) {
              binding.type_id = Some(ret_ty);
            }
          }
        }

        if let Some(span) = span.take() {
          span.finish(Some(ret_ty));
        }
        Ok(ret_ty)
      }
      Err(err) => {
        if let Some(span) = span.take() {
          span.finish(None);
        }
        Err(err)
      }
    }
  }

  /// TS7022 for unannotated defs whose type resolution re-entered via
  /// `type_stack` (circular initializer). No-op when annotated or when
  /// `--noImplicitAny` is off.
  fn report_circular_initializer_implicit_any(&mut self, def: DefId) {
    if !self.compiler_options.no_implicit_any {
      return;
    }
    let Some(def_data) = self.def_data.get(&def).cloned() else {
      return;
    };
    // Only value vars/fields participate in initializer circularity (class
    // fields are lowered as `DefKind::Var`).
    let DefKind::Var(var) = &def_data.kind else {
      return;
    };
    if var.typ.is_some() {
      return;
    }
    let has_hir_annotation = self
      .hir_lowered
      .get(&def_data.file)
      .and_then(|lowered| lowered.def(HirDefId(def.0)))
      .and_then(|hir_def| hir_def.declared_type)
      .is_some();
    if has_hir_annotation {
      return;
    }

    let (name_span, display_name) = self.binding_name_span_and_display(def, &def_data);
    self.push_program_diagnostic(codes::CIRCULAR_INITIALIZER_IMPLICIT_ANY.error(
      format!(
        "'{display_name}' implicitly has type 'any' because it does not have a type annotation and is referenced directly or indirectly in its own initializer."
      ),
      Span::new(def_data.file, name_span),
    ));
  }

  /// Name span + display string for binding/member diagnostics (TS7008/TS7022).
  ///
  /// For computed class fields, tsc highlights the full `["key"]` ComputedPropertyName
  /// (not our synthetic `<computed:…>` def name).
  fn binding_name_span_and_display(&self, def: DefId, def_data: &DefData) -> (TextRange, String) {
    let member_span = def_data.span;
    let name = def_data.name.as_str();
    let file_text = db::file_text(&self.typecheck_db, def_data.file);

    if name.starts_with("<computed:") {
      if let Some((span, display)) =
        computed_member_name_span_and_display(file_text.as_ref(), member_span)
      {
        return (span, display);
      }
    }

    // Prefer a precise name token within the member/declarator span.
    if let Some(span) = find_exact_name_span(file_text.as_ref(), name, member_span) {
      return (span, name.to_string());
    }

    let end = member_span
      .start
      .saturating_add(name.len() as u32)
      .min(member_span.end);
    if end > member_span.start {
      return (TextRange::new(member_span.start, end), name.to_string());
    }

    // Fall back: keep HIR def id in scope for future refinements.
    let _ = def;
    (member_span, name.to_string())
  }
}

fn computed_member_name_span_and_display(
  source: &str,
  member_span: TextRange,
) -> Option<(TextRange, String)> {
  let bytes = source.as_bytes();
  let start = member_span.start as usize;
  if start >= bytes.len() || bytes[start] != b'[' {
    return None;
  }
  let end_limit = (member_span.end as usize).min(bytes.len());
  let mut depth = 0i32;
  let mut i = start;
  while i < end_limit {
    match bytes[i] {
      b'[' => depth += 1,
      b']' => {
        depth -= 1;
        if depth == 0 {
          let end = i + 1;
          let display = source[start..end].to_string();
          return Some((TextRange::new(start as u32, end as u32), display));
        }
      }
      b'\'' | b'"' | b'`' => {
        let quote = bytes[i];
        i += 1;
        while i < end_limit {
          if bytes[i] == b'\\' {
            i = i.saturating_add(2);
            continue;
          }
          if bytes[i] == quote {
            break;
          }
          i += 1;
        }
      }
      _ => {}
    }
    i += 1;
  }
  None
}

fn find_exact_name_span(source: &str, name: &str, range: TextRange) -> Option<TextRange> {
  if name.is_empty() || name.starts_with('<') {
    return None;
  }
  let bytes = source.as_bytes();
  let start = (range.start as usize).min(bytes.len());
  let end = (range.end as usize).min(bytes.len());
  let slice = &source[start..end];
  let pos = slice.find(name)?;
  let abs_start = start + pos;
  let abs_end = abs_start + name.len();
  if abs_end > bytes.len() {
    return None;
  }
  Some(TextRange::new(abs_start as u32, abs_end as u32))
}
