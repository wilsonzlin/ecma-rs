use super::*;

impl ProgramState {
  fn param_type_for_def(&mut self, def: DefId, file: FileId) -> Result<TypeId, FatalError> {
    let unknown = self.interned_unknown();
    let Some(lowered) = self.hir_lowered.get(&file) else {
      return Ok(unknown);
    };
    let Some(hir_def) = lowered.def(def) else {
      return Ok(unknown);
    };
    let target_span = hir_def.span;

    fn record_matches(
      body_id: BodyId,
      body: &hir_js::Body,
      pat_id: HirPatId,
      target_span: TextRange,
      matches: &mut Vec<(BodyId, HirPatId)>,
    ) {
      let Some(pat) = body.pats.get(pat_id.0 as usize) else {
        return;
      };
      if pat.span == target_span {
        if matches!(pat.kind, HirPatKind::Ident(_)) {
          matches.push((body_id, pat_id));
        }
      }
      match &pat.kind {
        HirPatKind::Ident(_) | HirPatKind::AssignTarget(_) => {}
        HirPatKind::Array(arr) => {
          for elem in arr.elements.iter().flatten() {
            record_matches(body_id, body, elem.pat, target_span, matches);
          }
          if let Some(rest) = arr.rest {
            record_matches(body_id, body, rest, target_span, matches);
          }
        }
        HirPatKind::Object(obj) => {
          for prop in obj.props.iter() {
            record_matches(body_id, body, prop.value, target_span, matches);
          }
          if let Some(rest) = obj.rest {
            record_matches(body_id, body, rest, target_span, matches);
          }
        }
        HirPatKind::Rest(inner) => {
          record_matches(body_id, body, **inner, target_span, matches);
        }
        HirPatKind::Assign { target, .. } => {
          record_matches(body_id, body, *target, target_span, matches);
        }
      }
    }

    let mut body_ids: Vec<_> = lowered.body_index.keys().copied().collect();
    body_ids.sort_by_key(|id| id.0);
    let mut matches = Vec::new();
    for body_id in body_ids {
      let Some(body) = lowered.body(body_id) else {
        continue;
      };
      let Some(function) = body.function.as_ref() else {
        continue;
      };
      for param in function.params.iter() {
        record_matches(body_id, body, param.pat, target_span, &mut matches);
      }
    }

    matches.sort_by_key(|(body_id, pat_id)| (body_id.0, pat_id.0));
    let Some((body_id, pat_id)) = matches.first().copied() else {
      return Ok(unknown);
    };

    let result = self.check_body(body_id)?;
    Ok(result.pat_type(PatId(pat_id.0)).unwrap_or(unknown))
  }

  pub(super) fn type_of_def(&mut self, def: DefId) -> Result<TypeId, FatalError> {
    self.check_cancelled()?;
    let cache_hit = self.def_types.contains_key(&def);
    let mut span = QuerySpan::enter(
      QueryKind::TypeOfDef,
      query_span!(
        "typecheck_ts.type_of_def",
        self.def_data.get(&def).map(|d| d.file.0),
        Some(def.0),
        self.body_of_def(def).map(|b| b.0),
        cache_hit
      ),
      self.def_types.get(&def).copied(),
      cache_hit,
      Some(self.query_stats.clone()),
    );
    let def_data = match self.def_data.get(&def).cloned() {
      Some(data) => data,
      None => {
        if let Some(span) = span.take() {
          span.finish(Some(self.builtin.unknown));
        }
        return Ok(self.builtin.unknown);
      }
    };
    let is_param_def = self
      .hir_lowered
      .get(&def_data.file)
      .and_then(|lowered| lowered.def(def))
      .map(|hir_def| hir_def.path.kind == HirDefKind::Param)
      .unwrap_or(false);
    let synthetic_value_def = matches!(def_data.kind, DefKind::Var(_))
      && self.value_defs.values().any(|value_def| *value_def == def);

    if matches!(def_data.kind, DefKind::Interface(_)) {
      self.merge_interface_symbol_types(def)?;
    }

    if let Some(store) = self.interned_store.clone() {
      if let Some(interned) = self.interned_def_types.get(&def).copied() {
        let skip_cache = matches!(def_data.kind, DefKind::Var(_)) && !synthetic_value_def;
        let mut ty = store.canon(interned);
        let is_self_ref = matches!(
          store.type_kind(ty),
          tti::TypeKind::Ref { def: ref_def, args }
            if args.is_empty() && ref_def.0 == def.0
        );
        if matches!(store.type_kind(ty), tti::TypeKind::Unknown)
          || skip_cache
          || (is_param_def && is_self_ref)
        {
          self.interned_def_types.remove(&def);
        } else {
          if let DefKind::Function(func) = &def_data.kind {
            if func.return_ann.is_none()
              && func.body.is_some()
              && matches!(store.type_kind(ty), tti::TypeKind::Callable { .. })
              && callable_return_is_unknown(&store, ty)
            {
              let has_overloads = self.def_data.iter().any(|(other, data)| {
                *other != def
                  && data.symbol == def_data.symbol
                  && matches!(data.kind, DefKind::Function(_))
              });
              if !has_overloads {
                if let Some(updated) =
                  self.infer_cached_callable_return_type(def, func, &store, ty)?
                {
                  ty = updated;
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
    }
    if let Some(existing) = self.def_types.get(&def).copied() {
      let skip_cache = matches!(def_data.kind, DefKind::Var(_)) && !synthetic_value_def;
      let in_bounds = self.type_store.contains_id(existing);
      let needs_recompute = match &def_data.kind {
        DefKind::Function(func) => {
          func.return_ann.is_none()
            && func.body.is_some()
            && matches!(self.type_store.kind(existing), TypeKind::Function { ret, .. } if *ret == self.builtin.unknown)
        }
        _ => false,
      };
      if !skip_cache
        && in_bounds
        && !matches!(self.type_store.kind(existing), TypeKind::Unknown)
        && !needs_recompute
      {
        let ret = if let Some(store) = self.interned_store.as_ref() {
          self
            .interned_def_types
            .get(&def)
            .copied()
            .map(|ty| store.canon(ty))
            .unwrap_or(existing)
        } else {
          existing
        };
        if let Some(span) = span.take() {
          span.finish(Some(ret));
        }
        return Ok(ret);
      }
      self.def_types.remove(&def);
      self.interned_def_types.remove(&def);
    }
    let prev_file = self.current_file;
    self.current_file = Some(def_data.file);
    if self.type_stack.contains(&def) {
      if let Some(store) = self.interned_store.as_ref() {
        let ty = store.canon(store.intern_type(tti::TypeKind::Ref {
          def: tti::DefId(def.0),
          args: Vec::new(),
        }));
        self.interned_def_types.entry(def).or_insert(ty);
        let imported = self.import_interned_type(ty);
        self.def_types.entry(def).or_insert(imported);
        if let Some(span) = span.take() {
          span.finish(Some(ty));
        }
        self.current_file = prev_file;
        return Ok(ty);
      } else {
        if let Some(span) = span.take() {
          span.finish(Some(self.builtin.any));
        }
        self.current_file = prev_file;
        return Ok(self.builtin.any);
      }
    }
    let ns_entry = self
      .namespace_object_types
      .get(&(def_data.file, def_data.name.clone()))
      .copied();
    self.type_stack.push(def);
    let result = (|| -> Result<TypeId, FatalError> {
      self.check_cancelled()?;
      let ty = match def_data.kind.clone() {
        DefKind::Function(func) => self.function_type(def, func)?,
        DefKind::Var(var) => {
          if is_param_def {
            return Ok(self.param_type_for_def(def, def_data.file)?);
          }
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
          let declared_ann = self.declared_type_for_span(def_data.file, def_data.span);
          let annotated_raw = declared_ann.or(var.typ);
          let annotated = match annotated_raw {
            Some(ty) => Some(self.resolve_value_ref_type(ty)?),
            None => None,
          };
          let mut preserved_interned_init: Option<TypeId> = None;
          if let Some(annotated) = annotated {
            if let Some(store) = self.interned_store.as_ref() {
              if store.contains_type_id(annotated) {
                self
                  .interned_def_types
                  .entry(def)
                  .or_insert(store.canon(annotated));
              }
            }
            self.def_types.entry(def).or_insert(annotated);
          }
          let mut skip_implicit_any = false;
          let mut inferred = if let Some(t) = annotated {
            t
          } else if let Some(init) = init {
            if self.checking_bodies.contains(&init.body) {
              skip_implicit_any = true;
              self.builtin.unknown
            } else {
              self.body_results.remove(&init.body);
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
                .filter(|ty| !self.is_unknown_type_id(*ty));
              let init_ty_was_pat = init_ty_from_pat.is_some();
              let init_ty = init_ty_from_pat.or_else(|| res.expr_type(init.expr));
              if let Some(init_ty) = init_ty {
                let init_ty = self.resolve_value_ref_type(init_ty)?;
                let init_ty = if let Some(store) = self.interned_store.as_ref() {
                  let init_ty = store.canon(init_ty);
                  // Prefer preserving the interned binding type we got from
                  // the body checker. Round-tripping through the legacy
                  // `TypeStore` loses information like method-ness and often
                  // erases nominal refs entirely.
                  if init_ty_was_pat
                    || matches!(store.type_kind(init_ty), tti::TypeKind::Ref { .. })
                  {
                    preserved_interned_init = Some(init_ty);
                  }
                  self
                    .interned_def_types
                    .entry(def)
                    .and_modify(|existing| {
                      *existing =
                        ProgramState::merge_interned_decl_types(store, *existing, init_ty);
                    })
                    .or_insert(init_ty);
                  init_ty
                } else {
                  init_ty
                };
                self.import_interned_type(init_ty)
              } else {
                self.builtin.unknown
              }
            }
          } else if let Some((_, store_ty)) = ns_entry {
            store_ty
          } else if let Some(raw) = annotated_raw {
            raw
          } else {
            self.builtin.unknown
          };
          if const_like && init_pat_is_root {
            if let Some(init_span) = init_span_for_const {
              if let Some(file_body) = self.files.get(&def_data.file).and_then(|f| f.top_body) {
                if let Some(res) = self.body_results.get(&file_body).cloned() {
                  let top_ty = res
                    .expr_spans()
                    .iter()
                    .enumerate()
                    .find(|(_, span)| **span == init_span)
                    .and_then(|(idx, _)| res.expr_type(ExprId(idx as u32)));
                  if let (Some(top_ty), Some(store)) = (top_ty, self.interned_store.as_ref()) {
                    let top_kind = store.type_kind(top_ty);
                    let has_readonly = match top_kind {
                      tti::TypeKind::Object(obj) => {
                        let shape = store.shape(store.object(obj).shape);
                        shape.properties.iter().any(|p| p.data.readonly)
                      }
                      tti::TypeKind::Tuple(elems) => elems.iter().any(|e| e.readonly),
                      _ => false,
                    };
                    if has_readonly {
                      let top_ty = store.canon(top_ty);
                      self.interned_def_types.insert(def, top_ty);
                      inferred = self.import_interned_type(top_ty);
                    }
                  }
                }
              }
            }
          }
          if self.compiler_options.no_implicit_any
            && !skip_implicit_any
            && annotated.is_none()
            && inferred == self.builtin.unknown
          {
            // Like TypeScript with `--noImplicitAny`, flag unannotated bindings
            // that could not be inferred. Use `any` for recovery so later checks
            // don't cascade.
            self.push_program_diagnostic(codes::IMPLICIT_ANY.error(
              codes::implicit_any_message(Some(&def_data.name)),
              Span::new(def_data.file, def_data.span),
            ));
            inferred = self.builtin.any;
          }
          let init_is_satisfies = init
            .map(|init| self.init_is_satisfies(init.body, init.expr))
            .unwrap_or(false);
          if annotated.is_none() && !init_is_satisfies {
            inferred = self.widen_array_elements(inferred);
          }
          if annotated.is_none() {
            if !init_is_satisfies {
              inferred = self.widen_object_literal(inferred);
            }
          }
          let ty = if const_like {
            inferred
          } else {
            self.widen_literal(inferred)
          };
          if let Some(store) = self.interned_store.as_ref() {
            let mut cache = HashMap::new();
            let mut interned = store.canon(convert_type_for_display(ty, self, store, &mut cache));
            if annotated.is_none() {
              // The legacy `TypeStore` cannot represent `TypeKind::Ref`, and
              // converting through it also erases rich property metadata
              // (like "method" vs "property"). When we inferred a concrete
              // interned binding type from the body checker, preserve it
              // instead of round-tripping through the legacy store.
              if let Some(preserved) = preserved_interned_init.take() {
                interned = preserved;
              }
            }
            if annotated.is_some() {
              self
                .interned_def_types
                .entry(def)
                .and_modify(|existing| {
                  *existing = ProgramState::merge_interned_decl_types(store, *existing, interned);
                })
                .or_insert(interned);
            } else {
              self.interned_def_types.insert(def, interned);
            }
            if std::env::var("DEBUG_OVERLOAD").is_ok()
              && (def_data.name == "asString" || def_data.name == "asNumber")
            {
              eprintln!(
                "DEBUG var {} inferred {}",
                def_data.name,
                tti::TypeDisplay::new(store, interned)
              );
            }
          }
          ty
        }
        DefKind::VarDeclarator(_) => self.builtin.unknown,
        DefKind::Class(class) => {
          if let Some(store) = self.interned_store.as_ref() {
            if let Some(instance_type) = class.instance_type {
              let mut cache = HashMap::new();
              let interned = store.canon(convert_type_for_display(
                instance_type,
                self,
                store,
                &mut cache,
              ));
              self.interned_def_types.entry(def).or_insert(interned);
            }
          }
          class.static_type.unwrap_or(self.builtin.unknown)
        }
        DefKind::Enum(en) => {
          if let Some(store) = self.interned_store.as_ref() {
            if let Some(enum_type) = en.type_type {
              let mut cache = HashMap::new();
              let interned =
                store.canon(convert_type_for_display(enum_type, self, store, &mut cache));
              self.interned_def_types.entry(def).or_insert(interned);
            }
          }
          en.value_type.unwrap_or(self.builtin.unknown)
        }
        DefKind::Namespace(ns) => {
          if let Some((ns_interned, ns_store)) = ns_entry {
            self.def_types.insert(def, ns_store);
            self.interned_def_types.entry(def).or_insert(ns_interned);
            if let Some(data) = self.def_data.get_mut(&def) {
              if let DefKind::Namespace(ns_data) = &mut data.kind {
                ns_data.value_type = Some(ns_store);
                ns_data.type_type = Some(ns_store);
              }
            }
            ns_store
          } else {
            ns.value_type.unwrap_or(self.builtin.unknown)
          }
        }
        DefKind::Module(ns) => {
          if let Some((ns_interned, ns_store)) = ns_entry {
            self.def_types.insert(def, ns_store);
            self.interned_def_types.entry(def).or_insert(ns_interned);
            if let Some(data) = self.def_data.get_mut(&def) {
              if let DefKind::Module(ns_data) = &mut data.kind {
                ns_data.value_type = Some(ns_store);
                ns_data.type_type = Some(ns_store);
              }
            }
            ns_store
          } else {
            ns.value_type.unwrap_or(self.builtin.unknown)
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
                  self.builtin.unknown
                } else if let Some(entry) = exports.get("export=") {
                  if let Some(def) = entry.def {
                    self
                      .export_type_for_def(def)?
                      .unwrap_or(self.type_of_def(def)?)
                  } else if let Some(ty) = entry.type_id {
                    let mut unknown = false;
                    if self.type_store.contains_id(ty) {
                      unknown = matches!(self.type_store.kind(ty), TypeKind::Unknown);
                    } else if let Some(store) = self.interned_store.as_ref() {
                      if store.contains_type_id(ty) {
                        unknown = matches!(store.type_kind(ty), tti::TypeKind::Unknown);
                      }
                    }
                    if unknown {
                      self.builtin.unknown
                    } else {
                      ty
                    }
                  } else {
                    self.builtin.unknown
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
                let mut unknown = false;
                if self.type_store.contains_id(ty) {
                  unknown = matches!(self.type_store.kind(ty), TypeKind::Unknown);
                } else if let Some(store) = self.interned_store.as_ref() {
                  if store.contains_type_id(ty) {
                    unknown = matches!(store.type_kind(ty), tti::TypeKind::Unknown);
                  }
                }
                if !unknown {
                  ty
                } else {
                  self.builtin.unknown
                }
              } else {
                self.builtin.unknown
              }
            } else {
              self.builtin.unknown
            }
          }
        }
        DefKind::ImportAlias(alias) => {
          match self.resolve_import_alias_target(def_data.file, &alias.path) {
            Some(target) if target != def => self.type_of_def(target)?,
            _ => self.builtin.unknown,
          }
        }
        DefKind::Interface(interface) => {
          if let Some(store) = self.interned_store.as_ref() {
            if !self.interned_def_types.contains_key(&def) {
              let mut cache = HashMap::new();
              let interned = convert_type_for_display(interface.typ, self, store, &mut cache);
              self.interned_def_types.insert(def, store.canon(interned));
            }
          }
          interface.typ
        }
        DefKind::TypeAlias(alias) => {
          let mut typ = alias.typ;
          if typ == self.builtin.unknown {
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
          if let Some(store) = self.interned_store.as_ref() {
            if !self.interned_def_types.contains_key(&def) {
              let mut cache = HashMap::new();
              let interned = convert_type_for_display(typ, self, store, &mut cache);
              self.interned_def_types.insert(def, store.canon(interned));
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
        if let Some(store) = self.interned_store.as_ref() {
          if store.contains_type_id(ty) {
            let interned = store.canon(ty);
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
              self.interned_def_types.insert(def, interned);
            }
            let imported = self.import_interned_type(interned);
            ty = if imported == self.builtin.unknown {
              interned
            } else {
              imported
            };
          } else if !self.interned_def_types.contains_key(&def) {
            let mut cache = HashMap::new();
            let interned = store.canon(convert_type_for_display(ty, self, store, &mut cache));
            self.interned_def_types.insert(def, interned);
          }
        }
        if let Some((ns_interned, _ns_store)) = ns_entry {
          match def_data.kind {
            DefKind::Function(_) | DefKind::Var(_) | DefKind::Class(_) | DefKind::Enum(_) => {
              if let Some(store) = self.interned_store.as_ref() {
                let merged = if let Some(existing) = self.interned_def_types.get(&def).copied() {
                  store.intersection(vec![existing, ns_interned])
                } else {
                  ns_interned
                };
                self.interned_def_types.insert(def, merged);
              }
            }
            _ => {}
          }
        }
        self.def_types.insert(def, ty);
        let ret_ty = if let Some(store) = self.interned_store.as_ref() {
          self
            .interned_def_types
            .get(&def)
            .copied()
            .map(|ty| store.canon(ty))
            .unwrap_or(ty)
        } else {
          ty
        };
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

  fn infer_cached_callable_return_type(
    &mut self,
    def: DefId,
    func: &FuncData,
    store: &Arc<tti::TypeStore>,
    callable_ty: TypeId,
  ) -> Result<Option<TypeId>, FatalError> {
    let Some(body) = func.body else {
      return Ok(None);
    };
    let is_async = self.body_is_async_function(body);
    let tti::TypeKind::Callable { overloads } = store.type_kind(callable_ty) else {
      return Ok(None);
    };
    if overloads.len() != 1 {
      return Ok(None);
    }
    let mut ret = if self.checking_bodies.contains(&body) {
      store.primitive_ids().unknown
    } else {
      let res = self.check_body(body)?;
      if res.return_types.is_empty() {
        store.primitive_ids().void
      } else {
        let mut members = Vec::new();
        for ty in res.return_types.iter() {
          let ty = store.canon(self.ensure_interned_type(*ty));
          let widened = check::widen::widen_literal(store.as_ref(), ty);
          members.push(widened);
        }
        store.union(members)
      }
    };
    let prim = store.primitive_ids();
    if is_async && ret != prim.unknown {
      ret = self
        .promise_ref(store.as_ref(), ret)
        .unwrap_or(prim.unknown);
    }
    let sig_id = overloads[0];
    let mut sig = store.signature(sig_id);
    if sig.ret == ret {
      return Ok(None);
    }
    sig.ret = ret;
    let sig_id = store.intern_signature(sig);
    let callable_ty = store.canon(store.intern_type(tti::TypeKind::Callable {
      overloads: vec![sig_id],
    }));
    self.interned_def_types.insert(def, callable_ty);
    self.def_types.insert(def, callable_ty);
    if let Some(def_data) = self.def_data.get(&def) {
      if let Some(file_state) = self.files.get_mut(&def_data.file) {
        if let Some(binding) = file_state.bindings.get_mut(&def_data.name) {
          if binding.def == Some(def) {
            binding.type_id = Some(callable_ty);
          }
        }
      }
    }
    Ok(Some(callable_ty))
  }

  fn body_is_async_function(&self, body_id: BodyId) -> bool {
    let Some(meta) = self.body_map.get(&body_id) else {
      return false;
    };
    let Some(hir_body_id) = meta.hir else {
      return false;
    };
    let Some(lowered) = self.hir_lowered.get(&meta.file) else {
      return false;
    };
    let Some(body) = lowered.body(hir_body_id) else {
      return false;
    };
    body.function.as_ref().is_some_and(|f| f.async_)
  }

  fn resolve_promise_def(&self) -> Option<tti::DefId> {
    let mut best: Option<((u8, u8, u32, u32, u64), DefId)> = None;
    for (def, data) in self.def_data.iter() {
      if data.name != "Promise" {
        continue;
      }
      let pri = self.def_priority(*def, sem_ts::Namespace::TYPE);
      if pri == u8::MAX {
        continue;
      }
      let origin = self.file_registry.lookup_origin(data.file);
      let origin_rank: u8 = if self.current_file == Some(data.file) {
        0
      } else if matches!(origin, Some(FileOrigin::Source)) {
        1
      } else {
        2
      };
      let span = data.span;
      let key = (origin_rank, pri, span.start, span.end, def.0);
      best = match best {
        Some((best_key, best_def)) if best_key <= key => Some((best_key, best_def)),
        _ => Some((key, *def)),
      };
    }
    best.map(|(_, def)| tti::DefId(def.0))
  }

  fn promise_ref(&self, store: &tti::TypeStore, inner: TypeId) -> Option<TypeId> {
    let def = self.resolve_promise_def()?;
    Some(store.canon(store.intern_type(tti::TypeKind::Ref {
      def,
      args: vec![store.canon(inner)],
    })))
  }

  fn function_type(&mut self, def: DefId, func: FuncData) -> Result<TypeId, FatalError> {
    self.check_cancelled()?;
    let param_types: Vec<TypeId> = func
      .params
      .iter()
      .map(|p| p.typ.unwrap_or(self.builtin.any))
      .collect();
    let inferred_from_body = func.return_ann.is_none() && func.body.is_some();
    let ret = if let Some(ret) = func.return_ann {
      ret
    } else if let Some(body) = func.body {
      self.check_cancelled()?;
      if self.checking_bodies.contains(&body) {
        self.builtin.unknown
      } else {
        let res = self.check_body(body)?;
        if res.return_types.is_empty() {
          self.builtin.void
        } else {
          let mut widened = Vec::new();
          for ty in res.return_types.iter() {
            let imported = self.import_interned_type(*ty);
            widened.push(self.widen_literal(imported));
          }
          self.type_store.union(widened, &self.builtin)
        }
      }
    } else {
      self.builtin.unknown
    };
    let ty = self.type_store.function(param_types, ret);
    if let Some(store) = self.interned_store.as_ref() {
      let mut cache = HashMap::new();
      let mut interned = store.canon(convert_type_for_display(ty, self, store, &mut cache));
      if inferred_from_body
        && func
          .body
          .is_some_and(|body| self.body_is_async_function(body))
      {
        let prim = store.primitive_ids();
        if let tti::TypeKind::Callable { overloads } = store.type_kind(interned) {
          if overloads.len() == 1 {
            let sig_id = overloads[0];
            let mut sig = store.signature(sig_id);
            if sig.ret != prim.unknown {
              let wrapped = self
                .promise_ref(store.as_ref(), sig.ret)
                .unwrap_or(prim.unknown);
              if wrapped != sig.ret {
                sig.ret = wrapped;
                let sig_id = store.intern_signature(sig);
                interned = store.canon(store.intern_type(tti::TypeKind::Callable {
                  overloads: vec![sig_id],
                }));
              }
            }
          }
        }
      }
      self.interned_def_types.insert(def, interned);
    }
    self.def_types.insert(def, ty);
    Ok(ty)
  }

}
