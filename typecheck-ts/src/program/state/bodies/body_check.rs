use super::*;

mod helpers;

impl ProgramState {
  pub(in super::super) fn check_body(
    &mut self,
    body_id: BodyId,
  ) -> Result<Arc<BodyCheckResult>, FatalError> {
    self.check_cancelled()?;
    let _parallel_guard = db::queries::body_check::parallel_guard();
    let cache_hit = self.local_body_results.contains_key(&body_id);
    let body_meta = self.body_map.get(&body_id).copied();
    let owner = self.owner_of_body(body_id);
    let prev_file = self.current_file;
    if let Some(meta) = body_meta.as_ref() {
      self.current_file = Some(meta.file);
    }
    let mut span = QuerySpan::enter(
      QueryKind::CheckBody,
      query_span!(
        "typecheck_ts.check_body",
        body_meta.as_ref().map(|b| b.file.0),
        owner.map(|d| d.0),
        Some(body_id.0),
        cache_hit
      ),
      None,
      cache_hit,
      Some(self.query_stats.clone()),
    );
    if let Some(existing) = self.local_body_results.get(&body_id).cloned() {
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return Ok(existing);
    }
    let already_checking = !self
      .checking_bodies
      .lock()
      .unwrap_or_else(|err| err.into_inner())
      .insert(body_id);
    if already_checking {
      let res = self
        .local_body_results
        .get(&body_id)
        .cloned()
        .unwrap_or_else(|| BodyCheckResult::empty(body_id));
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return Ok(res);
    }
    /// Removes the body from the in-progress set on every exit path
    /// (including unwinds). Holds a shared handle rather than a pointer into
    /// `ProgramState`, so `self` stays freely usable while the guard lives.
    struct BodyCheckGuard {
      checking: std::sync::Arc<std::sync::Mutex<HashSet<BodyId>>>,
      body: BodyId,
    }
    impl Drop for BodyCheckGuard {
      fn drop(&mut self) {
        self
          .checking
          .lock()
          .unwrap_or_else(|err| err.into_inner())
          .remove(&self.body);
      }
    }
    let _body_guard = BodyCheckGuard {
      checking: std::sync::Arc::clone(&self.checking_bodies),
      body: body_id,
    };
    let Some(meta) = body_meta else {
      let res = Arc::new(BodyCheckResult {
        body: body_id,
        expr_types: Vec::new(),
        expr_spans: Vec::new(),
        pat_types: Vec::new(),
        pat_spans: Vec::new(),
        diagnostics: vec![codes::MISSING_BODY.error(
          "missing body",
          Span::new(FileId(u32::MAX), TextRange::new(0, 0)),
        )],
        return_types: Vec::new(),
        yield_types: Vec::new(),
      });
      self.local_body_results.insert(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return Ok(res);
    };

    let file = meta.file;

    let Some(lowered) = self.hir_lowered.get(&file).cloned() else {
      let res = Arc::new(BodyCheckResult {
        body: body_id,
        expr_types: Vec::new(),
        expr_spans: Vec::new(),
        pat_types: Vec::new(),
        pat_spans: Vec::new(),
        diagnostics: Vec::new(),
        return_types: Vec::new(),
        yield_types: Vec::new(),
      });
      self.local_body_results.insert(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return Ok(res);
    };

    let Some(ast) = self.asts.get(&file).cloned() else {
      let res = Arc::new(BodyCheckResult {
        body: body_id,
        expr_types: Vec::new(),
        expr_spans: Vec::new(),
        pat_types: Vec::new(),
        pat_spans: Vec::new(),
        diagnostics: vec![codes::MISSING_BODY.error(
          "missing parsed AST for body",
          Span::new(file, TextRange::new(0, 0)),
        )],
        return_types: Vec::new(),
        yield_types: Vec::new(),
      });
      self.local_body_results.insert(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      return Ok(res);
    };

    let mut _synthetic = None;
    let body = if let Some(hir_id) = meta.hir {
      lowered.body(hir_id)
    } else if matches!(meta.kind, HirBodyKind::TopLevel) {
      _synthetic = Some(hir_js::Body {
        owner: MISSING_DEF,
        span: TextRange::new(0, 0),
        kind: HirBodyKind::TopLevel,
        exprs: Vec::new(),
        stmts: Vec::new(),
        pats: Vec::new(),
        locals: Vec::new(),
        root_stmts: Vec::new(),
        function: None,
        class: None,
        expr_types: None,
      });
      _synthetic.as_ref()
    } else {
      None
    };

    let Some(body) = body else {
      let res = Arc::new(BodyCheckResult {
        body: body_id,
        expr_types: Vec::new(),
        expr_spans: Vec::new(),
        pat_types: Vec::new(),
        pat_spans: Vec::new(),
        diagnostics: Vec::new(),
        return_types: Vec::new(),
        yield_types: Vec::new(),
      });
      self.local_body_results.insert(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      return Ok(res);
    };

    if let Err(err) = self.check_cancelled() {
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return Err(err);
    }

    let store = Arc::clone(&self.store);
    let nested_check = self
      .checking_bodies
      .lock()
      .unwrap_or_else(|err| err.into_inner())
      .len()
      > 1;
    if self.callable_overloads.is_empty() {
      self.rebuild_callable_overloads();
    }

    let mut bindings: HashMap<String, TypeId> = HashMap::new();
    let mut binding_defs: HashMap<String, DefId> = HashMap::new();
    let map_def_ty = |state: &mut ProgramState, store: &Arc<tti::TypeStore>, def: DefId| {
      if owner == Some(def) {
        return state
          .interned_def_types
          .get(&def)
          .copied()
          .map(|ty| store.canon(ty));
      }

      // Class/enum defs store the *instance* type; value bindings need the
      // constructor value stored under the synthetic value def (cross-file
      // ambient `declare class` + `new C(...)` in another file).
      let def = state.value_defs.get(&def).copied().unwrap_or(def);

      let var_info = state.def_data.get(&def).and_then(|def_data| {
        if let DefKind::Var(var) = &def_data.kind {
          Some((def_data.file, def_data.span, var.typ))
        } else {
          None
        }
      });
      if let Some((file, span, var_typ)) = var_info {
        // Prefer HIR `declared_type` (class fields), then AST span lookup, then
        // the binder-populated `VarData.typ`.
        let ty = state
          .hir_declared_type_for_def(def)
          .or_else(|| state.declared_type_for_span(file, span))
          .or(var_typ);
        if let Some(ty) = ty {
          return Some(if store.contains_type_id(ty) {
            store.canon(ty)
          } else {
            store.primitive_ids().unknown
          });
        }
      }

      let import_target = state.def_data.get(&def).and_then(|data| {
        if let DefKind::Import(import) = &data.kind {
          Some(import.clone())
        } else {
          None
        }
      });

      let should_infer_callable_return = state.def_data.get(&def).is_some_and(|data| {
        matches!(
          data.kind,
          DefKind::Function(FuncData {
            return_ann: None,
            body: Some(_),
            ..
          })
        )
      });
      let cached_interned = state
        .interned_def_types
        .get(&def)
        .copied()
        .filter(|ty| store.contains_type_id(*ty))
        .map(|ty| store.canon(ty))
        .filter(|ty| !matches!(store.type_kind(*ty), tti::TypeKind::Unknown));
      let cached_interned = cached_interned
        .filter(|ty| !should_infer_callable_return || !callable_return_is_unknown(store, *ty));
      let computed = if Some(def) == owner {
        None
      } else if nested_check {
        // Nested body checks (e.g. while resolving other defs) still need to
        // compute referenced function types so async/await and return inference
        // can see real call signatures. Other defs are skipped to avoid deep
        // recursion and duplicate diagnostics.
        match state.def_data.get(&def).map(|data| &data.kind) {
          Some(DefKind::Function(_)) => state.type_of_def(def).ok().map(|ty| store.canon(ty)),
          _ => None,
        }
      } else {
        state.type_of_def(def).ok().map(|ty| store.canon(ty))
      };

      let ty = cached_interned.or(computed);

      if let Some(mut ty) = ty {
        if let Some(def_data) = state.def_data.get(&def) {
          if let Some(ns_ty) = state
            .namespace_object_types
            .get(&(def_data.file, def_data.name.clone()))
            .copied()
          {
            let ns_ty = if store.contains_type_id(ns_ty) {
              store.canon(ns_ty)
            } else {
              store.primitive_ids().unknown
            };
            ty = store.intersection(vec![ty, ns_ty]);
          }
        }
        if let Some(import) = import_target.as_ref() {
          if let Ok(exports) = state.exports_for_import(import) {
            if let Some(entry) = exports.get(&import.original) {
              let mapped = if let Some(target) = entry.def {
                if let Some(defs) = state.callable_overload_defs(target) {
                  state
                    .merged_overload_callable_type(&defs, store)
                    .or_else(|| state.export_type_for_def(target).ok().flatten())
                    .or(entry.type_id)
                } else {
                  state
                    .export_type_for_def(target)
                    .ok()
                    .flatten()
                    .or(entry.type_id)
                }
              } else {
                entry.type_id
              };
              if let Some(exported) = mapped {
                let mapped = if store.contains_type_id(exported) {
                  store.canon(exported)
                } else {
                  store.primitive_ids().unknown
                };
                ty = mapped;
                state.interned_def_types.insert(def, mapped);
              }
            }
          }
        }
        Some(ty)
      } else {
        None
      }
    };

    let mut file_binding_entries: Vec<_> = self
      .files
      .get(&file)
      .map(|state| {
        state
          .bindings
          .iter()
          .map(|(name, binding)| (name.clone(), binding.clone()))
          .collect::<Vec<_>>()
      })
      .unwrap_or_default();
    file_binding_entries.sort_by(|(name_a, binding_a), (name_b, binding_b)| {
      let def_key_a = binding_a
        .def
        .and_then(|def| {
          self
            .def_data
            .get(&def)
            .map(|data| (data.span.start, data.span.end, def.0))
        })
        .unwrap_or((u32::MAX, u32::MAX, u64::MAX));
      let def_key_b = binding_b
        .def
        .and_then(|def| {
          self
            .def_data
            .get(&def)
            .map(|data| (data.span.start, data.span.end, def.0))
        })
        .unwrap_or((u32::MAX, u32::MAX, u64::MAX));
      def_key_a.cmp(&def_key_b).then_with(|| name_a.cmp(name_b))
    });
    let file_binding_names: HashSet<_> = file_binding_entries
      .iter()
      .map(|(name, _)| name.clone())
      .collect();

    // JSX tag names are not represented as `ExprKind::Ident` in HIR, so we need
    // to collect component tag bases explicitly. This lets the body checker
    // include value bindings for imported/global components referenced only
    // from JSX (e.g. `<Foo />` or `<Foo.Bar />`).
    //
    // NOTE: JSX tag names containing `:` (namespaced) or `-` (custom elements)
    // should always be treated as intrinsic elements and must not be seeded as
    // value identifiers, regardless of capitalization.
    let needed_root_names: HashSet<String> = match self.local_semantics.get(&file) {
      Some(locals) => {
        let mut names = HashSet::new();
        for (idx, expr) in body.exprs.iter().enumerate() {
          if idx % 4096 == 0 {
            self.check_cancelled()?;
          }
          match &expr.kind {
            hir_js::ExprKind::Ident(name_id) => {
              let Some(name) = lowered.names.resolve(*name_id) else {
                continue;
              };
              let resolved_root = match locals.resolve_expr(body, hir_js::ExprId(idx as u32)) {
                Some(binding_id) => locals.symbol(binding_id).decl_scope == locals.root_scope(),
                // If locals didn't record the binding, fall back to the textual name so we still
                // seed file/global bindings for the body checker.
                None => true,
              };
              if resolved_root {
                names.insert(name.to_string());
              }
            }
            hir_js::ExprKind::Jsx(jsxe) => {
              helpers::collect_jsx_root_names(jsxe, &lowered, &mut names);
            }
            _ => {}
          }
        }
        names
      }
      None => {
        let mut names = HashSet::new();
        for expr in &body.exprs {
          match &expr.kind {
            hir_js::ExprKind::Ident(name_id) => {
              if let Some(name) = lowered.names.resolve(*name_id) {
                names.insert(name.to_string());
              }
            }
            hir_js::ExprKind::Jsx(jsxe) => {
              helpers::collect_jsx_root_names(jsxe, &lowered, &mut names);
            }
            _ => {}
          }
        }
        names
      }
    };

    let mut needed_globals: Vec<_> = needed_root_names
      .iter()
      .filter(|name| !file_binding_names.contains(*name))
      .cloned()
      .collect();
    needed_globals.sort();
    let global_binding_entries: Vec<_> = needed_globals
      .into_iter()
      .filter_map(|name| {
        self
          .global_bindings
          .get(&name)
          .cloned()
          .map(|binding| (name, binding))
      })
      .collect();

    let mut bind =
      |name: &str, binding: &SymbolBinding, include_type: bool| -> Result<(), FatalError> {
        self.check_cancelled()?;
        let prim = store.primitive_ids();
        let mut def_for_resolver = binding.def;
        let overload_defs = binding.def.and_then(|def| self.callable_overload_defs(def));
        if let Some(defs) = overload_defs.as_ref() {
          if let Some(first) = defs.first().copied() {
            def_for_resolver = Some(first);
          }
        }
        if let Some(def) = def_for_resolver {
          binding_defs.insert(name.to_string(), def);
        }
        if !include_type {
          return Ok(());
        }
        let mut ty = if binding.def.is_some() {
          None
        } else {
          binding
            .type_id
            .and_then(|ty| store.contains_type_id(ty).then_some(store.canon(ty)))
        };
        if let Some(converted) = ty {
          if matches!(store.type_kind(converted), tti::TypeKind::Unknown) {
            ty = None;
          }
        }
        let is_owner = owner == binding.def;
        let debug_overload = std::env::var("DEBUG_OVERLOAD").is_ok() && name == "overload";
        if let Some(def) = binding.def {
          if let Some(def_data) = self.def_data.get(&def) {
            if let DefKind::Import(import) = &def_data.kind {
              let import = import.clone();
              if let Ok(exports) = self.exports_for_import(&import) {
                if let Some(entry) = exports.get(&import.original) {
                  if debug_overload {
                    if let Some(ty) = entry.type_id {
                      let disp = if store.contains_type_id(ty) {
                        tti::TypeDisplay::new(&store, store.canon(ty))
                      } else {
                        tti::TypeDisplay::new(&store, store.primitive_ids().unknown)
                      };
                      eprintln!("DEBUG import export type {disp}");
                    }
                  }
                  if let Some(target) = entry.def {
                    if let Some(defs) = self.callable_overload_defs(target) {
                      if defs.len() > 1 {
                        if let Some(merged) = self.callable_overload_type_for_def(target, &store) {
                          ty = Some(merged);
                          self.interned_def_types.insert(def, merged);
                        }
                      }
                    }
                  }
                  if ty.is_none() {
                    let mapped = entry.type_id.or_else(|| {
                      entry
                        .def
                        .and_then(|target| self.export_type_for_def(target).ok().flatten())
                    });
                    if let Some(exported) = mapped {
                      let mapped = store
                        .contains_type_id(exported)
                        .then_some(store.canon(exported))
                        .unwrap_or_else(|| store.primitive_ids().unknown);
                      ty = Some(mapped);
                      self.interned_def_types.insert(def, mapped);
                    }
                  }
                }
              }
            }
          }
          if let Some(defs) = overload_defs {
            if debug_overload {
              eprintln!("DEBUG overload defs for {name}: {:?}", defs);
              for d in defs.iter() {
                let maybe_ty = self.interned_def_types.get(d).copied();
                if let Some(maybe_ty) = maybe_ty {
                  let disp = tti::TypeDisplay::new(&store, store.canon(maybe_ty));
                  eprintln!("DEBUG overload def {d:?} type {disp}");
                } else {
                  eprintln!("DEBUG overload def {d:?} type <none>");
                }
              }
            }
            if let Some(first) = defs.first().copied() {
              def_for_resolver = Some(first);
            }
            if defs.len() > 1 {
              if let Some(merged) = self.callable_overload_type_for_def(def, &store) {
                ty = Some(merged);
              }
            }
          }
          if ty.is_none() {
            ty = map_def_ty(self, &store, def);
          }
          if !is_owner {
            if let Some(def_data) = self.def_data.get(&def) {
              let def_body = self.body_of_def(def);
              let def_has_body = def_body.is_some();
              let same_body = def_body == Some(body_id);
              let needs_type = ty.is_none()
                || ty == Some(store.primitive_ids().unknown)
                || matches!(def_data.kind, DefKind::Import(_));
              let allow_body = matches!(
                def_data.kind,
                DefKind::Namespace(_) | DefKind::Module(_) | DefKind::Import(_)
              ) || (!same_body && def_has_body);
              if !nested_check && needs_type && (!def_has_body || allow_body) {
                match self.type_of_def(def) {
                  Ok(fresh) => {
                    let mapped = store.canon(fresh);
                    ty = Some(mapped);
                    self.interned_def_types.insert(def, mapped);
                  }
                  Err(FatalError::Cancelled) => return Err(FatalError::Cancelled),
                  Err(_) => {}
                }
              }
            }
          }
          if debug_overload {
            if let Some(current) = ty {
              eprintln!(
                "DEBUG overload binding computed ty {} for file {:?}",
                tti::TypeDisplay::new(&store, current),
                file
              );
            } else {
              eprintln!("DEBUG overload binding computed ty <none>");
            }
          }
        }
        if ty.is_none() {
          if binding.def.is_some() || binding.type_id.is_some() {
            ty = Some(prim.unknown);
          } else {
            if let Some(def) = def_for_resolver {
              binding_defs.insert(name.to_string(), def);
            }
            return Ok(());
          }
        }
        let ty = ty.unwrap_or_else(|| prim.unknown);
        let ty = match store.type_kind(ty) {
          tti::TypeKind::Callable { overloads } => {
            let mut merged = Vec::new();
            let mut seen = std::collections::HashSet::new();
            for sig_id in overloads.iter().copied() {
              if store.signature(sig_id).ret == prim.unknown {
                continue;
              }
              if seen.insert(sig_id) {
                merged.push(sig_id);
              }
            }
            if !merged.is_empty() && merged.len() < overloads.len() {
              store.canon(store.intern_type(tti::TypeKind::Callable { overloads: merged }))
            } else {
              ty
            }
          }
          _ => ty,
        };
        if debug_overload {
          eprintln!(
            "DEBUG overload binding final ty {} for file {:?}",
            tti::TypeDisplay::new(&store, ty),
            file
          );
        }
        let ty = if binding.def.is_some() {
          ty
        } else if let Some(existing) = bindings.get(name) {
          let existing_sigs = callable_signatures(store.as_ref(), *existing);
          let new_sigs = callable_signatures(store.as_ref(), ty);
          if !existing_sigs.is_empty() && !new_sigs.is_empty() {
            // Declaration order: earlier overload decls first (first-match resolution).
            let mut merged = Vec::new();
            let mut seen = std::collections::HashSet::new();
            for sig_id in existing_sigs.into_iter().chain(new_sigs) {
              if seen.insert(sig_id) {
                merged.push(sig_id);
              }
            }
            store.canon(store.intern_type(tti::TypeKind::Callable { overloads: merged }))
          } else {
            store.intersection(vec![*existing, ty])
          }
        } else {
          ty
        };
        bindings.insert(name.to_string(), ty);
        if let Some(def) = def_for_resolver {
          binding_defs.insert(name.to_string(), def);
        }
        Ok(())
      };
    for (name, binding) in file_binding_entries.into_iter() {
      let include_type = needed_root_names.contains(&name);
      bind(&name, &binding, include_type)?;
    }
    for (name, binding) in global_binding_entries.into_iter() {
      bind(&name, &binding, true)?;
    }

    if let Err(err) = self.collect_parent_bindings(body_id, &mut bindings, &mut binding_defs) {
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return Err(err);
    }
    // Nested `class` / `enum` / `interface` / `type` decls in *this* body are
    // in scope for type references in the same body (and nested checks that
    // reuse this resolver). Parent seeding alone misses `constructor() {
    // class Derived { m(x: Derived) {} } }` when the constructor body is
    // checked directly.
    {
      let mut seen: HashSet<String> = binding_defs.keys().cloned().collect();
      for stmt_id in body.root_stmts.iter().copied() {
        super::bindings::seed_type_decls_from_stmt(
          self,
          body,
          stmt_id,
          &mut binding_defs,
          &mut seen,
          None,
          false,
        );
      }
    }
    if let Err(err) = self.check_cancelled() {
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return Err(err);
    }

    for (name, def) in binding_defs.iter() {
      if self.type_stack.contains(def) {
        continue;
      }
      if let Some(def_data) = self.def_data.get(def) {
        if matches!(def_data.kind, DefKind::Import(_) | DefKind::ImportAlias(_)) {
          match self.type_of_def(*def) {
            Ok(def_ty) => {
              let ty = store.canon(def_ty);
              if std::env::var("DEBUG_OVERLOAD").is_ok() && name == "overload" {
                eprintln!(
                  "DEBUG overload import def type_of_def override {}",
                  tti::TypeDisplay::new(&store, ty)
                );
              }
              bindings.insert(name.clone(), ty);
            }
            Err(FatalError::Cancelled) => return Err(FatalError::Cancelled),
            Err(_) => {}
          }
        }
      }
    }

    let contextual_fn_ty = if matches!(meta.kind, HirBodyKind::Function) {
      if let Some(func_span) = self.function_expr_span(body_id) {
        self.contextual_callable_for_body(body_id, func_span, &store)?
      } else {
        None
      }
    } else {
      None
    };

    let prim = store.primitive_ids();
    let caches = self.checker_caches.for_body();
    for def in binding_defs.values() {
      if self.type_stack.contains(def) {
        continue;
      }
      if self.body_of_def(*def).is_none() && !self.interned_def_types.contains_key(def) {
        self.type_of_def(*def)?;
      }
    }
    let mut result = {
      let expander = RefExpander::new(
        Arc::clone(&store),
        &self.interned_def_types,
        &self.interned_type_params,
        &self.interned_type_param_decls,
        &self.interned_intrinsics,
        &self.interned_class_instances,
        &self.interned_enum_defs,
        caches.eval.clone(),
      );
      let ast_index = check::hir_body::AstIndex::new(ast.as_ref(), file, Some(&self.cancelled));
      let semantic_resolver = self.build_type_resolver(&binding_defs);
      let resolver = semantic_resolver.or_else(|| {
        if !binding_defs.is_empty() {
          Some(Arc::new(check::hir_body::BindingTypeResolver::new(
            binding_defs.clone(),
          )) as Arc<_>)
        } else {
          None
        }
      });
      let source_text = db::file_text(&self.typecheck_db, file);
      let jsdoc_source = matches!(
        self.file_kinds.get(&file),
        Some(FileKind::Js | FileKind::Jsx)
      )
      .then_some(source_text.as_ref());
      let class_expr_value_tys = {
        let mut tys = check::hir_body::class_expr_value_types_for_body(
          body,
          &self.interned_def_types,
          store.as_ref(),
          Some(&self.value_defs),
          None,
        );
        // Also seed class *declarations* by span: `this` in static/instance
        // members resolves through this span-keyed map when the body's scope
        // chain doesn't carry the file-level class binding
        // (`typeOfThisInStaticMembers.ts`).
        for def in lowered.defs.iter() {
          if def.path.kind != hir_js::DefKind::Class {
            continue;
          }
          let Some(value_def) = self.value_defs.get(&def.id).copied() else {
            continue;
          };
          let Some(candidate) = self.interned_def_types.get(&value_def).copied() else {
            continue;
          };
          if check::hir_body::type_has_construct_signature(store.as_ref(), candidate) {
            tys.insert(def.span, store.canon(candidate));
          }
        }
        tys
      };
      let mut result = check::hir_body::check_body_with_expander(
        body_id,
        body,
        &lowered.names,
        file,
        &ast_index,
        Arc::clone(&store),
        self.compiler_options.target,
        self.compiler_options.use_define_for_class_fields,
        self.compiler_options.strict_null_checks,
        self.compiler_options.strict_property_initialization,
        &caches,
        &bindings,
        resolver.clone(),
        Some(&expander),
        Some(&self.interned_type_param_decls),
        contextual_fn_ty,
        self.compiler_options.no_implicit_any,
        self.compiler_options.jsx,
        Some(&self.cancelled),
        jsdoc_source,
        Some(&lowered.types),
        &class_expr_value_tys,
        &self.expando_members,
      );
      let mut base_relate_hooks = relate_hooks();
      base_relate_hooks.expander = Some(&expander);
      base_relate_hooks.should_stop = Some(self.cancelled.as_ref());
      let relate = RelateCtx::with_hooks_and_cache(
        Arc::clone(&store),
        store.options(),
        base_relate_hooks,
        caches.relation.clone(),
      );
      if !body.exprs.is_empty() {
        if self.cancelled.load(Ordering::Relaxed) {
          if let Some(span) = span.take() {
            span.finish(None);
          }
          self.current_file = prev_file;
          return Err(FatalError::Cancelled);
        }
        let mut initial_env: HashMap<NameId, TypeId> = HashMap::new();
        if matches!(meta.kind, HirBodyKind::Function) {
          helpers::record_param_locals(body, &result.pat_types, prim.unknown, &mut initial_env);
        }
        let local_semantics = self.local_semantics.get(&file);
        let flow_bindings = local_semantics.map(|locals| FlowBindings::new(body, locals));
        for (idx, expr) in body.exprs.iter().enumerate() {
          if let hir_js::ExprKind::Ident(name_id) = expr.kind {
            if initial_env.contains_key(&name_id) {
              continue;
            }
            let Some(locals) = local_semantics else {
              continue;
            };
            let expr_id = hir_js::ExprId(idx as u32);
            // Prefer the precomputed flow binding table since it includes span-based fallbacks for
            // synthesized bodies (e.g. initializer bodies) where the exact expression span might
            // not match the locals binder key.
            let binding_id = flow_bindings
              .as_ref()
              .and_then(|bindings| bindings.binding_for_expr(expr_id))
              .or_else(|| locals.resolve_expr(body, expr_id));
            let Some(binding_id) = binding_id else {
              continue;
            };
            let symbol = locals.symbol(binding_id);
            if symbol.decl_scope != locals.root_scope() {
              continue;
            }
            if let Some(name) = lowered.names.resolve(name_id) {
              if let Some(ty) = bindings.get(name) {
                initial_env.insert(name_id, *ty);
              }
            }
          }
        }
        let mut flow_hooks = relate_hooks();
        flow_hooks.expander = Some(&expander);
        flow_hooks.should_stop = Some(self.cancelled.as_ref());
        let flow_relate = RelateCtx::with_hooks_and_cache(
          Arc::clone(&store),
          store.options(),
          flow_hooks,
          caches.relation.clone(),
        );
        let mut pinned_foreign = Vec::new();
        let type_aliases =
          helpers::da_type_alias_map_with_imports(self, file, &lowered, &mut pinned_foreign);
        let private_in_targets = {
          let body_span = if body.span.start < body.span.end {
            body.span
          } else {
            TextRange::new(
              body.stmts.first().map(|s| s.span.start).unwrap_or(0),
              body.stmts.last().map(|s| s.span.end).unwrap_or(0),
            )
          };
          check::hir_body::build_private_in_targets(&ast_index, body_span, |class_idx| {
            let name = ast_index.classes.get(class_idx)?.name.as_ref()?;
            let value_ty = *bindings.get(name)?;
            let instance = match store.type_kind(value_ty) {
              tti::TypeKind::Object(obj_id) => {
                let shape = store.shape(store.object(obj_id).shape);
                shape
                  .construct_signatures
                  .first()
                  .map(|sig| store.signature(*sig).ret)
              }
              tti::TypeKind::Callable { overloads } => {
                overloads.first().map(|sig| store.signature(*sig).ret)
              }
              _ => None,
            }?;
            Some((instance, value_ty))
          })
        };
        let flow_result = check::hir_body::check_body_with_env_with_bindings(
          body_id,
          body,
          &lowered.names,
          file,
          "",
          Arc::clone(&store),
          &initial_env,
          flow_bindings.as_ref(),
          flow_relate,
          Some(&expander),
          lowered.type_arenas(body.owner),
          Some(&type_aliases),
          private_in_targets,
          resolver.clone(),
          self.compiler_options.no_implicit_any,
        );
        if std::env::var("DEBUG_OVERLOAD").is_ok() {
          for (idx, expr) in body.exprs.iter().enumerate() {
            if let hir_js::ExprKind::Ident(name_id) = expr.kind {
              if lowered.names.resolve(name_id) == Some("overload") {
                let base_ty = result.expr_types.get(idx).copied().unwrap_or(prim.unknown);
                let flow_ty = flow_result
                  .expr_types
                  .get(idx)
                  .copied()
                  .unwrap_or(prim.unknown);
                eprintln!(
                  "DEBUG overload expr idx {idx} base {} flow {}",
                  tti::TypeDisplay::new(&store, base_ty),
                  tti::TypeDisplay::new(&store, flow_ty)
                );
              }
            }
          }
        }
        let widen_literal = |ty: TypeId| match store.type_kind(ty) {
          tti::TypeKind::NumberLiteral(_) => prim.number,
          tti::TypeKind::StringLiteral(_) => prim.string,
          tti::TypeKind::BooleanLiteral(_) => prim.boolean,
          tti::TypeKind::BigIntLiteral(_) => prim.bigint,
          _ => ty,
        };
        if flow_result.expr_types.len() == result.expr_types.len() {
          for (idx, ty) in flow_result.expr_types.iter().enumerate() {
            if *ty != prim.unknown {
              let existing = result.expr_types[idx];
              if matches!(body.exprs[idx].kind, hir_js::ExprKind::Ident(_)) {
                let flow_literal_on_primitive = matches!(
                  (store.type_kind(existing), store.type_kind(*ty)),
                  (tti::TypeKind::Number, tti::TypeKind::NumberLiteral(_))
                    | (tti::TypeKind::String, tti::TypeKind::StringLiteral(_))
                    | (tti::TypeKind::Boolean, tti::TypeKind::BooleanLiteral(_))
                    | (tti::TypeKind::BigInt, tti::TypeKind::BigIntLiteral(_))
                );
                if existing == prim.unknown || !flow_literal_on_primitive {
                  result.expr_types[idx] = *ty;
                }
                continue;
              }
              let narrower =
                relate.is_assignable(*ty, existing) && !relate.is_assignable(existing, *ty);
              let flow_literal_on_primitive = matches!(
                (store.type_kind(existing), store.type_kind(*ty)),
                (tti::TypeKind::Number, tti::TypeKind::NumberLiteral(_))
                  | (tti::TypeKind::String, tti::TypeKind::StringLiteral(_))
                  | (tti::TypeKind::Boolean, tti::TypeKind::BooleanLiteral(_))
                  | (tti::TypeKind::BigInt, tti::TypeKind::BigIntLiteral(_))
              );
              if existing == prim.unknown || (narrower && !flow_literal_on_primitive) {
                result.expr_types[idx] = *ty;
              }
            }
          }
        }
        if flow_result.pat_types.len() == result.pat_types.len() {
          for (idx, ty) in flow_result.pat_types.iter().enumerate() {
            if *ty != prim.unknown {
              let existing = result.pat_types[idx];
              let narrower =
                relate.is_assignable(*ty, existing) && !relate.is_assignable(existing, *ty);
              let flow_literal_on_primitive = matches!(
                (store.type_kind(existing), store.type_kind(*ty)),
                (tti::TypeKind::Number, tti::TypeKind::NumberLiteral(_))
                  | (tti::TypeKind::String, tti::TypeKind::StringLiteral(_))
                  | (tti::TypeKind::Boolean, tti::TypeKind::BooleanLiteral(_))
                  | (tti::TypeKind::BigInt, tti::TypeKind::BigIntLiteral(_))
              );
              if existing == prim.unknown || (narrower && !flow_literal_on_primitive) {
                result.pat_types[idx] = *ty;
              }
            }
          }
        }
        let flow_return_types: Vec<_> = flow_result
          .return_types
          .into_iter()
          .map(widen_literal)
          .collect();
        if result.return_types.is_empty() && !flow_return_types.is_empty() {
          result.return_types = flow_return_types;
        } else if flow_return_types.len() == result.return_types.len() {
          for (idx, ty) in flow_return_types.iter().enumerate() {
            if *ty != prim.unknown {
              let existing = result.return_types[idx];
              let narrower =
                relate.is_assignable(*ty, existing) && !relate.is_assignable(existing, *ty);
              if existing == prim.unknown || narrower {
                result.return_types[idx] = *ty;
              }
            }
          }
        }
        if !result.return_types.is_empty() {
          result.return_types = result
            .return_types
            .iter()
            .map(|ty| widen_literal(*ty))
            .collect();
        }
        let mut flow_diagnostics = flow_result.diagnostics;
        if !flow_diagnostics.is_empty() {
          let mut seen: HashSet<(String, FileId, TextRange, String)> = HashSet::new();
          let diag_key = |diag: &Diagnostic| -> (String, FileId, TextRange, String) {
            (
              diag.code.as_str().to_string(),
              diag.primary.file,
              diag.primary.range,
              diag.message.clone(),
            )
          };
          for diag in result.diagnostics.iter() {
            seen.insert(diag_key(diag));
          }
          flow_diagnostics.sort_by(|a, b| {
            a.primary
              .file
              .cmp(&b.primary.file)
              .then(a.primary.range.start.cmp(&b.primary.range.start))
              .then(a.primary.range.end.cmp(&b.primary.range.end))
              .then(a.code.cmp(&b.code))
              .then(a.message.cmp(&b.message))
          });
          for diag in flow_diagnostics.into_iter() {
            if seen.insert(diag_key(&diag)) {
              result.diagnostics.push(diag);
            }
          }
        }
      }
      result
    };
    {
      let expander = RefExpander::new(
        Arc::clone(&store),
        &self.interned_def_types,
        &self.interned_type_params,
        &self.interned_type_param_decls,
        &self.interned_intrinsics,
        &self.interned_class_instances,
        &self.interned_enum_defs,
        caches.eval.clone(),
      );
      for (idx, expr) in body.exprs.iter().enumerate() {
        let hir_js::ExprKind::Member(mem) = &expr.kind else {
          continue;
        };
        let current = result.expr_types.get(idx).copied().unwrap_or(prim.unknown);
        let current_unknown = !store.contains_type_id(current)
          || matches!(store.type_kind(current), tti::TypeKind::Unknown);
        if !current_unknown {
          continue;
        }
        let Some(key) = (match &mem.property {
          hir_js::ObjectKey::Ident(id) => lowered.names.resolve(*id).map(|s| s.to_string()),
          hir_js::ObjectKey::String(s) => Some(s.clone()),
          hir_js::ObjectKey::Number(n) => Some(n.clone()),
          hir_js::ObjectKey::Computed(_) => None,
        }) else {
          continue;
        };
        let base_ty = result
          .expr_types
          .get(mem.object.0 as usize)
          .copied()
          .unwrap_or(prim.unknown);
        let Some(prop_ty) =
          lookup_interned_property_type(store.as_ref(), Some(&expander), base_ty, &key)
        else {
          continue;
        };
        let ty = if mem.optional {
          store.union(vec![prop_ty, prim.undefined])
        } else {
          prop_ty
        };
        if let Some(slot) = result.expr_types.get_mut(idx) {
          *slot = ty;
        }
      }
    }
    let mut updated_callees: Vec<(hir_js::ExprId, TypeId)> = Vec::new();
    for (idx, expr) in body.exprs.iter().enumerate() {
      if let hir_js::ExprKind::Ident(name_id) = expr.kind {
        if let Some(name) = lowered.names.resolve(name_id) {
          let current = result.expr_types.get(idx).copied().unwrap_or(prim.unknown);
          let current_is_unknown = current == prim.unknown
            || (store.contains_type_id(current)
              && matches!(store.type_kind(current), tti::TypeKind::Unknown));
          let mut ty = bindings.get(name).copied();
          if ty.is_none() {
            if let Some(def) = binding_defs.get(name) {
              ty = map_def_ty(self, &store, *def);
            }
          } else if ty == Some(prim.unknown) {
            if let Some(def) = binding_defs.get(name) {
              if let Some(mapped) = map_def_ty(self, &store, *def) {
                ty = Some(mapped);
              }
            } else {
              ty = None;
            }
          }
          if current_is_unknown {
            if let Some(ty) = ty {
              if ty == prim.unknown {
                continue;
              }
              result.expr_types[idx] = ty;
              updated_callees.push((hir_js::ExprId(idx as u32), ty));
            }
          }
        }
      }
      if let Err(err) = self.check_cancelled() {
        if let Some(span) = span.take() {
          span.finish(None);
        }
        self.current_file = prev_file;
        return Err(err);
      }
    }
    if !updated_callees.is_empty() {
      let expander = RefExpander::new(
        Arc::clone(&store),
        &self.interned_def_types,
        &self.interned_type_params,
        &self.interned_type_param_decls,
        &self.interned_intrinsics,
        &self.interned_class_instances,
        &self.interned_enum_defs,
        caches.eval.clone(),
      );
      let mut base_relate_hooks = relate_hooks();
      base_relate_hooks.expander = Some(&expander);
      base_relate_hooks.should_stop = Some(self.cancelled.as_ref());
      let relate = RelateCtx::with_hooks_and_cache(
        Arc::clone(&store),
        store.options(),
        base_relate_hooks,
        caches.relation.clone(),
      );
      for (call_idx, expr) in body.exprs.iter().enumerate() {
        let hir_js::ExprKind::Call(call) = &expr.kind else {
          continue;
        };
        if let Some((_, callee_ty)) = updated_callees
          .iter()
          .find(|(callee, _)| *callee == call.callee)
        {
          let arg_tys: Vec<CallArgType> = call
            .args
            .iter()
            .map(|arg| {
              let ty = result.expr_types[arg.expr.0 as usize];
              let arg_span = result
                .expr_spans
                .get(arg.expr.0 as usize)
                .copied()
                .map(|range| Span::new(file, range));
              let base = if arg.spread {
                CallArgType::spread(ty)
              } else {
                CallArgType::new(ty)
              };
              match arg_span {
                Some(span) => base.with_span(span),
                None => base,
              }
            })
            .collect();
          let this_arg = match &body.exprs[call.callee.0 as usize].kind {
            hir_js::ExprKind::Member(mem) => Some(result.expr_types[mem.object.0 as usize]),
            _ => None,
          };
          let span = Span::new(
            file,
            result
              .expr_spans
              .get(call_idx)
              .copied()
              .unwrap_or(TextRange::new(0, 0)),
          );
          let resolution = if call.is_new {
            resolve_construct(
              &store,
              &relate,
              &caches.instantiation,
              *callee_ty,
              &arg_tys,
              None,
              None,
              None,
              span,
              None,
            )
          } else {
            resolve_call(
              &store,
              &relate,
              &caches.instantiation,
              *callee_ty,
              &arg_tys,
              None,
              this_arg,
              None,
              span,
              None,
            )
          };
          let mut ret_ty = resolution.return_type;
          if call.optional {
            ret_ty = store.union(vec![ret_ty, prim.undefined]);
          }
          result.expr_types[call_idx] = ret_ty;
          if resolution.diagnostics.is_empty() {
            result.diagnostics.retain(|diag| {
              let is_no_match = diag.code.as_str() == codes::NO_OVERLOAD.id
                || diag.code.as_str() == codes::NO_OVERLOAD_MATCHES.id;
              !(diag.primary.file == span.file
                && diag.primary.range.start >= span.range.start
                && diag.primary.range.end <= span.range.end
                && is_no_match)
            });
          } else {
            result.diagnostics.extend(resolution.diagnostics);
          }
        }
      }
    }
    let prop_relate = RelateCtx::new(Arc::clone(&store), store.options());
    for (idx, expr) in body.exprs.iter().enumerate() {
      if result.expr_types[idx] == prim.unknown {
        match &expr.kind {
          hir_js::ExprKind::Ident(name_id) => {
            if let Some(name) = lowered.names.resolve(*name_id) {
              if let Some(def) = binding_defs.get(name) {
                if let Ok(def_ty) = self.type_of_def(*def) {
                  result.expr_types[idx] = store.canon(def_ty);
                }
              }
            }
          }
          hir_js::ExprKind::Member(mem) => {
            let obj_ty = result.expr_types[mem.object.0 as usize];
            if obj_ty != prim.unknown {
              let prop_name = match &mem.property {
                hir_js::ObjectKey::Ident(id) => lowered.names.resolve(*id).map(str::to_string),
                hir_js::ObjectKey::String(s) => Some(s.clone()),
                hir_js::ObjectKey::Number(n) => Some(n.clone()),
                hir_js::ObjectKey::Computed(prop) => {
                  if let hir_js::ExprKind::Literal(hir_js::Literal::String(s)) =
                    &body.exprs[prop.0 as usize].kind
                  {
                    Some(s.lossy.clone())
                  } else {
                    None
                  }
                }
              };
              if let Some(name) = prop_name {
                if let Some(prop_ty) = helpers::prop_type(store.as_ref(), obj_ty, &name) {
                  let existing = result.expr_types[idx];
                  let narrower = prop_relate.is_assignable(prop_ty, existing)
                    && !prop_relate.is_assignable(existing, prop_ty);
                  if existing == prim.unknown || narrower {
                    result.expr_types[idx] = prop_ty;
                  }
                }
              }
            }
          }
          _ => {}
        }
      }
    }
    let res = Arc::new(result);
    if matches!(self.compiler_options.cache.mode, CacheMode::PerBody) {
      let mut stats = caches.stats();
      if stats.relation.evictions == 0 {
        let max = self.compiler_options.cache.max_relation_cache_entries as u64;
        if max > 0 && stats.relation.insertions > max {
          stats.relation.evictions = stats.relation.insertions - max;
        } else {
          stats.relation.evictions = 1;
        }
      }
      self.cache_stats.merge(&stats);
    }
    self.local_body_results.insert(body_id, res.clone());
    if let Some(span) = span.take() {
      span.finish(None);
    }
    self.current_file = prev_file;
    Ok(res)
  }
}
