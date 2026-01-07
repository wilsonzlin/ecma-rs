use super::*;

impl ProgramState {
  pub(super) fn ensure_analyzed(&mut self, host: &Arc<dyn Host>, roots: &[FileKey]) {
    if let Err(fatal) = self.ensure_analyzed_result(host, roots) {
      self.diagnostics.push(fatal_to_diagnostic(fatal));
    }
  }

  pub(super) fn ensure_analyzed_result(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileKey],
  ) -> Result<(), FatalError> {
    if self.analyzed {
      return Ok(());
    }
    self.check_cancelled()?;
    self.module_namespace_types.clear();
    self.module_namespace_in_progress.clear();
    let libs = self.collect_libraries(host.as_ref(), roots)?;
    self.check_cancelled()?;
    let mut lib_queue = VecDeque::new();
    self.process_libs(&libs, host, &mut lib_queue)?;

    fn type_package_fallback_specifier(name: &str) -> Option<String> {
      if name.starts_with("@types/") {
        return None;
      }

      // Match TypeScript's scoped package mapping for `@types`:
      // `@scope/pkg` -> `@types/scope__pkg`.
      let mapped = if let Some(stripped) = name.strip_prefix('@') {
        stripped.replace('/', "__")
      } else {
        name.to_string()
      };
      Some(format!("@types/{mapped}"))
    }

    fn record_type_package_resolution(
      state: &mut ProgramState,
      from: FileId,
      specifier: &str,
      host: &Arc<dyn Host>,
    ) -> Option<FileId> {
      if let Some(target) = state.record_module_resolution(from, specifier, host) {
        return Some(target);
      }
      let fallback = type_package_fallback_specifier(specifier)?;
      let Some(target) = state.record_module_resolution(from, &fallback, host) else {
        return None;
      };
      // Treat the resolved `@types/*` package as satisfying the original
      // specifier so downstream module graph queries see the dependency.
      state
        .typecheck_db
        .set_module_resolution_ref(from, specifier, Some(target));
      Some(target)
    }

    let mut root_keys: Vec<FileKey> = roots.to_vec();
    let mut root_ids: Vec<FileId> = roots
      .iter()
      .map(|key| self.intern_file_key(key.clone(), FileOrigin::Source))
      .collect();

    let mut type_packages = self.compiler_options.types.clone();
    type_packages.sort();
    type_packages.dedup();

    if !type_packages.is_empty() {
      let primary = if let Some(base_root) = roots.first() {
        let file_id = self.intern_file_key(base_root.clone(), FileOrigin::Source);
        Span::new(file_id, TextRange::new(0, 0))
      } else {
        Span::new(FileId(u32::MAX), TextRange::new(0, 0))
      };

      if let Some(base_root) = roots.first() {
        for name in type_packages.iter() {
          self.check_cancelled()?;
          let resolved = host.resolve(base_root, name).or_else(|| {
            type_package_fallback_specifier(name).and_then(|spec| host.resolve(base_root, &spec))
          });
          if let Some(key) = resolved {
            root_keys.push(key.clone());
            root_ids.push(self.intern_file_key(key, FileOrigin::Source));
          } else {
            self.push_program_diagnostic(
              codes::UNRESOLVED_MODULE
                .error(format!("cannot resolve type package \"{name}\""), primary),
            );
          }
        }
      } else {
        for name in type_packages.iter() {
          self.push_program_diagnostic(
            codes::UNRESOLVED_MODULE
              .error(format!("cannot resolve type package \"{name}\""), primary),
          );
        }
      }
    }

    root_keys.sort_unstable_by(|a, b| a.as_str().cmp(b.as_str()));
    root_keys.dedup_by(|a, b| a.as_str() == b.as_str());
    root_ids.sort_unstable_by_key(|id| id.0);
    root_ids.dedup();
    self.root_ids = root_ids;
    self
      .typecheck_db
      .set_roots(Arc::<[FileKey]>::from(root_keys));
    let mut queue: VecDeque<FileId> = self.root_ids.iter().copied().collect();
    queue.extend(lib_queue);
    if !self.compiler_options.types.is_empty() && !self.root_ids.is_empty() {
      let root_ids = self.root_ids.clone();
      let mut type_names = self.compiler_options.types.clone();
      type_names.sort();
      type_names.dedup();
      for name in type_names {
        self.check_cancelled()?;
        let mut resolved_any = false;
        for root in root_ids.iter().copied() {
          if let Some(target) = record_type_package_resolution(self, root, name.as_str(), host) {
            resolved_any = true;
            queue.push_back(target);
          }
        }
        if !resolved_any {
          let primary_file = self.root_ids.first().copied().unwrap_or(FileId(u32::MAX));
          self.push_program_diagnostic(codes::UNRESOLVED_MODULE.error(
            format!("unresolved type package \"{name}\""),
            Span::new(primary_file, TextRange::new(0, 0)),
          ));
        }
      }
    }
    let mut seen: AHashSet<FileId> = AHashSet::new();
    while let Some(file) = queue.pop_front() {
      self.check_cancelled()?;
      let prev_file = self.current_file;
      self.current_file = Some(file);
      if !seen.insert(file) || self.lib_file_ids.contains(&file) {
        self.current_file = prev_file;
        continue;
      }
      let Some(file_key) = self.file_key_for_id(file) else {
        self.current_file = prev_file;
        continue;
      };
      self
        .file_kinds
        .entry(file)
        .or_insert_with(|| host.file_kind(&file_key));
      let file_kind = *self.file_kinds.get(&file).unwrap_or(&FileKind::Ts);
      let text = self.load_text(file, host)?;
      self.check_cancelled()?;
      let directives = scan_triple_slash_directives(text.as_ref());
      let mut triple_slash_types: Vec<&str> = Vec::new();
      for reference in directives.references.iter() {
        let value = reference.value(text.as_ref());
        if value.is_empty() {
          continue;
        }
        match reference.kind {
          TripleSlashReferenceKind::Lib => {
            if let Some(lib_file) =
              crate::lib_support::lib_env::bundled_lib_file_by_option_name(value)
            {
              self.process_libs(std::slice::from_ref(&lib_file), host, &mut queue)?;
            } else {
              self.push_program_diagnostic(codes::LIB_DEFINITION_FILE_NOT_FOUND.error(
                format!("cannot find lib definition file for \"{value}\""),
                Span::new(file, reference.value_range),
              ));
            }
          }
          TripleSlashReferenceKind::Path => {
            let normalized = normalize_reference_path_specifier(value);
            if let Some(target) = self.record_module_resolution(file, normalized.as_ref(), host) {
              queue.push_back(target);
            } else {
              self.push_program_diagnostic(codes::FILE_NOT_FOUND.error(
                format!("file \"{}\" not found", normalized.as_ref()),
                Span::new(file, reference.value_range),
              ));
            }
          }
          TripleSlashReferenceKind::Types => {
            triple_slash_types.push(value);
            if let Some(target) = record_type_package_resolution(self, file, value, host) {
              queue.push_back(target);
            } else {
              self.push_program_diagnostic(codes::TYPE_DEFINITION_FILE_NOT_FOUND.error(
                format!("cannot find type definition file for \"{value}\""),
                Span::new(file, reference.value_range),
              ));
            }
          }
        }
      }
      let parse_span = QuerySpan::enter(
        QueryKind::Parse,
        query_span!(
          "typecheck_ts.parse",
          Some(file.0),
          Option::<u32>::None,
          Option::<u32>::None,
          false
        ),
        None,
        false,
        Some(self.query_stats.clone()),
      );
      let parsed = self.parse_via_salsa(file, file_kind, Arc::clone(&text));
      if let Some(span) = parse_span {
        span.finish(None);
      }
      self.check_cancelled()?;

      // Keep the host module resolution edges in sync with the current set of
      // module specifiers in the file. This avoids accumulating stale edges
      // once program edits become incremental (without recreating the salsa DB)
      // and keeps serialized snapshots consistent with the current module graph.
      let current_specifiers = db::module_specifiers(&self.typecheck_db, file);
      let is_root = self.root_ids.contains(&file);
      let mut keep_specifiers: AHashSet<&str> = AHashSet::new();
      for specifier in current_specifiers.iter() {
        keep_specifiers.insert(specifier.as_ref());
      }
      if is_root {
        for specifier in type_packages.iter() {
          keep_specifiers.insert(specifier.as_str());
        }
      }
      self
        .typecheck_db
        .retain_module_resolutions_for_file(file, |specifier| keep_specifiers.contains(specifier));

      let mut type_package_specifiers: AHashSet<&str> = AHashSet::new();
      for specifier in triple_slash_types.iter().copied() {
        type_package_specifiers.insert(specifier);
      }
      if is_root {
        for specifier in type_packages.iter() {
          type_package_specifiers.insert(specifier.as_str());
        }
      }

      for specifier in current_specifiers.iter() {
        self.check_cancelled()?;
        let specifier = specifier.as_ref();
        let target = if type_package_specifiers.contains(specifier) {
          record_type_package_resolution(self, file, specifier, host)
        } else {
          self.record_module_resolution(file, specifier, host)
        };
        if let Some(target) = target {
          queue.push_back(target);
        }
      }
      if is_root {
        for specifier in type_packages.iter() {
          self.check_cancelled()?;
          if let Some(target) = record_type_package_resolution(self, file, specifier.as_str(), host)
          {
            queue.push_back(target);
          }
        }
      }

      match parsed {
        Ok(ast) => {
          let (locals, _) = sem_ts::locals::bind_ts_locals_tables(ast.as_ref(), file);
          self.local_semantics.insert(file, locals);
          self.asts.insert(file, Arc::clone(&ast));
          self.queue_type_imports_in_ast(file, ast.as_ref(), host, &mut queue);
          let lower_span = QuerySpan::enter(
            QueryKind::LowerHir,
            query_span!(
              "typecheck_ts.lower_hir",
              Some(file.0),
              Option::<u32>::None,
              Option::<u32>::None,
              false
            ),
            None,
            false,
            Some(self.query_stats.clone()),
          );
          let lowered = db::lower_hir(&self.typecheck_db, file);
          let Some(lowered) = lowered.lowered else {
            if let Some(span) = lower_span {
              span.finish(None);
            }
            continue;
          };
          self.hir_lowered.insert(file, Arc::clone(&lowered));
          let _bound_sem_hir = self.bind_file(file, ast.as_ref(), host, &mut queue);
          let _ = self.align_definitions_with_hir(file, lowered.as_ref());
          self.map_hir_bodies(file, lowered.as_ref());
          self.check_cancelled()?;
          if let Some(span) = lower_span {
            span.finish(None);
          }
        }
        Err(err) => {
          let _ = err;
        }
      }
      self.current_file = prev_file;
    }
    if !self.hir_lowered.is_empty() {
      self.check_cancelled()?;
      let ts_semantics = db::ts_semantics(&self.typecheck_db);
      self.check_cancelled()?;
      self.semantics = Some(Arc::clone(&ts_semantics.semantics));
      self.extend_symbol_to_def_with_semantic_ids();
      self.push_semantic_diagnostics(ts_semantics.diagnostics.as_ref().clone());
      self.check_export_assignments_in_esm();
      self.check_import_assignment_requires();
      self.check_required_global_types();
    }
    self.check_cancelled()?;
    self.resolve_reexports();
    self.rebuild_callable_overloads();
    self.recompute_global_bindings();
    self.rebuild_namespace_member_index()?;
    self.rebuild_body_owners();
    self.analyzed = true;
    Ok(())
  }

  fn collect_libraries(
    &mut self,
    host: &dyn Host,
    roots: &[FileKey],
  ) -> Result<Vec<LibFile>, FatalError> {
    let mut options = self
      .compiler_options_override
      .clone()
      .unwrap_or_else(|| host.compiler_options());
    if !options.no_default_lib && options.libs.is_empty() && !roots.is_empty() {
      for key in roots {
        let text = if let Some(text) = self.file_overrides.get(key) {
          Arc::clone(text)
        } else {
          host.file_text(key)?
        };
        if scan_triple_slash_directives(text.as_ref()).no_default_lib {
          options.no_default_lib = true;
          break;
        }
      }
    }

    self.compiler_options = options.clone();
    self.checker_caches = CheckerCaches::new(options.cache.clone());
    self.cache_stats = CheckerCacheStats::default();
    self.typecheck_db.set_compiler_options(options.clone());
    self
      .typecheck_db
      .set_cancellation_flag(self.cancelled.clone());
    let libs = collect_libs(&options, host.lib_files(), &self.lib_manager);
    if libs.is_empty() && options.no_default_lib {
      self.lib_diagnostics.clear();
      return Ok(Vec::new());
    }
    let validated = validate_libs(libs, |lib| {
      self.intern_file_key(lib.key.clone(), FileOrigin::Lib)
    });
    self.lib_diagnostics = validated.diagnostics.clone();

    let mut dts_libs = Vec::new();
    for (lib, file_id) in validated.libs.into_iter() {
      self.file_kinds.insert(file_id, FileKind::Dts);
      dts_libs.push(lib);
    }

    Ok(dts_libs)
  }

  fn process_libs(
    &mut self,
    libs: &[LibFile],
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) -> Result<(), FatalError> {
    let mut pending: VecDeque<LibFile> = libs.iter().cloned().collect();
    while let Some(lib) = pending.pop_front() {
      self.check_cancelled()?;
      let file_id = self.intern_file_key(lib.key.clone(), FileOrigin::Lib);
      if self.lib_texts.contains_key(&file_id) {
        continue;
      }
      self.file_kinds.insert(file_id, FileKind::Dts);
      self.lib_texts.insert(file_id, lib.text.clone());

      let directives = scan_triple_slash_directives(lib.text.as_ref());
      for reference in directives.references.iter() {
        let value = reference.value(lib.text.as_ref());
        if value.is_empty() {
          continue;
        }
        match reference.kind {
          TripleSlashReferenceKind::Lib => {
            if let Some(lib_file) =
              crate::lib_support::lib_env::bundled_lib_file_by_option_name(value)
            {
              let lib_id = self.intern_file_key(lib_file.key.clone(), FileOrigin::Lib);
              if !self.lib_texts.contains_key(&lib_id) {
                pending.push_back(lib_file);
              }
            } else {
              self.push_program_diagnostic(codes::LIB_DEFINITION_FILE_NOT_FOUND.error(
                format!("cannot find lib definition file for \"{value}\""),
                Span::new(file_id, reference.value_range),
              ));
            }
          }
          TripleSlashReferenceKind::Path => {
            let normalized = normalize_reference_path_specifier(value);
            if let Some(target) = self.record_module_resolution(file_id, normalized.as_ref(), host)
            {
              queue.push_back(target);
            } else {
              self.push_program_diagnostic(codes::FILE_NOT_FOUND.error(
                format!("file \"{}\" not found", normalized.as_ref()),
                Span::new(file_id, reference.value_range),
              ));
            }
          }
          TripleSlashReferenceKind::Types => {
            if let Some(target) = self.record_module_resolution(file_id, value, host) {
              queue.push_back(target);
            } else {
              self.push_program_diagnostic(codes::TYPE_DEFINITION_FILE_NOT_FOUND.error(
                format!("cannot find type definition file for \"{value}\""),
                Span::new(file_id, reference.value_range),
              ));
            }
          }
        }
      }

      let parsed = self.parse_via_salsa(file_id, FileKind::Dts, Arc::clone(&lib.text));
      match parsed {
        Ok(ast) => {
          self.check_cancelled()?;
          let (locals, _) = sem_ts::locals::bind_ts_locals_tables(ast.as_ref(), file_id);
          self.local_semantics.insert(file_id, locals);
          self.asts.insert(file_id, Arc::clone(&ast));
          self.queue_type_imports_in_ast(file_id, ast.as_ref(), host, queue);
          let lowered = db::lower_hir(&self.typecheck_db, file_id);
          let Some(lowered) = lowered.lowered else {
            continue;
          };
          self.hir_lowered.insert(file_id, Arc::clone(&lowered));
          let _bound_sem_hir = self.bind_file(file_id, ast.as_ref(), host, queue);
          let _ = self.align_definitions_with_hir(file_id, lowered.as_ref());
          self.map_hir_bodies(file_id, lowered.as_ref());
        }
        Err(err) => {
          let _ = err;
        }
      }
    }
    Ok(())
  }

  /// Remap bound definitions to the stable IDs produced by HIR lowering while
  /// preserving existing symbols and cached types.
  ///
  /// The binder allocates definitions sequentially, but HIR uses content-derived
  /// identifiers that stay stable across edits. Re-aligning keeps
  /// `definitions_in_file`, `expr_at`, and `type_of_def` working across repeated
  /// checks and avoids dropping cached type information when files are
  /// re-lowered.
  fn align_definitions_with_hir(
    &mut self,
    file: FileId,
    lowered: &LowerResult,
  ) -> HashMap<DefId, DefId> {
    let is_file_level_binding = |def: &hir_js::DefData| -> bool {
      if def.in_global {
        // `declare global { ... }` members are injected into the program-wide
        // global scope but do not create file/module bindings.
        return false;
      }

      // `hir-js` models variable declarations as a `VarDeclarator` container
      // owning the initializer body plus one or more `Var` children for the
      // bindings. Treat those `Var` defs as top-level when the declarator
      // itself is top-level.
      let mut parent = def.parent;
      while let Some(parent_id) = parent {
        let Some(parent_def) = lowered.def(parent_id) else {
          return false;
        };
        if matches!(parent_def.path.kind, HirDefKind::VarDeclarator) {
          parent = parent_def.parent;
          continue;
        }
        return false;
      }

      matches!(
        def.path.kind,
        HirDefKind::Var
          | HirDefKind::Function
          | HirDefKind::Class
          | HirDefKind::Enum
          | HirDefKind::Namespace
          | HirDefKind::Module
          | HirDefKind::ImportBinding
          | HirDefKind::Interface
          | HirDefKind::TypeAlias
          | HirDefKind::ExportAlias
      )
    };

    let file_def_ids: HashSet<_> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file == file)
      .map(|(id, _)| *id)
      .collect();
    let mut by_name_kind: HashMap<(String, DefMatchKind), Vec<(DefId, DefData)>> = HashMap::new();
    for (id, data) in self.def_data.iter() {
      if data.file != file {
        continue;
      }
      by_name_kind
        .entry((data.name.clone(), match_kind_from_def(&data.kind)))
        .or_default()
        .push((*id, data.clone()));
    }
    for defs in by_name_kind.values_mut() {
      defs.sort_by_key(|(_, data)| (data.span.start, data.span.end));
    }

    let mut new_def_data: HashMap<DefId, DefData> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file != file)
      .map(|(id, data)| (*id, data.clone()))
      .collect();
    let mut new_def_types: HashMap<DefId, TypeId> = self
      .def_types
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, ty)| (*id, *ty))
      .collect();
    let mut new_interned_def_types: HashMap<DefId, tti::TypeId> = self
      .interned_def_types
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, ty)| (*id, *ty))
      .collect();
    let mut new_interned_type_params: HashMap<DefId, Vec<TypeParamId>> = self
      .interned_type_params
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, params)| (*id, params.clone()))
      .collect();
    let mut new_interned_type_param_decls: HashMap<DefId, Arc<[tti::TypeParamDecl]>> = self
      .interned_type_param_decls
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, decls)| (*id, Arc::clone(decls)))
      .collect();
    let mut id_mapping: HashMap<DefId, DefId> = HashMap::new();

    let Some(file_state) = self.files.get(&file).cloned() else {
      return HashMap::new();
    };
    let mut resolved_defs = Vec::new();
    let mut bindings = file_state.bindings.clone();
    let mut exports = file_state.exports.clone();
    let reexports = file_state.reexports.clone();
    let export_all = file_state.export_all.clone();

    // `hir-js` definition order is not guaranteed to match source order (IDs
    // are content-derived). Align by spans to keep stable IDs wired to the
    // correct bound declaration when multiple defs share a name (e.g. globals
    // vs ambient modules).
    let mut lowered_defs: Vec<_> = lowered.defs.iter().collect();
    lowered_defs.sort_by_key(|def| (def.span.start, def.span.end, def.id.0));
    for def in lowered_defs {
      let raw_name = lowered
        .names
        .resolve(def.name)
        .unwrap_or_default()
        .to_string();
      // `hir-js` emits `VarDeclarator` defs as a container for the declaration
      // itself, alongside `Var` defs for the bound identifiers. Keep the
      // declarator defs addressable by ID, but avoid treating them as the named
      // binding to keep `definitions_in_file` name-based queries focused on
      // actual bindings.
      let is_var_declarator = def.path.kind == HirDefKind::VarDeclarator;
      let name = if is_var_declarator {
        format!("<var_decl:{raw_name}>")
      } else {
        raw_name.clone()
      };
      let match_kind = match_kind_from_hir(def.path.kind);
      // `hir-js` models variable declarations as a `VarDeclarator` node that owns the initializer
      // body plus one or more child `Var` defs for the bindings (to support destructuring).
      //
      // Track `VarDeclarator` as a definition for stable IDs, but do not treat it as a symbol in
      // any namespace or allow it to clobber the real `Var` binding in `bindings`/`exports`.
      let is_var_declarator = matches!(match_kind, DefMatchKind::VarDeclarator);
      let matched = by_name_kind
        .get_mut(&(name.clone(), match_kind))
        .and_then(|list| {
          if list.is_empty() {
            None
          } else {
            Some(list.remove(0))
          }
        });
      let (def_id, data) = if let Some((old_id, mut data)) = matched {
        id_mapping.insert(old_id, def.id);
        data.span = def.span;
        data.export = data.export || def.is_exported || def.is_default_export;
        if is_var_declarator {
          data.export = false;
        }
        match &mut data.kind {
          DefKind::Function(func) => func.body = def.body,
          DefKind::Var(var) => {
            if let Some(body) = def.body {
              var.body = body;
            }
          }
          DefKind::VarDeclarator(var) => {
            var.body = def.body;
          }
          DefKind::Class(class) => {
            class.body = def.body;
            class.declare |= def.is_ambient;
          }
          DefKind::Enum(en) => {
            en.body = def.body;
            en.declare |= def.is_ambient;
          }
          DefKind::Namespace(ns) => {
            if def.body.is_some() {
              ns.body = def.body;
            }
            ns.declare |= def.is_ambient;
          }
          DefKind::Module(ns) => {
            if def.body.is_some() {
              ns.body = def.body;
            }
            ns.declare |= def.is_ambient;
          }
          _ => {}
        }
        if let Some(ty) = self.def_types.get(&old_id).copied() {
          new_def_types.insert(def.id, ty);
        }
        if let Some(ty) = self.interned_def_types.get(&old_id).copied() {
          new_interned_def_types.insert(def.id, ty);
        }
        if let Some(params) = self.interned_type_params.get(&old_id).cloned() {
          new_interned_type_params.insert(def.id, params);
        }
        if let Some(decls) = self.interned_type_param_decls.get(&old_id).cloned() {
          new_interned_type_param_decls.insert(def.id, decls);
        }
        (def.id, data)
      } else {
        let symbol = self.alloc_symbol();
        let kind = match match_kind {
          DefMatchKind::Function => DefKind::Function(FuncData {
            params: def
              .body
              .and_then(|body_id| lowered.body(body_id))
              .and_then(|body| body.function.as_ref().map(|func| (body, func)))
              .map(|(body, func)| {
                func
                  .params
                  .iter()
                  .enumerate()
                  .map(|(index, param)| {
                    let name = match body.pats.get(param.pat.0 as usize).map(|pat| &pat.kind) {
                      Some(HirPatKind::Ident(name_id)) => lowered
                        .names
                        .resolve(*name_id)
                        .unwrap_or_default()
                        .to_string(),
                      _ => format!("<pattern{index}>"),
                    };
                    ParamData {
                      name,
                      typ: None,
                      symbol: self.alloc_symbol(),
                      pat: None,
                    }
                  })
                  .collect()
              })
              .unwrap_or_default(),
            return_ann: None,
            body: def.body,
          }),
          DefMatchKind::VarDeclarator => {
            DefKind::VarDeclarator(VarDeclaratorData { body: def.body })
          }
          DefMatchKind::Class => DefKind::Class(ClassData {
            body: def.body,
            instance_type: None,
            static_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Enum => DefKind::Enum(EnumData {
            body: def.body,
            is_const: false,
            value_type: None,
            type_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Namespace => DefKind::Namespace(NamespaceData {
            body: def.body,
            value_type: None,
            type_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Module => DefKind::Module(ModuleData {
            body: def.body,
            value_type: None,
            type_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Interface => DefKind::Interface(InterfaceData {
            typ: self.builtin.unknown,
          }),
          DefMatchKind::TypeAlias => DefKind::TypeAlias(TypeAliasData {
            typ: self.builtin.unknown,
          }),
          _ => DefKind::Var(VarData {
            typ: None,
            init: None,
            body: def.body.unwrap_or(MISSING_BODY),
            mode: VarDeclMode::Var,
          }),
        };
        let export = if is_var_declarator {
          false
        } else {
          def.is_exported || def.is_default_export
        };
        let data = DefData {
          name: name.clone(),
          file,
          span: def.span,
          symbol,
          export,
          kind,
        };
        self.record_def_symbol(def.id, symbol);
        if !is_var_declarator {
          self.record_symbol(file, def.span, symbol);
        }
        (def.id, data)
      };

      if !is_var_declarator {
        if is_file_level_binding(def) {
          bindings
            .entry(raw_name.clone())
            .and_modify(|binding| {
              binding.symbol = data.symbol;
              binding.def = Some(def_id);
            })
            .or_insert(SymbolBinding {
              symbol: data.symbol,
              def: Some(def_id),
              type_id: None,
            });
        }
      }

      if data.export && !is_var_declarator && is_file_level_binding(def) {
        let export_name = if def.is_default_export {
          "default".to_string()
        } else {
          raw_name.clone()
        };
        exports.insert(
          export_name,
          ExportEntry {
            symbol: data.symbol,
            def: Some(def_id),
            type_id: new_def_types.get(&def_id).copied(),
          },
        );
      }

      new_def_data.insert(def_id, data);
      resolved_defs.push(def_id);
    }

    for leftovers in by_name_kind.values_mut() {
      for (old_id, data) in leftovers.drain(..) {
        new_def_data.insert(old_id, data.clone());
        if let Some(ty) = self.def_types.get(&old_id).copied() {
          new_def_types.insert(old_id, ty);
        }
        if let Some(ty) = self.interned_def_types.get(&old_id).copied() {
          new_interned_def_types.insert(old_id, ty);
        }
        if let Some(params) = self.interned_type_params.get(&old_id).cloned() {
          new_interned_type_params.insert(old_id, params);
        }
        if let Some(decls) = self.interned_type_param_decls.get(&old_id).cloned() {
          new_interned_type_param_decls.insert(old_id, decls);
        }
      }
    }

    for binding in bindings.values_mut() {
      if let Some(def) = binding.def {
        if let Some(mapped) = id_mapping.get(&def) {
          binding.def = Some(*mapped);
        }
      }
    }
    for entry in exports.values_mut() {
      if let Some(def) = entry.def {
        if let Some(mapped) = id_mapping.get(&def) {
          entry.def = Some(*mapped);
        }
      }
    }

    // Synthesize value-side definitions for classes/enums so `typeof` can map to a
    // dedicated value def without conflating with the instance/type-side def.
    // These defs are stable across runs: they are derived from the type-side `DefId`.
    self.value_defs.retain(|type_def, value_def| {
      !file_def_ids.contains(type_def) && !file_def_ids.contains(value_def)
    });
    let mut taken_ids: HashSet<DefId> = new_def_data.keys().copied().collect();
    let mut class_enum_type_defs: Vec<DefId> = Vec::new();
    for def_id in resolved_defs.iter().copied() {
      if let Some(data) = new_def_data.get(&def_id) {
        if matches!(data.kind, DefKind::Class(_) | DefKind::Enum(_)) {
          class_enum_type_defs.push(def_id);
        }
      }
    }
    class_enum_type_defs.sort_by_key(|d| d.0);
    for type_def in class_enum_type_defs {
      let Some(type_data) = new_def_data.get(&type_def).cloned() else {
        continue;
      };
      let tag = match type_data.kind {
        DefKind::Class(_) => 1u32,
        DefKind::Enum(_) => 2u32,
        _ => continue,
      };
      let value_def = alloc_synthetic_def_id(
        file,
        &mut taken_ids,
        &("ts_value_def", file.0, type_def.0, tag),
      );
      self.value_defs.insert(type_def, value_def);
      new_def_data.entry(value_def).or_insert_with(|| DefData {
        name: type_data.name.clone(),
        file: type_data.file,
        span: type_data.span,
        symbol: type_data.symbol,
        export: type_data.export,
        kind: DefKind::Var(VarData {
          typ: None,
          init: None,
          body: MISSING_BODY,
          mode: VarDeclMode::Let,
        }),
      });
      if let Some(binding) = bindings.get_mut(&type_data.name) {
        if binding.def == Some(type_def) {
          binding.def = Some(value_def);
        }
      }
      for entry in exports.values_mut() {
        if entry.def == Some(type_def) {
          entry.def = Some(value_def);
        }
      }
    }

    self.files.insert(
      file,
      FileState {
        defs: resolved_defs,
        exports,
        bindings,
        top_body: file_state.top_body,
        reexports,
        export_all,
      },
    );

    self.def_data = new_def_data;
    self.def_types = new_def_types;
    self.interned_def_types = new_interned_def_types;
    self.interned_type_params = new_interned_type_params;
    self.interned_type_param_decls = new_interned_type_param_decls;

    self.symbol_to_def.clear();
    for (def, data) in self.def_data.iter() {
      self.symbol_to_def.insert(data.symbol, *def);
    }
    self.next_def = self
      .def_data
      .keys()
      .map(|d| d.0)
      .max()
      .unwrap_or(0)
      .saturating_add(1);

    id_mapping
  }

  fn map_hir_bodies(&mut self, file: FileId, lowered: &LowerResult) {
    // Bodies are keyed by stable hash-based IDs. In the (rare) event that a body id collides
    // across files, we must ensure we clear any stale metadata/parent edges before inserting the
    // newly-lowered bodies for `file`.
    let mut stale: HashSet<BodyId> = self
      .body_map
      .iter()
      .filter(|(_, meta)| meta.file == file)
      .map(|(id, _)| *id)
      .collect();
    stale.extend(lowered.body_index.keys().copied());
    self.body_map.retain(|id, _| !stale.contains(id));
    self.body_parents.retain(|child, _| !stale.contains(child));

    if let Some(state) = self.files.get_mut(&file) {
      state.top_body = Some(lowered.root_body());
    }

    let mut defs_by_span: HashMap<(TextRange, &'static str), DefId> = HashMap::new();
    let mut defs_by_name: HashMap<(String, &'static str), DefId> = HashMap::new();
    let mut file_defs: Vec<_> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file == file)
      .collect();
    file_defs.sort_by_key(|(id, data)| (data.span.start, data.span.end, id.0));
    for (def_id, data) in file_defs {
      let kind = match data.kind {
        DefKind::Function(_) => Some("fn"),
        DefKind::Var(_) => Some("var"),
        _ => None,
      };
      if let Some(kind) = kind {
        if kind == "var" {
          if let Some(hir_def) = lowered.def(*def_id) {
            if matches!(hir_def.path.kind, HirDefKind::VarDeclarator) {
              // `VarDeclarator` defs exist to own initializer bodies; they are not
              // bindings and shouldn't be used for mapping patterns to program
              // definitions.
              continue;
            }
          }
        }
        defs_by_span.entry((data.span, kind)).or_insert(*def_id);
        defs_by_name
          .entry((data.name.clone(), kind))
          .or_insert(*def_id);
      }
    }

    for (hir_body_id, idx) in lowered.body_index.iter() {
      let hir_body = lowered
        .bodies
        .get(*idx)
        .map(Arc::as_ref)
        .unwrap_or_else(|| panic!("missing lowered body for id {:?}", hir_body_id));

      for stmt in hir_body.stmts.iter() {
        if let hir_js::StmtKind::Var(decl) = &stmt.kind {
          for declarator in decl.declarators.iter() {
            // Update every bound identifier in the declarator (including destructuring patterns)
            // with the initializer expression/body. This keeps `var_initializer` fast and avoids
            // relying on the salsa HIR scan for common destructuring cases.
            let mut stack = vec![declarator.pat];
            let mut updated: HashSet<DefId> = HashSet::new();
            while let Some(pat_id) = stack.pop() {
              let Some(pat) = hir_body.pats.get(pat_id.0 as usize) else {
                continue;
              };
              match &pat.kind {
                hir_js::PatKind::Ident(name_id) => {
                  let name = lowered.names.resolve(*name_id).map(|n| n.to_string());
                  let def_id = defs_by_span.get(&(pat.span, "var")).copied().or_else(|| {
                    name
                      .as_ref()
                      .and_then(|name| defs_by_name.get(&(name.clone(), "var")).copied())
                  });
                  let Some(def_id) = def_id else {
                    continue;
                  };
                  if !updated.insert(def_id) {
                    continue;
                  }
                  if let Some(def) = self.def_data.get_mut(&def_id) {
                    if let DefKind::Var(var) = &mut def.kind {
                      var.mode = match decl.kind {
                        hir_js::VarDeclKind::Var => VarDeclMode::Var,
                        hir_js::VarDeclKind::Let => VarDeclMode::Let,
                        hir_js::VarDeclKind::Const => VarDeclMode::Const,
                        hir_js::VarDeclKind::Using => VarDeclMode::Using,
                        hir_js::VarDeclKind::AwaitUsing => VarDeclMode::AwaitUsing,
                      };
                      if let Some(init) = declarator.init {
                        let prefer = matches!(hir_body.kind, HirBodyKind::Initializer);
                        if var.body == MISSING_BODY || prefer {
                          var.body = *hir_body_id;
                        }
                        if var.init.is_none() || prefer {
                          var.init = Some(init);
                        }
                      }
                    }
                  }
                }
                hir_js::PatKind::Array(arr) => {
                  for elem in arr.elements.iter() {
                    let Some(elem) = elem.as_ref() else {
                      continue;
                    };
                    stack.push(elem.pat);
                  }
                  if let Some(rest) = arr.rest {
                    stack.push(rest);
                  }
                }
                hir_js::PatKind::Object(obj) => {
                  for prop in obj.props.iter() {
                    stack.push(prop.value);
                  }
                  if let Some(rest) = obj.rest {
                    stack.push(rest);
                  }
                }
                hir_js::PatKind::Rest(inner) => {
                  stack.push(**inner);
                }
                hir_js::PatKind::Assign { target, .. } => {
                  stack.push(*target);
                }
                hir_js::PatKind::AssignTarget(_) => {}
              }
            }
          }
        }
      }

      for stmt in hir_body.stmts.iter() {
        if let hir_js::StmtKind::Decl(def) = &stmt.kind {
          if let Some(hir_def) = lowered.def(*def) {
            if let Some(child) = hir_def.body {
              self.body_parents.insert(child, *hir_body_id);
            }
          }
        }
      }

      for expr in hir_body.exprs.iter() {
        match &expr.kind {
          HirExprKind::FunctionExpr { body, .. } | HirExprKind::ClassExpr { body, .. } => {
            self.body_parents.insert(*body, *hir_body_id);
          }
          _ => {}
        }
      }

      self.body_map.insert(
        *hir_body_id,
        BodyMeta {
          file,
          hir: Some(*hir_body_id),
          kind: hir_body.kind,
        },
      );
    }

    for export in lowered.hir.exports.iter() {
      if let HirExportKind::Default(default) = &export.kind {
        match &default.value {
          hir_js::ExportDefaultValue::Expr { expr, body } => {
            if let Some((_def_id, def)) = self
              .def_data
              .iter_mut()
              .find(|(_, data)| data.file == file && data.name == "default")
            {
              if let DefKind::Var(var) = &mut def.kind {
                var.body = *body;
                var.init = Some(*expr);
                var.mode = VarDeclMode::Const;
              }
              self.body_parents.insert(*body, lowered.root_body());
            }
          }
          hir_js::ExportDefaultValue::Class { def, body, .. }
          | hir_js::ExportDefaultValue::Function { def, body, .. } => {
            if let Some(data) = self.def_data.get_mut(def) {
              match &mut data.kind {
                DefKind::Function(func) => func.body = Some(*body),
                DefKind::Class(class) => class.body = Some(*body),
                _ => {}
              }
            }
            self.body_parents.insert(*body, lowered.root_body());
          }
        }
      }
    }

    // Connect definition-owned bodies (notably initializer bodies) to their containing body so
    // nested checks can seed outer bindings (parameters, locals, etc). Bodies introduced by
    // `StmtKind::Decl` and expression nodes are already linked above; this covers orphan bodies
    // such as `DefSource::Var` initializer bodies that otherwise lack a parent edge.
    let root_body = lowered.root_body();
    let mut def_to_body: HashMap<HirDefId, BodyId> = HashMap::new();
    for def in lowered.defs.iter() {
      if let Some(body) = def.body {
        def_to_body.insert(def.id, body);
      }
    }
    for def in lowered.defs.iter() {
      let Some(child_body) = def.body else {
        continue;
      };
      if child_body == root_body {
        continue;
      }
      let Some(parent_def) = def.parent else {
        continue;
      };
      let Some(parent_body) = def_to_body.get(&parent_def).copied() else {
        continue;
      };
      if child_body == parent_body {
        continue;
      }
      self.body_parents.entry(child_body).or_insert(parent_body);
    }

    // Fallback: infer missing parent links from body span containment.
    //
    // `hir-js` synthesizes bodies for variable initializers (and similar nodes) that are not
    // referenced by the surrounding statement list. Those bodies still need parent edges so
    // nested checks can seed parameter/local bindings.
    fn hir_body_range(body: &hir_js::Body) -> TextRange {
      let mut start = u32::MAX;
      let mut end = 0u32;
      for stmt in body.stmts.iter() {
        start = start.min(stmt.span.start);
        end = end.max(stmt.span.end);
      }
      for expr in body.exprs.iter() {
        start = start.min(expr.span.start);
        end = end.max(expr.span.end);
      }
      for pat in body.pats.iter() {
        start = start.min(pat.span.start);
        end = end.max(pat.span.end);
      }
      if start == u32::MAX {
        // Use the stored body span for synthesized bodies (notably initializer bodies) that don't
        // record statement/expression spans. This keeps span containment inference stable so
        // initializer bodies inherit bindings from their lexical parent.
        match body.kind {
          HirBodyKind::Class => TextRange::new(0, 0),
          _ => body.span,
        }
      } else {
        TextRange::new(start, end)
      }
    }

    let mut bodies: Vec<(BodyId, TextRange)> = lowered
      .body_index
      .keys()
      .copied()
      .filter_map(|id| lowered.body(id).map(|b| (id, hir_body_range(b))))
      .collect();
    bodies.sort_by_key(|(id, range)| (range.start, Reverse(range.end), id.0));

    let mut stack: Vec<(BodyId, TextRange)> = Vec::new();
    for (child, range) in bodies {
      if child == root_body {
        stack.clear();
        stack.push((child, range));
        continue;
      }
      while let Some((_, parent_range)) = stack.last().copied() {
        if range.start >= parent_range.start && range.end <= parent_range.end {
          break;
        }
        stack.pop();
      }
      let computed_parent = stack.last().map(|(id, _)| *id).unwrap_or(root_body);
      if computed_parent != child {
        let is_initializer = lowered
          .body(child)
          .map(|body| matches!(body.kind, HirBodyKind::Initializer))
          .unwrap_or(false);
        // Initializer bodies must inherit bindings from their containing scope
        // (e.g. function parameters). The def-parent chain can be incomplete or
        // point at a broader container, so prefer the lexical parent inferred
        // from span containment for initializer bodies.
        if is_initializer || !self.body_parents.contains_key(&child) {
          self.body_parents.insert(child, computed_parent);
        }
      }
      stack.push((child, range));
    }

    // Keep the body parent graph consistent with the query-side computation used
    // by `db::body_parents_in_file`. The salsa query includes additional edges
    // (e.g. getter/setter bodies and synthesized initializer bodies) and is the
    // canonical implementation. Overwrite any locally inferred edges for this
    // file so nested checks can reliably seed outer bindings.
    let parents = db::body_parents_in_file(&self.typecheck_db, file);
    for (child, parent) in parents.iter() {
      self.body_parents.insert(*child, *parent);
    }

    self.next_body = self
      .body_map
      .keys()
      .map(|b| b.0)
      .max()
      .unwrap_or(0)
      .saturating_add(1);
  }

  fn rebuild_body_owners(&mut self) {
    self.body_owners.clear();
    let mut defs: Vec<_> = self.def_data.iter().collect();
    defs.sort_by_key(|(id, data)| (data.file.0, data.span.start, data.span.end, id.0));
    for (def_id, data) in defs {
      match &data.kind {
        DefKind::Function(func) => {
          if let Some(body) = func.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Var(var) => {
          if var.body != MISSING_BODY {
            self.body_owners.insert(var.body, *def_id);
          }
        }
        DefKind::VarDeclarator(var) => {
          if let Some(body) = var.body {
            self.body_owners.entry(body).or_insert(*def_id);
          }
        }
        DefKind::Class(class) => {
          if let Some(body) = class.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Enum(en) => {
          if let Some(body) = en.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Namespace(ns) => {
          if let Some(body) = ns.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Module(ns) => {
          if let Some(body) = ns.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Import(_)
        | DefKind::ImportAlias(_)
        | DefKind::Interface(_)
        | DefKind::TypeAlias(_) => {}
      }
    }
  }

  fn push_semantic_diagnostics(&mut self, diags: Vec<Diagnostic>) {
    for mut diag in diags {
      if diag.code == "BIND1002" {
        continue;
      }
      if diag.code == "BIND1002" && diag.message.contains("unresolved import:") {
        if let Some(spec) = diag.message.split(':').nth(1).map(|s| s.trim()) {
          let has_ambient = self
            .semantics
            .as_ref()
            .and_then(|semantics| semantics.exports_of_ambient_module(spec))
            .map(|exports| !exports.is_empty())
            .unwrap_or(false);
          if has_ambient {
            continue;
          }
        }
      }
      if diag.code == "BIND1002" {
        if diag.message.contains("unresolved") {
          diag.code = codes::UNRESOLVED_MODULE.as_str().into();
        } else {
          diag.code = codes::UNKNOWN_EXPORT.as_str().into();
        }
      }
      let duplicate = self.diagnostics.iter().any(|existing| {
        existing.code == diag.code
          && existing.primary == diag.primary
          && existing.message == diag.message
      });
      if duplicate {
        continue;
      }
      self.diagnostics.push(diag);
    }
  }

  fn check_import_assignment_requires(&mut self) {
    // Match tsc's TS1202 behaviour: `import x = require("...")` is rejected when
    // targeting ECMAScript module outputs.
    //
    // Note: `tsc` only allows `import = require()` in ESM output modes for the
    // Node16/NodeNext emit strategies, and only when importing from a
    // CommonJS-style module (one that uses `export =`).
    let module =
      self
        .compiler_options
        .module
        .unwrap_or_else(|| match self.compiler_options.target {
          ScriptTarget::Es3 | ScriptTarget::Es5 => ModuleKind::CommonJs,
          _ => ModuleKind::Es2015,
        });
    let targets_ecmascript_modules = matches!(
      module,
      ModuleKind::Es2015
        | ModuleKind::Es2020
        | ModuleKind::Es2022
        | ModuleKind::EsNext
        | ModuleKind::Node16
        | ModuleKind::NodeNext
    );
    if !targets_ecmascript_modules {
      return;
    }

    let Some(semantics) = self.semantics.as_ref() else {
      return;
    };

    let allow_commonjs_interop = matches!(module, ModuleKind::Node16 | ModuleKind::NodeNext);
    let mut records = self.import_assignment_requires.clone();
    records.sort_by_key(|record| (record.file.0, record.span.start, record.span.end));
    for record in records {
      // TypeScript permits `import = require()` declarations in `.d.ts` files
      // regardless of emit target. Since these files never produce JS output,
      // the restriction only applies to emit-capable sources.
      if self.file_kinds.get(&record.file) == Some(&FileKind::Dts) {
        continue;
      }
      if allow_commonjs_interop {
        let has_export_assignment = match record.target {
          ImportTarget::File(target_file) => semantics
            .exports_of_opt(sem_ts::FileId(target_file.0))
            .map(|exports| exports.contains_key("export="))
            .unwrap_or(false),
          ImportTarget::Unresolved { .. } => false,
        };
        if has_export_assignment {
          continue;
        }
      }
      self.diagnostics.push(codes::IMPORT_ASSIGNMENT_IN_ESM.error(
        "Import assignment cannot be used when targeting ECMAScript modules.",
        Span::new(record.file, record.span),
      ));
    }
  }

  fn check_export_assignments_in_esm(&mut self) {
    // Match tsc's TS1203 behaviour: `export = value` is rejected when emitting
    // ECMAScript modules.
    let module =
      self
        .compiler_options
        .module
        .unwrap_or_else(|| match self.compiler_options.target {
          ScriptTarget::Es3 | ScriptTarget::Es5 => ModuleKind::CommonJs,
          _ => ModuleKind::Es2015,
        });
    let targets_ecmascript_modules = matches!(
      module,
      ModuleKind::Es2015
        | ModuleKind::Es2020
        | ModuleKind::Es2022
        | ModuleKind::EsNext
        | ModuleKind::Node16
        | ModuleKind::NodeNext
    );
    if !targets_ecmascript_modules {
      return;
    }

    let mut files: Vec<FileId> = self.hir_lowered.keys().copied().collect();
    files.sort_by_key(|file| file.0);
    for file in files {
      // TypeScript permits `export =` declarations in `.d.ts` files regardless
      // of emit target. Since these files never produce JS output, the
      // restriction only applies to emit-capable sources.
      if self.file_kinds.get(&file) == Some(&FileKind::Dts) {
        continue;
      }
      let Some(lowered) = self.hir_lowered.get(&file) else {
        continue;
      };
      for export in lowered.hir.exports.iter() {
        if matches!(export.kind, hir_js::ExportKind::Assignment(_)) {
          self.diagnostics.push(codes::EXPORT_ASSIGNMENT_IN_ESM.error(
            "Export assignment cannot be used when targeting ECMAScript modules.",
            Span::new(file, export.span),
          ));
        }
      }
    }
  }

  fn resolve_reexports(&mut self) {
    let mut changed = true;
    let mut files: Vec<FileId> = self.files.keys().copied().collect();
    files.sort_by_key(|f| f.0);
    while changed {
      changed = false;
      for file in files.iter() {
        let Some(state) = self.files.get(file).cloned() else {
          continue;
        };
        let mut exports = state.exports.clone();
        for spec in state.reexports.iter() {
          let Ok(target_exports) = self.exports_of_file(spec.from) else {
            continue;
          };
          if let Some(entry) = target_exports.get(&spec.original) {
            let resolved_def = entry
              .def
              .or_else(|| self.symbol_to_def.get(&entry.symbol).copied());
            if !spec.type_only {
              if let Some(def) = resolved_def {
                if let Some(def_data) = self.def_data.get(&def) {
                  if matches!(def_data.kind, DefKind::TypeAlias(_) | DefKind::Interface(_)) {
                    let duplicate = self.diagnostics.iter().any(|existing| {
                      existing.code.as_str() == codes::UNKNOWN_EXPORT.as_str()
                        && existing.primary.file == *file
                        && existing.primary.range == spec.span
                    });
                    if !duplicate {
                      self.diagnostics.push(codes::UNKNOWN_EXPORT.error(
                        format!("unknown export {}", spec.original),
                        Span::new(*file, spec.span),
                      ));
                    }
                    continue;
                  }
                }
              }
            }
            let mut type_id = entry.type_id;
            if let Some(def) = resolved_def {
              match self.export_type_for_def(def) {
                Ok(Some(ty)) => type_id = Some(ty),
                Ok(None) => {
                  if type_id.is_none() {
                    type_id = self.def_types.get(&def).copied();
                  }
                }
                Err(fatal) => {
                  self.diagnostics.push(fatal_to_diagnostic(fatal));
                  if type_id.is_none() {
                    type_id = self.def_types.get(&def).copied();
                  }
                }
              }
            }
            let mapped = ExportEntry {
              symbol: entry.symbol,
              def: None,
              type_id,
            };
            let mut update = true;
            if let Some(existing) = exports.get(&spec.alias) {
              if existing.symbol != mapped.symbol {
                update = false;
              } else if existing.def.is_none() && mapped.def.is_some() {
                update = true;
              } else if existing.def == mapped.def {
                update = mapped.type_id.is_some()
                  && (existing.type_id.is_none() || existing.type_id != mapped.type_id);
              } else {
                update = false;
              }
            }
            if update {
              let previous = exports.insert(spec.alias.clone(), mapped.clone());
              if previous
                .as_ref()
                .map(|prev| {
                  prev.symbol != mapped.symbol
                    || prev.def != mapped.def
                    || prev.type_id != mapped.type_id
                })
                .unwrap_or(true)
              {
                changed = true;
              }
            }
            continue;
          }
          let duplicate = self.diagnostics.iter().any(|existing| {
            existing.code.as_str() == codes::UNKNOWN_EXPORT.as_str()
              && existing.primary.file == *file
              && existing.primary.range == spec.span
          });
          if !duplicate {
            self.diagnostics.push(codes::UNKNOWN_EXPORT.error(
              format!("unknown export {}", spec.original),
              Span::new(*file, spec.span),
            ));
          }
        }

        for spec in state.export_all.iter() {
          let Ok(target_exports) = self.exports_of_file(spec.from) else {
            continue;
          };
          for (name, entry) in target_exports.iter() {
            if name == "default" {
              continue;
            }
            let mut is_type = false;
            let resolved_def = entry
              .def
              .or_else(|| self.symbol_to_def.get(&entry.symbol).copied());
            if let Some(def) = resolved_def {
              if let Some(def_data) = self.def_data.get(&def) {
                is_type = matches!(def_data.kind, DefKind::TypeAlias(_) | DefKind::Interface(_));
                if !spec.type_only && is_type {
                  continue;
                }
              }
            }
            if spec.type_only && !is_type {
              continue;
            }
            let mut type_id = entry.type_id;
            if let Some(def) = resolved_def {
              match self.export_type_for_def(def) {
                Ok(Some(ty)) => type_id = Some(ty),
                Ok(None) => {
                  if type_id.is_none() {
                    type_id = self.def_types.get(&def).copied();
                  }
                }
                Err(fatal) => {
                  self.diagnostics.push(fatal_to_diagnostic(fatal));
                  if type_id.is_none() {
                    type_id = self.def_types.get(&def).copied();
                  }
                }
              }
            }
            let mapped = ExportEntry {
              symbol: entry.symbol,
              def: None,
              type_id,
            };
            let mut update = true;
            if let Some(existing) = exports.get(name) {
              if existing.symbol != mapped.symbol {
                update = false;
              } else if existing.def.is_none() && mapped.def.is_some() {
                update = true;
              } else if existing.def == mapped.def {
                update = mapped.type_id.is_some()
                  && (existing.type_id.is_none() || existing.type_id != mapped.type_id);
              } else {
                update = false;
              }
            }
            if update {
              let previous = exports.insert(name.clone(), mapped.clone());
              if previous
                .as_ref()
                .map(|prev| {
                  prev.symbol != mapped.symbol
                    || prev.def != mapped.def
                    || prev.type_id != mapped.type_id
                })
                .unwrap_or(true)
              {
                changed = true;
              }
            }
          }
        }

        if let Some(existing) = self.files.get_mut(file) {
          existing.exports = exports;
        }
      }
    }
  }

  fn check_required_global_types(&mut self) {
    // TypeScript emits TS2318 ("Cannot find global type") whenever the default
    // lib set is disabled and the compilation does not provide the core global
    // type declarations required by the checker.
    //
    // This can happen either when `--noLib` / `no-default-lib` is set, or when
    // an explicit `--lib` list omits foundational libs like `es5`.
    if !self.compiler_options.no_default_lib && self.compiler_options.libs.is_empty() {
      return;
    }
    let Some(semantics) = self.semantics.as_ref().map(Arc::clone) else {
      return;
    };
    const REQUIRED: [&str; 8] = [
      "Array",
      "Boolean",
      "Function",
      "IArguments",
      "Number",
      "Object",
      "RegExp",
      "String",
    ];
    let symbols = semantics.symbols();
    for name in REQUIRED {
      let has_type = semantics
        .global_symbols()
        .get(name)
        .and_then(|group| group.symbol_for(sem_ts::Namespace::TYPE, symbols))
        .is_some();
      if has_type {
        continue;
      }
      self.push_program_diagnostic(codes::CANNOT_FIND_GLOBAL_TYPE.error(
        format!("Cannot find global type '{name}'."),
        Span::new(FileId(u32::MAX), TextRange::new(0, 0)),
      ));
    }
  }
}
