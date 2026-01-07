use super::*;

impl ProgramState {
  pub(super) fn collect_libraries(
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
    let store_options = (&options).into();
    let store = match self.interned_store.as_ref() {
      Some(existing) if existing.options() == store_options => Arc::clone(existing),
      _ => {
        let store = tti::TypeStore::with_options(store_options);
        self.interned_store = Some(Arc::clone(&store));
        self.decl_types_fingerprint = None;
        self.interned_def_types.clear();
        self.interned_named_def_types.clear();
        self.interned_type_params.clear();
        self.interned_type_param_decls.clear();
        self.interned_intrinsics.clear();
        self.namespace_object_types.clear();
        store
      }
    };
    self
      .typecheck_db
      .set_type_store(crate::db::types::SharedTypeStore(Arc::clone(&store)));
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

  pub(super) fn process_libs(
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

}
