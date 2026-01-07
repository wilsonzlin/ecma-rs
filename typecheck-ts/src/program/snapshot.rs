use super::*;

#[cfg(feature = "serde")]
use crate::snapshot::{
  DefSnapshot, FileSnapshot, FileStateSnapshot, LocalSymbolInfoSnapshot, ModuleResolutionSnapshot,
  ProgramSnapshot, PROGRAM_SNAPSHOT_VERSION,
};

impl Program {
  /// Serialize the current analyzed state into a deterministic snapshot suitable
  /// for caching or offline queries. All bodies and definitions are fully
  /// checked before serialization to ensure type and diagnostic tables are
  /// populated.
  #[cfg(feature = "serde")]
  pub fn snapshot(&self) -> ProgramSnapshot {
    use sha2::{Digest, Sha256};

    let mut state = self.lock_state();
    state.ensure_analyzed(&self.host, &self.roots);
    if let Err(fatal) = state.ensure_interned_types(&self.host, &self.roots) {
      state.diagnostics.push(fatal_to_diagnostic(fatal));
    }

    let mut body_ids: Vec<_> = state.body_map.keys().copied().collect();
    body_ids.sort_by_key(|id| id.0);
    for body in body_ids.iter() {
      if let Err(fatal) = state.check_body(*body) {
        state.diagnostics.push(fatal_to_diagnostic(fatal));
        break;
      }
    }

    let mut def_ids: Vec<_> = state.def_data.keys().copied().collect();
    def_ids.sort_by_key(|id| id.0);
    for def in def_ids.iter() {
      if let Err(fatal) = ProgramState::type_of_def(&mut state, *def) {
        state.diagnostics.push(fatal_to_diagnostic(fatal));
        break;
      }
    }

    let mut file_ids: Vec<_> = state.file_kinds.keys().copied().collect();
    file_ids.sort_by_key(|id| id.0);
    let mut files = Vec::new();
    for file in file_ids {
      let kind = *state.file_kinds.get(&file).unwrap_or(&FileKind::Ts);
      let key = state
        .file_key_for_id(file)
        .unwrap_or_else(|| FileKey::new(format!("file{}.ts", file.0)));
      let is_lib = state.lib_file_ids.contains(&file);
      let text = state.lib_texts.get(&file).cloned().or_else(|| {
        state
          .file_key_for_id(file)
          .and_then(|key| self.host.file_text(&key).ok())
      });
      let hash = if let Some(text) = text.as_ref() {
        let mut hasher = Sha256::new();
        hasher.update(text.as_bytes());
        format!("{:x}", hasher.finalize())
      } else {
        String::new()
      };
      files.push(FileSnapshot {
        file,
        key,
        kind,
        is_lib,
        hash,
        text: text.map(|t| t.to_string()),
      });
    }

    let mut file_states = Vec::new();
    let mut file_state_ids: Vec<_> = state.files.keys().copied().collect();
    file_state_ids.sort_by_key(|id| id.0);
    for file in file_state_ids {
      let exports = match state.exports_of_file(file) {
        Ok(exports) => exports,
        Err(fatal) => {
          state.diagnostics.push(fatal_to_diagnostic(fatal));
          state
            .files
            .get(&file)
            .map(|state| state.exports.clone())
            .unwrap_or_default()
        }
      };
      let fs = state.files.get(&file).expect("file state present");
      let mut bindings: Vec<_> = fs
        .bindings
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
      bindings.sort_by(|a, b| a.0.cmp(&b.0));
      let mut defs = fs.defs.clone();
      defs.sort_by_key(|d| d.0);
      file_states.push(FileStateSnapshot {
        file,
        defs,
        exports,
        bindings,
        top_body: fs.top_body,
        ambient_modules: Vec::new(),
      });
    }

    let mut def_data = Vec::new();
    for def in def_ids.iter() {
      if let Some(data) = state.def_data.get(def) {
        def_data.push(DefSnapshot {
          def: *def,
          data: data.clone(),
        });
      }
    }

    let mut body_results: Vec<_> = state
      .body_results
      .iter()
      .map(|(id, res)| (*id, (**res).clone()))
      .collect();
    body_results.sort_by_key(|(id, _)| id.0);
    let body_results: Vec<_> = body_results.into_iter().map(|(_, res)| res).collect();

    let mut symbol_occurrences = Vec::new();
    let mut symbol_files: Vec<_> = state.file_kinds.keys().copied().collect();
    symbol_files.sort_by_key(|file| file.0);
    for file in symbol_files.iter().copied() {
      let occs = crate::db::symbol_occurrences(&state.typecheck_db, file);
      symbol_occurrences.push((file, occs.iter().cloned().collect()));
    }

    let mut local_symbol_info = Vec::new();
    for file in symbol_files.iter().copied() {
      let locals = crate::db::local_symbol_info(&state.typecheck_db, file);
      for (symbol, info) in locals.iter() {
        local_symbol_info.push(LocalSymbolInfoSnapshot {
          symbol: *symbol,
          file: info.file,
          name: info.name.clone(),
          span: info.span,
        });
      }
    }
    local_symbol_info.sort_by_key(|info| (info.file.0, info.symbol.0));

    let mut symbol_to_def: Vec<_> = state
      .symbol_to_def
      .iter()
      .map(|(sym, def)| (*sym, *def))
      .collect();
    symbol_to_def.sort_by_key(|(sym, _)| sym.0);

    let mut global_bindings: Vec<_> = state
      .global_bindings
      .iter()
      .map(|(name, binding)| (name.clone(), binding.clone()))
      .collect();
    global_bindings.sort_by(|a, b| a.0.cmp(&b.0));

    let interned_type_store = state.store.snapshot();
    let mut interned_def_types: Vec<_> = state
      .interned_def_types
      .iter()
      .map(|(def, ty)| (*def, *ty))
      .collect();
    interned_def_types.sort_by_key(|(def, _)| def.0);
    let mut interned_type_params: Vec<_> = state
      .interned_type_params
      .iter()
      .map(|(def, params)| (*def, params.clone()))
      .collect();
    interned_type_params.sort_by_key(|(def, _)| def.0);
    let mut interned_type_param_decls: Vec<_> = state
      .interned_type_param_decls
      .iter()
      .map(|(def, decls)| (*def, decls.as_ref().to_vec()))
      .collect();
    interned_type_param_decls.sort_by_key(|(def, _)| def.0);
    let mut interned_intrinsics: Vec<_> = state
      .interned_intrinsics
      .iter()
      .map(|(def, kind)| (*def, *kind))
      .collect();
    interned_intrinsics.sort_by_key(|(def, _)| def.0);
    let mut value_def_map: Vec<_> = state.value_defs.iter().map(|(a, b)| (*a, *b)).collect();
    value_def_map.sort_by_key(|(def, _)| def.0);

    let canonical_defs_map = match state.canonical_defs() {
      Ok(map) => map,
      Err(fatal) => {
        state.diagnostics.push(fatal_to_diagnostic(fatal));
        HashMap::new()
      }
    };
    let mut canonical_defs: Vec<_> = canonical_defs_map
      .into_iter()
      .filter(|((_, parent, _, _), _)| parent.is_none())
      .map(|((file, _parent, name, _ns), def)| ((file, name), def))
      .collect();
    canonical_defs.sort_by(|a, b| (a.0 .0, &a.0 .1, a.1 .0).cmp(&(b.0 .0, &b.0 .1, b.1 .0)));

    let mut namespace_types: Vec<_> = state
      .namespace_object_types
      .iter()
      .filter_map(|((file, name), store_ty)| {
        state
          .find_namespace_def(*file, name)
          .map(|def| (def, *store_ty))
      })
      .collect();
    namespace_types.sort_by_key(|(def, _)| def.0);

    let diagnostics = match state.program_diagnostics(&self.host, &self.roots) {
      Ok(diags) => diags.to_vec(),
      Err(fatal) => {
        state.diagnostics.push(fatal_to_diagnostic(fatal));
        state.diagnostics.clone()
      }
    };

    let module_resolutions = state
      .typecheck_db
      .module_resolutions_snapshot()
      .into_iter()
      .map(|(from, specifier, resolved)| ModuleResolutionSnapshot {
        from,
        specifier,
        resolved,
      })
      .collect();

    ProgramSnapshot {
      schema_version: PROGRAM_SNAPSHOT_VERSION,
      tool_version: env!("CARGO_PKG_VERSION").to_string(),
      compiler_options: state.compiler_options.clone(),
      roots: {
        let mut roots = state.root_ids.clone();
        roots.sort_by_key(|id| id.0);
        roots.dedup();
        roots
      },
      module_resolutions,
      files,
      file_states,
      def_data,
      canonical_defs,
      namespace_types,
      body_results,
      symbol_occurrences,
      local_symbol_info,
      symbol_to_def,
      global_bindings,
      diagnostics,
      interned_type_store,
      interned_def_types,
      enum_value_types: Vec::new(),
      interned_type_params,
      interned_type_param_decls,
      interned_intrinsics,
      value_def_map,
      next_def: state.next_def,
      next_body: state.next_body,
    }
  }

  /// Rehydrate a program from a previously captured snapshot. The provided host
  /// is used for subsequent queries (such as fetching file text) but the
  /// returned program skips parsing and checking, relying entirely on the
  /// snapshot contents.
  #[cfg(feature = "serde")]
  pub fn from_snapshot(host: impl Host, snapshot: ProgramSnapshot) -> Program {
    assert_eq!(
      snapshot.schema_version, PROGRAM_SNAPSHOT_VERSION,
      "Program snapshot schema mismatch"
    );
    let file_key_map: HashMap<_, _> = snapshot
      .files
      .iter()
      .map(|file| (file.file, file.key.clone()))
      .collect();
    let root_keys: Vec<FileKey> = snapshot
      .roots
      .iter()
      .map(|id| {
        file_key_map
          .get(id)
          .cloned()
          .unwrap_or_else(|| FileKey::new(format!("file{}.ts", id.0)))
      })
      .collect();
    let program = Program::with_lib_manager(host, root_keys, Arc::new(LibManager::new()));
    {
      let mut state = program.lock_state();
      let mut extra_diagnostics = Vec::new();
      state.analyzed = true;
      state.snapshot_loaded = true;
      state.compiler_options = snapshot.compiler_options;
      state.checker_caches = CheckerCaches::new(state.compiler_options.cache.clone());
      state.cache_stats = CheckerCacheStats::default();
      let options = state.compiler_options.clone();
      let cancelled = state.cancelled.clone();
      state.typecheck_db.set_compiler_options(options);
      state.typecheck_db.set_cancellation_flag(cancelled);
      for resolution in snapshot.module_resolutions.into_iter() {
        state.typecheck_db.set_module_resolution_ref(
          resolution.from,
          resolution.specifier.as_str(),
          resolution.resolved,
        );
      }
      for file in snapshot.files.into_iter() {
        let key = file.key.clone();
        let origin = if file.is_lib {
          FileOrigin::Lib
        } else {
          FileOrigin::Source
        };
        let id = state.file_registry.intern(&key, origin);
        debug_assert_eq!(id, file.file, "snapshot file id mismatch");
        state.file_kinds.insert(file.file, file.kind);
        if file.is_lib {
          state.lib_file_ids.insert(file.file);
        }
        let arc = if let Some(text) = file.text {
          Arc::from(text)
        } else {
          match state.host.file_text(&key) {
            Ok(text) => text,
            Err(err) => {
              let placeholder = Span::new(file.file, TextRange::new(0, 0));
              let mut diagnostic = codes::HOST_ERROR.error(err.to_string(), placeholder);
              diagnostic.push_note(
                "host error while restoring snapshot: file text was not embedded and could not be loaded",
              );
              extra_diagnostics.push(diagnostic);
              Arc::<str>::from("")
            }
          }
        };
        state.lib_texts.insert(file.file, Arc::clone(&arc));
        state.set_salsa_inputs(file.file, file.kind, arc);
      }
      state.files = snapshot
        .file_states
        .into_iter()
        .map(|fs| {
          let bindings = fs.bindings.into_iter().collect();
          (
            fs.file,
            FileState {
              defs: fs.defs,
              exports: fs.exports,
              bindings,
              top_body: fs.top_body,
              reexports: Vec::new(),
              export_all: Vec::new(),
            },
          )
        })
        .collect();
      state.asts = HashMap::new();
      state.def_data = snapshot
        .def_data
        .into_iter()
        .map(|def| (def.def, def.data))
        .collect();
      state.body_map = HashMap::new();
      state.body_parents = HashMap::new();
      state.body_results = snapshot
        .body_results
        .into_iter()
        .map(|res| (res.body(), Arc::new(res)))
        .collect();
      state.ensure_body_map_from_defs();
      state.symbol_to_def = snapshot.symbol_to_def.into_iter().collect();
      state.symbol_occurrences = snapshot
        .symbol_occurrences
        .into_iter()
        .map(|(file, mut occs)| {
          occs.sort_by_key(|occ| (occ.range.start, occ.range.end, occ.symbol.0));
          occs.dedup_by(|a, b| a.range == b.range && a.symbol == b.symbol);
          (file, occs)
        })
        .collect();
      state.local_symbol_info = snapshot
        .local_symbol_info
        .into_iter()
        .map(|info| {
          (
            info.symbol,
            crate::db::symbols::LocalSymbolInfo {
              file: info.file,
              name: info.name,
              span: info.span,
            },
          )
        })
        .collect();
      state.global_bindings = Arc::new(snapshot.global_bindings.into_iter().collect());
      state.diagnostics = snapshot.diagnostics;
      state.diagnostics.extend(extra_diagnostics);
      state.store = tti::TypeStore::from_snapshot(snapshot.interned_type_store);
      let store = Arc::clone(&state.store);
      state
        .typecheck_db
        .set_type_store(crate::db::types::SharedTypeStore(store));
      state.interned_def_types = snapshot.interned_def_types.into_iter().collect();
      for (def, ty) in snapshot.enum_value_types.into_iter() {
        state.interned_def_types.entry(def).or_insert(ty);
      }
      state.interned_type_params = snapshot.interned_type_params.into_iter().collect();
      state.interned_type_param_decls = snapshot
        .interned_type_param_decls
        .into_iter()
        .map(|(def, decls)| (def, Arc::from(decls.into_boxed_slice())))
        .collect();
      state.interned_intrinsics = snapshot.interned_intrinsics.into_iter().collect();
      state.value_defs = snapshot.value_def_map.into_iter().collect();
      state.root_ids = snapshot.roots.clone();
      state.lib_diagnostics.clear();
      state.namespace_object_types.clear();
      for (def, ns_ty) in snapshot.namespace_types.into_iter() {
        if let Some((file, name)) = state
          .def_data
          .get(&def)
          .map(|data| (data.file, data.name.clone()))
        {
          state.namespace_object_types.insert((file, name), ns_ty);
        };
        state.interned_def_types.entry(def).or_insert(ns_ty);
      }
      state.next_def = snapshot.next_def;
      state.next_body = snapshot.next_body;
      state.sync_typecheck_roots();
      state.rebuild_module_namespace_defs();
      let module_namespace_defs = Arc::new(state.module_namespace_defs.clone());
      let value_defs = Arc::new(state.value_defs.clone());
      state
        .typecheck_db
        .set_module_namespace_defs(module_namespace_defs);
      state.typecheck_db.set_value_defs(value_defs);
      state.rebuild_callable_overloads();
      state.merge_callable_overload_types();
      state.rebuild_interned_named_def_types();
      state.decl_types_fingerprint = Some(db::decl_types_fingerprint(&state.typecheck_db));
    }
    program
  }
}
