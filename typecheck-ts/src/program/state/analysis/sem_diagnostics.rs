use super::*;

impl ProgramState {
  pub(super) fn push_semantic_diagnostics(&mut self, diags: Vec<Diagnostic>) {
    for mut diag in diags {
      if diag.code == codes::NAMESPACE_BEFORE_MERGE_TARGET.as_str() {
        continue;
      }
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

  pub(super) fn check_import_assignment_requires(&mut self) {
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

  pub(super) fn check_export_assignments_in_esm(&mut self) {
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

  pub(super) fn resolve_reexports(&mut self) {
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

  pub(super) fn check_required_global_types(&mut self) {
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
