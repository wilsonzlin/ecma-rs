use crate::execution_context::ModuleId;
use crate::module_graph::ModuleGraph;
use crate::ModuleRequest;
use crate::VmError;
use diagnostics::FileId;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::import_export::ExportNames;
use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalExportEntry {
  pub export_name: String,
  pub local_name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImportName {
  Name(String),
  /// Corresponds to ECMA-262 `ImportName = all`, used by `export * as ns from "m"`.
  All,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndirectExportEntry {
  pub export_name: String,
  pub module_request: ModuleRequest,
  pub import_name: ImportName,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StarExportEntry {
  pub module_request: ModuleRequest,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BindingName {
  Name(String),
  Namespace,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedBinding {
  pub module: ModuleId,
  pub binding_name: BindingName,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolveExportResult {
  Resolved(ResolvedBinding),
  NotFound,
  Ambiguous,
}

/// Source Text Module Record (ECMA-262).
#[derive(Clone, Debug, Default)]
pub struct SourceTextModuleRecord {
  pub requested_modules: Vec<ModuleRequest>,
  pub local_export_entries: Vec<LocalExportEntry>,
  pub indirect_export_entries: Vec<IndirectExportEntry>,
  pub star_export_entries: Vec<StarExportEntry>,

  /// `[[LoadedModules]]` – a host-populated mapping from module requests to resolved module ids.
  pub loaded_modules: Vec<(ModuleRequest, ModuleId)>,
}

impl SourceTextModuleRecord {
  /// Parses a source text module using the `parse-js` front-end and extracts the module record
  /// fields needed by `GetExportedNames` and `ResolveExport`.
  ///
  /// This corresponds to the spec's `ParseModule` abstract operation, but only models the export
  /// entry lists and `[[RequestedModules]]`.
  pub fn parse(source: &str) -> Result<Self, VmError> {
    let opts = ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Module,
    };
    let top = parse_with_options(source, opts)
      .map_err(|err| VmError::Syntax(vec![err.to_diagnostic(FileId(0))]))?;

    let mut record = SourceTextModuleRecord::default();

    for stmt in &top.stx.body {
      match &*stmt.stx {
        Stmt::Import(import_stmt) => {
          if import_stmt.stx.type_only {
            continue;
          }
          record
            .requested_modules
            .push(module_request_from_specifier(&import_stmt.stx.module));
        }

        Stmt::ExportDefaultExpr(_) => {
          record.local_export_entries.push(LocalExportEntry {
            export_name: "default".to_string(),
            local_name: "*default*".to_string(),
          });
        }

        Stmt::ExportList(export_stmt) => {
          if export_stmt.stx.type_only {
            continue;
          }

          let from = export_stmt
            .stx
            .from
            .as_ref()
            .map(|s| module_request_from_specifier(s));
          if let Some(req) = &from {
            record.requested_modules.push(req.clone());
          }

          match (&export_stmt.stx.names, from) {
            (ExportNames::All(None), Some(req)) => {
              // `export * from "module"`
              record.star_export_entries.push(StarExportEntry { module_request: req });
            }
            (ExportNames::All(Some(alias)), Some(req)) => {
              // `export * as name from "module"`
              record.indirect_export_entries.push(IndirectExportEntry {
                export_name: alias.stx.name.clone(),
                module_request: req,
                import_name: ImportName::All,
              });
            }
            (ExportNames::Specific(names), Some(req)) => {
              // `export {x as y} from "module"`
              for name in names {
                record.indirect_export_entries.push(IndirectExportEntry {
                  export_name: name.stx.alias.stx.name.clone(),
                  module_request: req.clone(),
                  import_name: ImportName::Name(name.stx.exportable.as_str().to_string()),
                });
              }
            }
            (ExportNames::Specific(names), None) => {
              // `export {x as y}`
              for name in names {
                record.local_export_entries.push(LocalExportEntry {
                  export_name: name.stx.alias.stx.name.clone(),
                  local_name: name.stx.exportable.as_str().to_string(),
                });
              }
            }
            // `export *` without a `from` clause is not valid syntax; ignore.
            (ExportNames::All(_), None) => {}
          }
        }

        Stmt::VarDecl(var_decl) if var_decl.stx.export => {
          for declarator in &var_decl.stx.declarators {
            let pat = &declarator.pattern.stx.pat;
            let name = match &*pat.stx {
              Pat::Id(id) => id.stx.name.clone(),
              _ => return Err(VmError::Unimplemented("exported destructuring patterns")),
            };

            record.local_export_entries.push(LocalExportEntry {
              export_name: name.clone(),
              local_name: name,
            });
          }
        }

        Stmt::FunctionDecl(func) if func.stx.export || func.stx.export_default => {
          let local_name = func
            .stx
            .name
            .as_ref()
            .map(|n| n.stx.name.clone())
            .unwrap_or_else(|| "*default*".to_string());
          record.local_export_entries.push(LocalExportEntry {
            export_name: if func.stx.export {
              local_name.clone()
            } else {
              "default".to_string()
            },
            local_name,
          });
        }

        Stmt::ClassDecl(class) if class.stx.export || class.stx.export_default => {
          let local_name = class
            .stx
            .name
            .as_ref()
            .map(|n| n.stx.name.clone())
            .unwrap_or_else(|| "*default*".to_string());
          record.local_export_entries.push(LocalExportEntry {
            export_name: if class.stx.export {
              local_name.clone()
            } else {
              "default".to_string()
            },
            local_name,
          });
        }

        _ => {}
      }
    }

    Ok(record)
  }

  /// Implements ECMA-262 `GetExportedNames([exportStarSet])`.
  pub fn get_exported_names(&self, graph: &ModuleGraph, module: ModuleId) -> Vec<String> {
    self.get_exported_names_with_star_set(graph, module, &mut Vec::new())
  }

  pub fn get_exported_names_with_star_set(
    &self,
    graph: &ModuleGraph,
    module: ModuleId,
    export_star_set: &mut Vec<ModuleId>,
  ) -> Vec<String> {
    // 1. If exportStarSet contains module, then
    if export_star_set.contains(&module) {
      // a. Return a new empty List.
      return Vec::new();
    }

    // 2. Append module to exportStarSet.
    export_star_set.push(module);

    // 3. Let exportedNames be a new empty List.
    let mut exported_names = Vec::<String>::new();

    // 4. For each ExportEntry Record e of module.[[LocalExportEntries]], do
    for entry in &self.local_export_entries {
      // a. Append e.[[ExportName]] to exportedNames.
      exported_names.push(entry.export_name.clone());
    }

    // 5. For each ExportEntry Record e of module.[[IndirectExportEntries]], do
    for entry in &self.indirect_export_entries {
      // a. Append e.[[ExportName]] to exportedNames.
      exported_names.push(entry.export_name.clone());
    }

    // 6. For each ExportEntry Record e of module.[[StarExportEntries]], do
    for entry in &self.star_export_entries {
      // a. Let requestedModule be GetImportedModule(module, e.[[ModuleRequest]]).
      let Some(requested_module) = graph.get_imported_module(module, &entry.module_request) else {
        continue;
      };
      // b. Let starNames be requestedModule.GetExportedNames(exportStarSet).
      let star_names =
        graph
          .module(requested_module)
          .get_exported_names_with_star_set(graph, requested_module, export_star_set);

      // c. For each element n of starNames, do
      for name in star_names {
        // i. If SameValue(n, "default") is false, then
        if name == "default" {
          continue;
        }
        // 1. If exportedNames does not contain n, then
        if !exported_names.contains(&name) {
          // a. Append n to exportedNames.
          exported_names.push(name);
        }
      }
    }

    // 7. Return exportedNames.
    exported_names
  }

  /// Implements ECMA-262 `ResolveExport(exportName[, resolveSet])`.
  pub fn resolve_export(
    &self,
    graph: &ModuleGraph,
    module: ModuleId,
    export_name: &str,
  ) -> ResolveExportResult {
    self.resolve_export_with_set(graph, module, export_name, &mut Vec::new())
  }

  pub fn resolve_export_with_set(
    &self,
    graph: &ModuleGraph,
    module: ModuleId,
    export_name: &str,
    resolve_set: &mut Vec<(ModuleId, String)>,
  ) -> ResolveExportResult {
    // 1. For each Record { [[Module]], [[ExportName]] } r of resolveSet, do
    //    a. If module and r.[[Module]] are the same Module Record and SameValue(exportName, r.[[ExportName]]) is true, then
    //       i. Return null.
    if resolve_set
      .iter()
      .any(|(m, name)| *m == module && name == export_name)
    {
      return ResolveExportResult::NotFound;
    }

    // 2. Append the Record { [[Module]]: module, [[ExportName]]: exportName } to resolveSet.
    resolve_set.push((module, export_name.to_string()));

    // 3. For each ExportEntry Record e of module.[[LocalExportEntries]], do
    for entry in &self.local_export_entries {
      // a. If SameValue(exportName, e.[[ExportName]]) is true, then
      if entry.export_name == export_name {
        // i. Assert: module provides the direct binding for this export.
        // ii. Return ResolvedBinding Record { [[Module]]: module, [[BindingName]]: e.[[LocalName]] }.
        return ResolveExportResult::Resolved(ResolvedBinding {
          module,
          binding_name: BindingName::Name(entry.local_name.clone()),
        });
      }
    }

    // 4. For each ExportEntry Record e of module.[[IndirectExportEntries]], do
    for entry in &self.indirect_export_entries {
      // a. If SameValue(exportName, e.[[ExportName]]) is true, then
      if entry.export_name == export_name {
        // i. Let importedModule be GetImportedModule(module, e.[[ModuleRequest]]).
        let Some(imported_module) = graph.get_imported_module(module, &entry.module_request) else {
          return ResolveExportResult::NotFound;
        };
        // ii. If e.[[ImportName]] is all, then
        if entry.import_name == ImportName::All {
          // 1. Return ResolvedBinding Record { [[Module]]: importedModule, [[BindingName]]: namespace }.
          return ResolveExportResult::Resolved(ResolvedBinding {
            module: imported_module,
            binding_name: BindingName::Namespace,
          });
        }

        // iii. Else,
        // 1. Assert: e.[[ImportName]] is a String.
        // 2. Return importedModule.ResolveExport(e.[[ImportName]], resolveSet).
        let import_name = match &entry.import_name {
          ImportName::Name(name) => name,
          ImportName::All => {
            debug_assert!(false, "ImportName::All handled above");
            return ResolveExportResult::NotFound;
          }
        };
        return graph
          .module(imported_module)
          .resolve_export_with_set(graph, imported_module, import_name, resolve_set);
      }
    }

    // 5. If SameValue(exportName, "default") is true, then
    if export_name == "default" {
      // a. Return null.
      return ResolveExportResult::NotFound;
    }

    // 6. Let starResolution be null.
    let mut star_resolution: Option<ResolvedBinding> = None;

    // 7. For each ExportEntry Record e of module.[[StarExportEntries]], do
    for entry in &self.star_export_entries {
      // a. Let importedModule be GetImportedModule(module, e.[[ModuleRequest]]).
      let Some(imported_module) = graph.get_imported_module(module, &entry.module_request) else {
        continue;
      };
      // b. Let resolution be importedModule.ResolveExport(exportName, resolveSet).
      let resolution = graph
        .module(imported_module)
        .resolve_export_with_set(graph, imported_module, export_name, resolve_set);

      // c. If resolution is ambiguous, return ambiguous.
      if resolution == ResolveExportResult::Ambiguous {
        return ResolveExportResult::Ambiguous;
      }

      // d. If resolution is not null, then
      let ResolveExportResult::Resolved(resolution) = resolution else {
        continue;
      };

      // i. If starResolution is null, then
      let Some(existing) = &star_resolution else {
        // 1. Set starResolution to resolution.
        star_resolution = Some(resolution);
        continue;
      };

      // ii. Else,
      // 1. If resolution.[[Module]] and starResolution.[[Module]] are not the same Module Record, return ambiguous.
      // 2. If resolution.[[BindingName]] is not the same as starResolution.[[BindingName]], return ambiguous.
      if existing != &resolution {
        return ResolveExportResult::Ambiguous;
      }
    }

    // 8. Return starResolution.
    match star_resolution {
      Some(binding) => ResolveExportResult::Resolved(binding),
      None => ResolveExportResult::NotFound,
    }
  }
}

fn module_request_from_specifier(specifier: &str) -> ModuleRequest {
  ModuleRequest::new(specifier, Vec::new())
}
