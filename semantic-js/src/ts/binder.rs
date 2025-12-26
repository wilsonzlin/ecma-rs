use super::model::*;
use diagnostics::{sort_diagnostics, Diagnostic, Label, Span, TextRange};
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::sync::Arc;

const EXPORT_EQUALS_NAME: &str = "export=";
const DEFAULT_EXPORT_NAME: &str = "default";

#[derive(Clone, Debug)]
struct ModuleState {
  symbols: SymbolGroups,
  imports: BTreeMap<String, ImportEntry>,
  export_specs: Vec<ExportSpec>,
  exports: ExportMap,
  export_spans: BTreeMap<String, ExportNamespaceSpans>,
  export_as_namespace: Vec<ExportAsNamespaceEntry>,
}

impl ModuleState {
  fn new(_file_id: FileId) -> Self {
    Self {
      symbols: BTreeMap::new(),
      imports: BTreeMap::new(),
      export_specs: Vec::new(),
      exports: ExportMap::new(),
      export_spans: BTreeMap::new(),
      export_as_namespace: Vec::new(),
    }
  }
}

#[derive(Clone, Debug)]
enum ExportSpec {
  Local {
    name: String,
    exported_as: String,
    type_only: bool,
    span: Span,
  },
  ReExport {
    from: Option<FileId>,
    name: String,
    exported_as: String,
    type_only: bool,
    span: Span,
  },
  ExportAll {
    from: Option<FileId>,
    type_only: bool,
    span: Span,
  },
  ExportEquals {
    expr: String,
    span: Span,
  },
}

#[derive(Clone, Debug)]
struct ExportAsNamespaceEntry {
  name: String,
  span: Span,
}

#[derive(Clone, Copy, Debug, Default)]
struct ExportNamespaceSpans {
  value: Option<Span>,
  ty: Option<Span>,
  namespace: Option<Span>,
}

impl ExportNamespaceSpans {
  fn span_for(&self, ns: Namespace) -> Option<Span> {
    match ns {
      Namespace::VALUE => self.value,
      Namespace::TYPE => self.ty,
      Namespace::NAMESPACE => self.namespace,
      _ => None,
    }
  }

  fn set_if_empty(&mut self, ns: Namespace, span: Span) {
    match ns {
      Namespace::VALUE => {
        if self.value.is_none() {
          self.value = Some(span);
        }
      }
      Namespace::TYPE => {
        if self.ty.is_none() {
          self.ty = Some(span);
        }
      }
      Namespace::NAMESPACE => {
        if self.namespace.is_none() {
          self.namespace = Some(span);
        }
      }
      _ => {}
    }
  }
}

pub fn bind_ts_program(
  roots: &[FileId],
  resolver: &dyn Resolver,
  hir_provider: impl Fn(FileId) -> Arc<HirFile>,
) -> (TsProgramSemantics, Vec<Diagnostic>) {
  let mut binder = Binder {
    resolver,
    hir_provider: &hir_provider,
    modules: BTreeMap::new(),
    ambient_modules: BTreeMap::new(),
    symbols: SymbolTable::new(),
    global_symbols: BTreeMap::new(),
    diagnostics: Vec::new(),
    next_decl_order: 0,
  };
  binder.run(roots)
}

struct Binder<'a, HP: Fn(FileId) -> Arc<HirFile>> {
  resolver: &'a dyn Resolver,
  hir_provider: &'a HP,
  modules: BTreeMap<FileId, ModuleState>,
  ambient_modules: BTreeMap<String, ModuleState>,
  symbols: SymbolTable,
  global_symbols: SymbolGroups,
  diagnostics: Vec<Diagnostic>,
  next_decl_order: u32,
}

impl<'a, HP: Fn(FileId) -> Arc<HirFile>> Binder<'a, HP> {
  fn run(&mut self, roots: &[FileId]) -> (TsProgramSemantics, Vec<Diagnostic>) {
    let mut queue: VecDeque<FileId> = roots.iter().cloned().collect();
    let mut seen = HashMap::new();
    while let Some(file_id) = queue.pop_front() {
      if seen.insert(file_id, ()).is_some() {
        continue;
      }
      if self.modules.contains_key(&file_id) {
        continue;
      }
      let hir = (self.hir_provider)(file_id);
      let deps = self.bind_file(hir.clone());
      queue.extend(deps);
    }

    self.compute_exports();

    self.apply_export_as_namespace();

    let module_exports = self
      .modules
      .iter()
      .map(|(id, m)| (*id, m.exports.clone()))
      .collect();
    let module_symbols = self
      .modules
      .iter()
      .map(|(id, m)| (*id, m.symbols.clone()))
      .collect();
    let ambient_module_symbols = self
      .ambient_modules
      .iter()
      .map(|(name, m)| (name.clone(), m.symbols.clone()))
      .collect();
    let ambient_module_exports = self
      .ambient_modules
      .iter()
      .map(|(name, m)| (name.clone(), m.exports.clone()))
      .collect();

    let global_symbols = self.global_symbols.clone();

    sort_diagnostics(&mut self.diagnostics);
    (
      TsProgramSemantics {
        symbols: self.symbols.clone(),
        module_symbols,
        module_exports,
        global_symbols,
        ambient_module_symbols,
        ambient_module_exports,
      },
      self.diagnostics.clone(),
    )
  }

  fn push_diag_once(&mut self, diag: Diagnostic) {
    if !self.diagnostics.contains(&diag) {
      self.diagnostics.push(diag);
    }
  }

  fn bind_file(&mut self, hir: Arc<HirFile>) -> Vec<FileId> {
    let mut state = ModuleState::new(hir.file_id);
    let mut deps = Vec::new();
    let is_script = self.is_effective_script(
      hir.module_kind,
      hir.file_kind,
      &hir.imports,
      &hir.exports,
      &hir.decls,
      &hir.export_as_namespace,
      &hir.ambient_modules,
    );

    self.bind_module_items(
      &mut state,
      hir.file_id,
      hir.file_kind,
      hir.module_kind,
      is_script,
      false,
      &hir.decls,
      &hir.imports,
      &hir.exports,
      &hir.export_as_namespace,
      &mut deps,
    );

    for ambient in &hir.ambient_modules {
      deps.extend(self.bind_ambient_module(hir.file_id, hir.file_kind, ambient));
    }

    self.modules.insert(hir.file_id, state);
    deps
  }

  fn bind_ambient_module(
    &mut self,
    file_id: FileId,
    file_kind: FileKind,
    module: &AmbientModule,
  ) -> Vec<FileId> {
    let mut deps = Vec::new();
    let mut state = self
      .ambient_modules
      .remove(&module.name)
      .unwrap_or_else(|| ModuleState::new(file_id));

    self.bind_module_items(
      &mut state,
      file_id,
      file_kind,
      ModuleKind::Module,
      false,
      true,
      &module.decls,
      &module.imports,
      &module.exports,
      &module.export_as_namespace,
      &mut deps,
    );

    for nested in &module.ambient_modules {
      deps.extend(self.bind_ambient_module(file_id, file_kind, nested));
    }

    self.ambient_modules.insert(module.name.clone(), state);
    deps
  }

  fn bind_module_items(
    &mut self,
    state: &mut ModuleState,
    file_id: FileId,
    file_kind: FileKind,
    _module_kind: ModuleKind,
    is_script: bool,
    implicit_export: bool,
    decls: &[Decl],
    imports: &[Import],
    exports: &[Export],
    export_as_namespace: &[ExportAsNamespace],
    deps: &mut Vec<FileId>,
  ) {
    let mut has_exports = false;
    let mut first_export_span: Option<Span> = None;
    let mut import_def_ids = HashMap::new();

    for decl in decls {
      if matches!(decl.kind, DeclKind::ImportBinding) {
        import_def_ids
          .entry(decl.name.clone())
          .or_insert(decl.def_id);
        continue;
      }
      let namespaces = decl.kind.namespaces();
      let order = self.bump_order();
      let decl_id = self.symbols.alloc_decl(
        file_id,
        decl.name.clone(),
        decl.kind.clone(),
        namespaces,
        decl.is_ambient,
        decl.is_global,
        order,
        Some(decl.def_id),
      );
      let symbol_id = add_decl_to_groups(
        &mut state.symbols,
        &decl.name,
        decl_id,
        namespaces,
        &mut self.symbols,
        SymbolOrigin::Local,
      );
      if self.decl_participates_in_global_kind(file_kind, decl, is_script) {
        add_decl_to_groups(
          &mut self.global_symbols,
          &decl.name,
          decl_id,
          namespaces,
          &mut self.symbols,
          SymbolOrigin::Local,
        );
      } else if decl.is_global && file_kind != FileKind::Dts {
        let span = Span::new(file_id, decl.span);
        self.diagnostics.push(Diagnostic::error(
          "BIND2001",
          "global augmentations in non-.d.ts modules are not supported yet",
          span,
        ));
      }
      match decl.exported {
        Exported::No => {
          if implicit_export {
            has_exports = true;
            let span = Span::new(file_id, decl.span);
            first_export_span.get_or_insert(span);
            state.export_specs.push(ExportSpec::Local {
              name: decl.name.clone(),
              exported_as: decl.name.clone(),
              type_only: false,
              span,
            })
          }
        }
        Exported::Named => {
          has_exports = true;
          let span = Span::new(file_id, decl.span);
          first_export_span.get_or_insert(span);
          state.export_specs.push(ExportSpec::Local {
            name: decl.name.clone(),
            exported_as: decl.name.clone(),
            type_only: false,
            span,
          })
        }
        Exported::Default => {
          has_exports = true;
          let span = Span::new(file_id, decl.span);
          first_export_span.get_or_insert(span);
          state.export_specs.push(ExportSpec::Local {
            name: decl.name.clone(),
            exported_as: "default".to_string(),
            type_only: false,
            span,
          })
        }
      }

      // Keep namespaces stored on symbol entry.
      let sym = self.symbols.symbol_mut(symbol_id);
      sym.namespaces |= namespaces;
    }

    for import in imports {
      let target = self.resolve_spec(
        file_id,
        &import.specifier,
        Span::new(file_id, import.specifier_span),
        true,
      );
      if let Some(t) = target {
        deps.push(t);
      }
      if let Some(default) = &import.default {
        let entry = ImportEntry {
          local: default.local.clone(),
          from: target,
          imported: ImportItem::Default,
          type_only: import.is_type_only || default.is_type_only,
          def_id: import_def_ids.get(&default.local).copied(),
        };
        self.add_import_binding(state, file_id, &entry);
      }
      if let Some(ns) = &import.namespace {
        let entry = ImportEntry {
          local: ns.local.clone(),
          from: target,
          imported: ImportItem::Namespace,
          type_only: import.is_type_only || ns.is_type_only,
          def_id: import_def_ids.get(&ns.local).copied(),
        };
        self.add_import_binding(state, file_id, &entry);
      }
      for named in &import.named {
        let entry = ImportEntry {
          local: named.local.clone(),
          from: target,
          imported: ImportItem::Named(named.imported.clone()),
          type_only: import.is_type_only || named.is_type_only,
          def_id: import_def_ids.get(&named.local).copied(),
        };
        self.add_import_binding(state, file_id, &entry);
      }
    }

    for export in exports {
      match export {
        Export::Named(named) => {
          let span_range = named
            .specifier_span
            .or_else(|| named.items.first().and_then(|i| i.exported_span))
            .or_else(|| named.items.first().map(|i| i.local_span))
            .unwrap_or_else(|| TextRange::new(0, 0));
          let target = match (named.specifier.as_ref(), Some(span_range)) {
            (Some(spec), Some(span)) => {
              let resolved = self.resolve_spec(file_id, spec, Span::new(file_id, span), false);
              if let Some(t) = resolved {
                deps.push(t);
              }
              Some(resolved)
            }
            _ => None,
          };
          for item in &named.items {
            if named.specifier.is_none() {
              let span = Span::new(file_id, item.exported_span.unwrap_or(item.local_span));
              first_export_span.get_or_insert(span);
              state.export_specs.push(ExportSpec::Local {
                name: item.local.clone(),
                exported_as: item.exported.clone().unwrap_or_else(|| item.local.clone()),
                type_only: named.is_type_only,
                span,
              });
            } else {
              let span = Span::new(file_id, item.exported_span.unwrap_or(item.local_span));
              first_export_span.get_or_insert(span);
              state.export_specs.push(ExportSpec::ReExport {
                from: target.flatten(),
                name: item.local.clone(),
                exported_as: item.exported.clone().unwrap_or_else(|| item.local.clone()),
                type_only: named.is_type_only,
                span,
              });
            }
          }
          has_exports |= !named.items.is_empty();
        }
        Export::All(all) => {
          let spec_span = Span::new(file_id, all.specifier_span);
          first_export_span.get_or_insert(spec_span);
          let target = self.resolve_spec(file_id, &all.specifier, spec_span, false);
          if let Some(t) = target {
            deps.push(t);
          }
          state.export_specs.push(ExportSpec::ExportAll {
            from: target,
            type_only: all.is_type_only,
            span: spec_span,
          });
          has_exports = true;
        }
        Export::ExportAssignment { span, expr } => {
          let span = Span::new(file_id, *span);
          first_export_span.get_or_insert(span);
          if !is_script {
            state.export_specs.push(ExportSpec::ExportEquals {
              expr: expr.clone(),
              span,
            });
          }
          has_exports = true;
        }
      }
    }

    for export in export_as_namespace {
      let span = Span::new(file_id, export.span);
      first_export_span.get_or_insert(span);
      if !state
        .export_as_namespace
        .iter()
        .any(|existing| existing.name == export.name && existing.span == span)
      {
        state.export_as_namespace.push(ExportAsNamespaceEntry {
          name: export.name.clone(),
          span,
        });
      }
      has_exports = true;
    }

    if is_script && has_exports {
      let span = first_export_span.unwrap_or_else(|| Span::new(file_id, TextRange::new(0, 0)));
      self.diagnostics.push(Diagnostic::error(
        "BIND1003",
        "exports are not allowed in script modules",
        span,
      ));
    }
  }

  fn decl_participates_in_global_kind(
    &self,
    file_kind: FileKind,
    decl: &Decl,
    is_script: bool,
  ) -> bool {
    if is_script {
      return true;
    }
    decl.is_global && matches!(file_kind, FileKind::Dts)
  }

  fn is_effective_script(
    &self,
    module_kind: ModuleKind,
    file_kind: FileKind,
    imports: &[Import],
    exports: &[Export],
    decls: &[Decl],
    export_as_namespace: &[ExportAsNamespace],
    ambient_modules: &[AmbientModule],
  ) -> bool {
    match module_kind {
      ModuleKind::Script => true,
      ModuleKind::Module => {
        matches!(file_kind, FileKind::Dts)
          && imports.is_empty()
          && exports.is_empty()
          && export_as_namespace.is_empty()
          && ambient_modules.is_empty()
          && decls
            .iter()
            .all(|decl| matches!(decl.exported, Exported::No))
      }
    }
  }

  fn add_import_binding(&mut self, state: &mut ModuleState, file: FileId, entry: &ImportEntry) {
    state.imports.insert(entry.local.clone(), entry.clone());
    let namespaces = if entry.type_only {
      Namespace::TYPE
    } else {
      match entry.imported {
        ImportItem::Namespace => Namespace::VALUE | Namespace::NAMESPACE | Namespace::TYPE,
        _ => Namespace::VALUE | Namespace::TYPE,
      }
    };
    let order = self.bump_order();
    let decl_id = self.symbols.alloc_decl(
      file,
      entry.local.clone(),
      DeclKind::ImportBinding,
      namespaces,
      false,
      false,
      order,
      entry.def_id,
    );
    add_decl_to_groups(
      &mut state.symbols,
      &entry.local,
      decl_id,
      namespaces,
      &mut self.symbols,
      SymbolOrigin::Import {
        from: entry.from,
        imported: match &entry.imported {
          ImportItem::Named(n) => n.clone(),
          ImportItem::Default => "default".to_string(),
          ImportItem::Namespace => "*".to_string(),
        },
      },
    );
  }

  fn resolve_spec(
    &mut self,
    from: FileId,
    spec: &str,
    span: Span,
    is_import: bool,
  ) -> Option<FileId> {
    let resolved = self.resolver.resolve(from, spec);
    if resolved.is_none() {
      let message = format!(
        "unresolved {}: {}",
        if is_import { "import" } else { "export" },
        spec
      );
      self
        .diagnostics
        .push(Diagnostic::error("BIND1002", message, span));
    }
    resolved
  }

  fn compute_exports(&mut self) {
    let module_ids: Vec<FileId> = self.modules.keys().cloned().collect();
    let mut changed = true;
    while changed {
      changed = false;
      for file in module_ids.iter() {
        let Some(module) = self.modules.get(file).cloned() else {
          continue;
        };
        let mut export_spans = module.export_spans.clone();
        let mut map = module.exports.clone();
        let mut module_changed = false;
        for spec in &module.export_specs {
          if self.apply_export_spec(&module, spec, &mut map, &mut export_spans, false) {
            module_changed = true;
          }
        }
        if module_changed {
          changed = true;
          if let Some(state) = self.modules.get_mut(file) {
            state.exports = map.clone();
            state.export_spans = export_spans.clone();
          }
        }
      }
    }

    for file in module_ids {
      let Some(module) = self.modules.get(&file).cloned() else {
        continue;
      };
      let mut export_spans = module.export_spans.clone();
      let mut map = module.exports.clone();
      for spec in &module.export_specs {
        let _ = self.apply_export_spec(&module, spec, &mut map, &mut export_spans, true);
      }
      if let Some(state) = self.modules.get_mut(&file) {
        state.exports = map;
        state.export_spans = export_spans;
      }
    }

    let ambient_ids: Vec<String> = self.ambient_modules.keys().cloned().collect();
    let mut ambient_changed = true;
    while ambient_changed {
      ambient_changed = false;
      for name in ambient_ids.iter() {
        let Some(module) = self.ambient_modules.get(name).cloned() else {
          continue;
        };
        let mut export_spans = module.export_spans.clone();
        let mut map = module.exports.clone();
        let mut module_changed = false;
        for spec in &module.export_specs {
          if self.apply_export_spec(&module, spec, &mut map, &mut export_spans, false) {
            module_changed = true;
          }
        }
        if module_changed {
          ambient_changed = true;
          if let Some(state) = self.ambient_modules.get_mut(name) {
            state.exports = map.clone();
            state.export_spans = export_spans.clone();
          }
        }
      }
    }

    for name in ambient_ids {
      let Some(module) = self.ambient_modules.get(&name).cloned() else {
        continue;
      };
      let mut export_spans = module.export_spans.clone();
      let mut map = module.exports.clone();
      for spec in &module.export_specs {
        let _ = self.apply_export_spec(&module, spec, &mut map, &mut export_spans, true);
      }
      if let Some(state) = self.ambient_modules.get_mut(&name) {
        state.exports = map;
        state.export_spans = export_spans;
      }
    }
  }

  fn apply_export_spec(
    &mut self,
    module: &ModuleState,
    spec: &ExportSpec,
    map: &mut ExportMap,
    export_spans: &mut BTreeMap<String, ExportNamespaceSpans>,
    emit_missing: bool,
  ) -> bool {
    match spec {
      ExportSpec::Local {
        name,
        exported_as,
        type_only,
        span,
      } => self.add_local_export(
        module,
        name,
        exported_as,
        *type_only,
        *span,
        map,
        export_spans,
        emit_missing,
      ),
      ExportSpec::ReExport {
        from,
        name,
        exported_as,
        type_only,
        span,
      } => self.add_reexport(
        *from,
        name,
        exported_as,
        *type_only,
        *span,
        map,
        export_spans,
        emit_missing,
      ),
      ExportSpec::ExportAll {
        from,
        type_only,
        span,
      } => self.add_export_all(*from, *type_only, *span, map, export_spans),
      ExportSpec::ExportEquals { expr, span } => {
        self.add_export_assignment(module, expr, *span, map, export_spans, emit_missing)
      }
    }
  }

  fn add_local_export(
    &mut self,
    module: &ModuleState,
    name: &str,
    exported_as: &str,
    type_only: bool,
    origin_span: Span,
    map: &mut ExportMap,
    export_spans: &mut BTreeMap<String, ExportNamespaceSpans>,
    emit_missing: bool,
  ) -> bool {
    if let Some(import) = module.imports.get(name) {
      if let Some(from) = import.from {
        let target_name = match &import.imported {
          ImportItem::Named(n) => n.clone(),
          ImportItem::Default => "default".to_string(),
          ImportItem::Namespace => name.to_string(),
        };
        let target_exports = self
          .modules
          .get(&from)
          .map(|m| m.exports.clone())
          .unwrap_or_default();
        if let Some(entry) = target_exports.get(&target_name) {
          let filtered = filter_group(
            entry.clone(),
            if type_only || import.type_only {
              Namespace::TYPE
            } else {
              Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE
            },
            &self.symbols,
          );
          if let Some(group) = filtered {
            return self.insert_export(map, export_spans, exported_as, origin_span, group);
          } else if emit_missing {
            self.push_diag_once(Diagnostic::error(
              "BIND1002",
              format!("cannot find export '{}' in module", target_name),
              origin_span,
            ));
          }
        } else if emit_missing {
          self.push_diag_once(Diagnostic::error(
            "BIND1002",
            format!("cannot find export '{}' in module", target_name),
            origin_span,
          ));
        }
        return false;
      }
    }

    if let Some(group) = module.symbols.get(name) {
      let filtered = filter_group(
        group.clone(),
        if type_only {
          Namespace::TYPE
        } else {
          Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE
        },
        &self.symbols,
      );
      if let Some(g) = filtered {
        return self.insert_export(map, export_spans, exported_as, origin_span, g);
      } else if emit_missing {
        self.push_diag_once(Diagnostic::error(
          "BIND1002",
          format!("cannot export '{}': symbol not found", name),
          origin_span,
        ));
      }
    } else if emit_missing {
      self.push_diag_once(Diagnostic::error(
        "BIND1002",
        format!("cannot export '{}': symbol not found", name),
        origin_span,
      ));
    }
    false
  }

  fn add_reexport(
    &mut self,
    from: Option<FileId>,
    name: &str,
    exported_as: &str,
    type_only: bool,
    origin_span: Span,
    map: &mut ExportMap,
    export_spans: &mut BTreeMap<String, ExportNamespaceSpans>,
    emit_missing: bool,
  ) -> bool {
    let Some(target) = from else {
      return false;
    };
    let target_exports = self
      .modules
      .get(&target)
      .map(|m| m.exports.clone())
      .unwrap_or_default();
    if let Some(entry) = target_exports.get(name) {
      if let Some(group) = filter_group(
        entry.clone(),
        if type_only {
          Namespace::TYPE
        } else {
          Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE
        },
        &self.symbols,
      ) {
        return self.insert_export(map, export_spans, exported_as, origin_span, group);
      } else if emit_missing {
        self.push_diag_once(Diagnostic::error(
          "BIND1002",
          format!("cannot re-export '{}': not found", name),
          origin_span,
        ));
      }
    } else if emit_missing {
      self.push_diag_once(Diagnostic::error(
        "BIND1002",
        format!("cannot re-export '{}': not found", name),
        origin_span,
      ));
    }
    false
  }

  fn add_export_assignment(
    &mut self,
    module: &ModuleState,
    expr: &str,
    origin_span: Span,
    map: &mut ExportMap,
    export_spans: &mut BTreeMap<String, ExportNamespaceSpans>,
    emit_missing: bool,
  ) -> bool {
    if expr.is_empty() {
      if emit_missing {
        self.push_diag_once(Diagnostic::error(
          "BIND1002",
          "export assignment must target an identifier",
          origin_span,
        ));
      }
      return false;
    }

    let mut changed = self.add_local_export(
      module,
      expr,
      EXPORT_EQUALS_NAME,
      false,
      origin_span,
      map,
      export_spans,
      emit_missing,
    );

    if let Some(group) = map.get(EXPORT_EQUALS_NAME).cloned() {
      if self.insert_export(map, export_spans, DEFAULT_EXPORT_NAME, origin_span, group) {
        changed = true;
      }
    }

    changed
  }

  fn add_export_all(
    &mut self,
    from: Option<FileId>,
    type_only: bool,
    origin_span: Span,
    map: &mut ExportMap,
    export_spans: &mut BTreeMap<String, ExportNamespaceSpans>,
  ) -> bool {
    let Some(target) = from else {
      return false;
    };
    let target_exports = self
      .modules
      .get(&target)
      .map(|m| m.exports.clone())
      .unwrap_or_default();
    let mut changed = false;
    for (name, entry) in target_exports.iter() {
      if name == DEFAULT_EXPORT_NAME || name == EXPORT_EQUALS_NAME {
        continue;
      }
      if let Some(group) = filter_group(
        entry.clone(),
        if type_only {
          Namespace::TYPE
        } else {
          Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE
        },
        &self.symbols,
      ) {
        if self.insert_export(map, export_spans, name, origin_span, group) {
          changed = true;
        }
      }
    }
    changed
  }

  fn apply_export_as_namespace(&mut self) {
    let module_ids: Vec<FileId> = self.modules.keys().copied().collect();
    for file in module_ids {
      if let Some(state) = self.modules.get(&file).cloned() {
        for entry in state.export_as_namespace {
          self.add_export_as_namespace_binding(&entry, &state.exports);
        }
      }
    }

    let ambient_ids: Vec<String> = self.ambient_modules.keys().cloned().collect();
    for name in ambient_ids {
      if let Some(state) = self.ambient_modules.get(&name).cloned() {
        for entry in state.export_as_namespace {
          self.add_export_as_namespace_binding(&entry, &state.exports);
        }
      }
    }
  }

  fn add_export_as_namespace_binding(
    &mut self,
    entry: &ExportAsNamespaceEntry,
    exports: &ExportMap,
  ) {
    let mut target = exports.get(EXPORT_EQUALS_NAME).and_then(|g| {
      filter_group(
        g.clone(),
        Namespace::VALUE | Namespace::NAMESPACE,
        &self.symbols,
      )
    });

    if target.is_none() {
      target = exports.get(DEFAULT_EXPORT_NAME).and_then(|g| {
        filter_group(
          g.clone(),
          Namespace::VALUE | Namespace::NAMESPACE,
          &self.symbols,
        )
      });
    }

    if target.is_none() {
      for group in exports.values() {
        if let Some(filtered) = filter_group(
          group.clone(),
          Namespace::VALUE | Namespace::NAMESPACE,
          &self.symbols,
        ) {
          target = Some(filtered);
          break;
        }
      }
    }

    let Some(group) = target else {
      self.push_diag_once(Diagnostic::error(
        "BIND1002",
        format!(
          "cannot export namespace '{}': module has no value or namespace exports",
          entry.name
        ),
        entry.span,
      ));
      return;
    };

    if let Some(existing) = self.global_symbols.remove(&entry.name) {
      let merged = merge_groups(existing, group, &mut self.symbols);
      self.global_symbols.insert(entry.name.clone(), merged);
    } else {
      self.global_symbols.insert(entry.name.clone(), group);
    }
  }

  fn bump_order(&mut self) -> u32 {
    let order = self.next_decl_order;
    self.next_decl_order += 1;
    order
  }
}

fn add_decl_to_groups(
  symbols: &mut SymbolGroups,
  name: &str,
  decl: DeclId,
  namespaces: Namespace,
  table: &mut SymbolTable,
  origin: SymbolOrigin,
) -> SymbolId {
  let group = symbols.remove(name).unwrap_or_else(SymbolGroup::empty);
  let (group, symbol_id) = merge_decl_into_group(group, name, decl, namespaces, table, origin);
  symbols.insert(name.to_string(), group);
  symbol_id
}

fn filter_group(group: SymbolGroup, mask: Namespace, symbols: &SymbolTable) -> Option<SymbolGroup> {
  let available = group.namespaces(symbols) & mask;
  if available.is_empty() {
    return None;
  }
  match group.kind {
    SymbolGroupKind::Merged(sym) => {
      if available == (Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE) {
        Some(SymbolGroup::merged(sym))
      } else {
        // Return separate entries only for the requested namespaces.
        let mut value = None;
        let mut ty = None;
        let mut namespace = None;
        if available.contains(Namespace::VALUE) {
          value = Some(sym);
        }
        if available.contains(Namespace::TYPE) {
          ty = Some(sym);
        }
        if available.contains(Namespace::NAMESPACE) {
          namespace = Some(sym);
        }
        Some(SymbolGroup {
          kind: SymbolGroupKind::Separate {
            value,
            ty,
            namespace,
          },
        })
      }
    }
    SymbolGroupKind::Separate {
      value,
      ty,
      namespace,
    } => {
      let mut new_value = None;
      let mut new_ty = None;
      let mut new_namespace = None;
      if available.contains(Namespace::VALUE) {
        new_value = value;
      }
      if available.contains(Namespace::TYPE) {
        new_ty = ty;
      }
      if available.contains(Namespace::NAMESPACE) {
        new_namespace = namespace;
      }
      Some(SymbolGroup {
        kind: SymbolGroupKind::Separate {
          value: new_value,
          ty: new_ty,
          namespace: new_namespace,
        },
      })
    }
  }
}

fn merge_decl_into_group(
  group: SymbolGroup,
  name: &str,
  decl: DeclId,
  namespaces: Namespace,
  symbols: &mut SymbolTable,
  origin: SymbolOrigin,
) -> (SymbolGroup, SymbolId) {
  if namespaces.is_empty() {
    return (group, SymbolId(0));
  }

  if let SymbolGroupKind::Merged(sym) = group.kind.clone() {
    symbols.add_decl_to_symbol(sym, decl, namespaces);
    return (SymbolGroup::merged(sym), sym);
  }

  if !namespaces.is_single() {
    // Create a merged symbol that includes any existing declarations as well.
    let merged_sym = build_merged_symbol(&group, name, decl, namespaces, symbols, origin.clone());
    return (SymbolGroup::merged(merged_sym), merged_sym);
  }

  let mut value = match &group.kind {
    SymbolGroupKind::Separate { value, .. } => *value,
    _ => None,
  };
  let mut ty = match &group.kind {
    SymbolGroupKind::Separate { ty, .. } => *ty,
    _ => None,
  };
  let mut namespace_sym = match &group.kind {
    SymbolGroupKind::Separate { namespace, .. } => *namespace,
    _ => None,
  };

  let target_slot = if namespaces.contains(Namespace::VALUE) {
    &mut value
  } else if namespaces.contains(Namespace::TYPE) {
    &mut ty
  } else {
    &mut namespace_sym
  };

  let symbol_id = if let Some(sym) = target_slot {
    symbols.add_decl_to_symbol(*sym, decl, namespaces);
    *sym
  } else {
    let sym = symbols.alloc_symbol(name, namespaces, origin.clone());
    symbols.add_decl_to_symbol(sym, decl, namespaces);
    *target_slot = Some(sym);
    sym
  };

  // Namespace + namespace merging happens automatically by using the same slot.
  // Value + namespace merges for specific declaration kinds.
  if should_merge_value_namespace(&value, &namespace_sym, symbols) {
    let merged_sym = build_merged_symbol(
      &SymbolGroup {
        kind: SymbolGroupKind::Separate {
          value,
          ty,
          namespace: namespace_sym,
        },
      },
      name,
      decl,
      Namespace::empty(),
      symbols,
      origin,
    );
    return (SymbolGroup::merged(merged_sym), merged_sym);
  }

  (
    SymbolGroup {
      kind: SymbolGroupKind::Separate {
        value,
        ty,
        namespace: namespace_sym,
      },
    },
    symbol_id,
  )
}

fn build_merged_symbol(
  group: &SymbolGroup,
  name: &str,
  new_decl: DeclId,
  namespaces: Namespace,
  symbols: &mut SymbolTable,
  origin: SymbolOrigin,
) -> SymbolId {
  let mut decls: [Vec<DeclId>; 3] = Default::default();
  collect_decls(group, symbols, &mut decls);
  for bit in namespaces.iter_bits() {
    decls[ns_index(bit)].push(new_decl);
  }

  for d in decls.iter_mut() {
    d.sort_by_key(|d| symbols.decl(*d).order);
    d.dedup();
  }

  let mut mask = Namespace::empty();
  for (idx, bit) in [Namespace::VALUE, Namespace::TYPE, Namespace::NAMESPACE]
    .iter()
    .enumerate()
  {
    if !decls[idx].is_empty() {
      mask |= *bit;
    }
  }

  let sym = symbols.alloc_symbol(name, mask, origin);
  for bit in mask.iter_bits() {
    for d in decls[ns_index(bit)].iter() {
      symbols.add_decl_to_symbol(sym, *d, bit);
    }
  }
  sym
}

fn collect_decls(group: &SymbolGroup, symbols: &SymbolTable, out: &mut [Vec<DeclId>; 3]) {
  match &group.kind {
    SymbolGroupKind::Merged(sym) => {
      let symbol = symbols.symbol(*sym);
      for bit in symbol.namespaces.iter_bits() {
        out[ns_index(bit)].extend(symbol.decls_for(bit).iter().copied());
      }
    }
    SymbolGroupKind::Separate {
      value,
      ty,
      namespace,
    } => {
      if let Some(sym) = value {
        out[ns_index(Namespace::VALUE)].extend(
          symbols
            .symbol(*sym)
            .decls_for(Namespace::VALUE)
            .iter()
            .copied(),
        );
      }
      if let Some(sym) = ty {
        out[ns_index(Namespace::TYPE)].extend(
          symbols
            .symbol(*sym)
            .decls_for(Namespace::TYPE)
            .iter()
            .copied(),
        );
      }
      if let Some(sym) = namespace {
        out[ns_index(Namespace::NAMESPACE)].extend(
          symbols
            .symbol(*sym)
            .decls_for(Namespace::NAMESPACE)
            .iter()
            .copied(),
        );
      }
    }
  }
}

fn should_merge_value_namespace(
  value: &Option<SymbolId>,
  namespace: &Option<SymbolId>,
  symbols: &SymbolTable,
) -> bool {
  if value.is_none() || namespace.is_none() {
    return false;
  }
  if let Some(sym) = value {
    let sym = symbols.symbol(*sym);
    if let Some(first) = sym.decls_for(Namespace::VALUE).first() {
      let decl_kind = &symbols.decl(*first).kind;
      matches!(
        decl_kind,
        DeclKind::Function | DeclKind::Class | DeclKind::Enum
      )
    } else {
      false
    }
  } else {
    false
  }
}

fn namespace_name(ns: Namespace) -> &'static str {
  match ns {
    Namespace::VALUE => "value",
    Namespace::TYPE => "type",
    Namespace::NAMESPACE => "namespace",
    _ => "unknown",
  }
}

fn groups_equal(a: &SymbolGroup, b: &SymbolGroup, symbols: &SymbolTable) -> bool {
  for bit in [Namespace::VALUE, Namespace::TYPE, Namespace::NAMESPACE] {
    if symbol_for_namespace(a, bit, symbols) != symbol_for_namespace(b, bit, symbols) {
      return false;
    }
  }
  true
}

fn merge_groups(a: SymbolGroup, b: SymbolGroup, symbols: &SymbolTable) -> SymbolGroup {
  let mut temp: [Vec<SymbolId>; 3] = Default::default();

  for bit in [Namespace::VALUE, Namespace::TYPE, Namespace::NAMESPACE] {
    if let Some(sym) = symbol_for_namespace(&a, bit, symbols) {
      temp[ns_index(bit)].push(sym);
    }
    if let Some(sym) = symbol_for_namespace(&b, bit, symbols) {
      temp[ns_index(bit)].push(sym);
    }
  }

  for bucket in temp.iter_mut() {
    bucket.sort_by_key(|s| s.0);
    bucket.dedup();
  }

  let value = temp[0].first().copied();
  let ty = temp[1].first().copied();
  let namespace = temp[2].first().copied();

  // If all namespaces use the same symbol and it contains them, keep merged.
  let same_symbol = value == ty && ty == namespace && value.is_some();
  if same_symbol {
    return SymbolGroup::merged(value.unwrap());
  }

  SymbolGroup {
    kind: SymbolGroupKind::Separate {
      value,
      ty,
      namespace,
    },
  }
}

impl<'a, HP: Fn(FileId) -> Arc<HirFile>> Binder<'a, HP> {
  fn insert_export(
    &mut self,
    map: &mut ExportMap,
    spans: &mut BTreeMap<String, ExportNamespaceSpans>,
    name: &str,
    origin_span: Span,
    group: SymbolGroup,
  ) -> bool {
    if let Some(existing) = map.get(name) {
      if let Some(existing_spans) = spans.get(name) {
        for bit in group.namespaces(&self.symbols).iter_bits() {
          let existing_sym = symbol_for_namespace(existing, bit, &self.symbols);
          let new_sym = symbol_for_namespace(&group, bit, &self.symbols);
          if let (Some(existing_sym), Some(new_sym)) = (existing_sym, new_sym) {
            if existing_sym != new_sym {
              let previous = existing_spans.span_for(bit).unwrap_or(origin_span);
              self.push_diag_once(
                Diagnostic::error(
                  "BIND1001",
                  format!(
                    "duplicate export of '{}' in {} namespace",
                    name,
                    namespace_name(bit)
                  ),
                  origin_span,
                )
                .with_label(Label::secondary(previous, "previous export here")),
              );
            }
          }
        }
      }
    }

    let existing = map.remove(name);
    let merged = if let Some(existing) = existing.clone() {
      merge_groups(existing, group, &self.symbols)
    } else {
      group
    };
    let changed = existing
      .as_ref()
      .map(|old| !groups_equal(old, &merged, &self.symbols))
      .unwrap_or(true);
    map.insert(name.to_string(), merged.clone());

    let entry = spans.entry(name.to_string()).or_default();
    for bit in merged.namespaces(&self.symbols).iter_bits() {
      entry.set_if_empty(bit, origin_span);
    }
    changed
  }
}

fn symbol_for_namespace(
  group: &SymbolGroup,
  ns: Namespace,
  symbols: &SymbolTable,
) -> Option<SymbolId> {
  match &group.kind {
    SymbolGroupKind::Merged(sym) => {
      if symbols.symbol(*sym).namespaces.contains(ns) {
        Some(*sym)
      } else {
        None
      }
    }
    SymbolGroupKind::Separate {
      value,
      ty,
      namespace,
    } => match ns {
      Namespace::VALUE => value.and_then(|s| {
        if symbols.symbol(s).namespaces.contains(Namespace::VALUE) {
          Some(s)
        } else {
          None
        }
      }),
      Namespace::TYPE => ty.and_then(|s| {
        if symbols.symbol(s).namespaces.contains(Namespace::TYPE) {
          Some(s)
        } else {
          None
        }
      }),
      Namespace::NAMESPACE => namespace.and_then(|s| {
        if symbols.symbol(s).namespaces.contains(Namespace::NAMESPACE) {
          Some(s)
        } else {
          None
        }
      }),
      _ => None,
    },
  }
}
