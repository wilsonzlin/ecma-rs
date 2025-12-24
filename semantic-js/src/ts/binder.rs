use super::model::*;
use diagnostics::{Diagnostic, Label, Span, TextRange};
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::sync::Arc;

#[derive(Clone, Debug)]
enum ExportStatus {
  InProgress(ExportMap),
  Done(ExportMap),
}

#[derive(Clone, Debug)]
struct ModuleState {
  _file_id: FileId,
  symbols: SymbolGroups,
  imports: HashMap<String, ImportEntry>,
  export_specs: Vec<ExportSpec>,
  exports: ExportMap,
  export_spans: BTreeMap<String, ExportNamespaceSpans>,
}

impl ModuleState {
  fn new(file_id: FileId) -> Self {
    Self {
      _file_id: file_id,
      symbols: BTreeMap::new(),
      imports: HashMap::new(),
      export_specs: Vec::new(),
      exports: ExportMap::new(),
      export_spans: BTreeMap::new(),
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
    symbols: SymbolTable::new(),
    diagnostics: Vec::new(),
    export_cache: HashMap::new(),
    next_decl_order: 0,
  };
  binder.run(roots)
}

struct Binder<'a, HP: Fn(FileId) -> Arc<HirFile>> {
  resolver: &'a dyn Resolver,
  hir_provider: &'a HP,
  modules: BTreeMap<FileId, ModuleState>,
  symbols: SymbolTable,
  diagnostics: Vec<Diagnostic>,
  export_cache: HashMap<FileId, ExportStatus>,
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

    // Compute exports for every module.
    let files: Vec<FileId> = self.modules.keys().cloned().collect();
    for file in files {
      self.exports_for(file);
    }

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

    let mut global_symbols: BTreeMap<String, SymbolGroup> = BTreeMap::new();
    for module in self.modules.values() {
      for (name, group) in module.symbols.iter() {
        let entry = global_symbols.remove(name);
        let merged = match entry {
          None => group.clone(),
          Some(existing) => merge_groups(existing, group.clone(), &mut self.symbols),
        };
        global_symbols.insert(name.clone(), merged);
      }
    }

    (
      TsProgramSemantics {
        symbols: self.symbols.clone(),
        module_symbols,
        module_exports,
        global_symbols,
      },
      self.diagnostics.clone(),
    )
  }

  fn bind_file(&mut self, hir: Arc<HirFile>) -> Vec<FileId> {
    let mut state = ModuleState::new(hir.file_id);
    let mut deps = Vec::new();

    let mut has_exports = false;
    let mut first_export_span: Option<Span> = None;

    for decl in &hir.decls {
      let namespaces = decl.kind.namespaces();
      let order = self.bump_order();
      let decl_id = self.symbols.alloc_decl(
        hir.file_id,
        decl.name.clone(),
        decl.kind.clone(),
        namespaces,
        decl.is_ambient,
        order,
        Some(decl.def_id),
      );
      let symbol_id = self.add_decl_to_symbols(
        &mut state.symbols,
        &decl.name,
        decl_id,
        namespaces,
        SymbolOrigin::Local,
      );
      match decl.exported {
        Exported::No => {}
        Exported::Named => {
          has_exports = true;
          let span = Span::new(hir.file_id, decl.span);
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
          let span = Span::new(hir.file_id, decl.span);
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

    for import in &hir.imports {
      let target = self.resolve_spec(
        hir.file_id,
        &import.specifier,
        Span::new(hir.file_id, import.specifier_span),
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
        };
        self.add_import_binding(&mut state, hir.file_id, &entry);
      }
      if let Some(ns) = &import.namespace {
        let entry = ImportEntry {
          local: ns.local.clone(),
          from: target,
          imported: ImportItem::Namespace,
          type_only: import.is_type_only || ns.is_type_only,
        };
        self.add_import_binding(&mut state, hir.file_id, &entry);
      }
      for named in &import.named {
        let entry = ImportEntry {
          local: named.local.clone(),
          from: target,
          imported: ImportItem::Named(named.imported.clone()),
          type_only: import.is_type_only || named.is_type_only,
        };
        self.add_import_binding(&mut state, hir.file_id, &entry);
      }
    }

    for export in &hir.exports {
      match export {
        Export::Named(named) => {
          let target = match (named.specifier.as_ref(), named.specifier_span) {
            (Some(spec), Some(span)) => {
              let resolved =
                self.resolve_spec(hir.file_id, spec, Span::new(hir.file_id, span), false);
              if let Some(t) = resolved {
                deps.push(t);
              }
              Some(resolved)
            }
            (Some(spec), None) => {
              let resolved = self.resolve_spec(
                hir.file_id,
                spec,
                Span::new(hir.file_id, TextRange::new(0, 0)),
                false,
              );
              if let Some(t) = resolved {
                deps.push(t);
              }
              Some(resolved)
            }
            _ => None,
          };
          for item in &named.items {
            if named.specifier.is_none() {
              let span = Span::new(hir.file_id, item.exported_span.unwrap_or(item.local_span));
              first_export_span.get_or_insert(span);
              state.export_specs.push(ExportSpec::Local {
                name: item.local.clone(),
                exported_as: item.exported.clone().unwrap_or_else(|| item.local.clone()),
                type_only: named.is_type_only,
                span,
              });
            } else {
              let span = Span::new(hir.file_id, item.exported_span.unwrap_or(item.local_span));
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
          let spec_span = Span::new(hir.file_id, all.specifier_span);
          first_export_span.get_or_insert(spec_span);
          let target = self.resolve_spec(hir.file_id, &all.specifier, spec_span, false);
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
        Export::ExportAssignment { span, .. } => {
          let span = Span::new(hir.file_id, *span);
          first_export_span.get_or_insert(span);
          self.diagnostics.push(Diagnostic::error(
            "BIND1003",
            "export assignments are not supported in this module kind",
            span,
          ));
          has_exports = true;
        }
      }
    }

    if matches!(hir.module_kind, ModuleKind::Script) && has_exports {
      let span = first_export_span.unwrap_or_else(|| Span::new(hir.file_id, TextRange::new(0, 0)));
      self.diagnostics.push(Diagnostic::error(
        "BIND1003",
        "exports are not allowed in script modules",
        span,
      ));
    }

    self.modules.insert(hir.file_id, state);
    deps
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
      order,
      None,
    );
    self.add_decl_to_symbols(
      &mut state.symbols,
      &entry.local,
      decl_id,
      namespaces,
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

  fn add_decl_to_symbols(
    &mut self,
    symbols: &mut SymbolGroups,
    name: &str,
    decl: DeclId,
    namespaces: Namespace,
    origin: SymbolOrigin,
  ) -> SymbolId {
    let group = symbols.remove(name).unwrap_or_else(SymbolGroup::empty);
    let (group, symbol_id) =
      merge_decl_into_group(group, name, decl, namespaces, &mut self.symbols, origin);
    symbols.insert(name.to_string(), group);
    symbol_id
  }

  fn exports_for(&mut self, file: FileId) -> ExportMap {
    if let Some(status) = self.export_cache.get(&file) {
      return match status {
        ExportStatus::InProgress(m) | ExportStatus::Done(m) => m.clone(),
      };
    }
    self
      .export_cache
      .insert(file, ExportStatus::InProgress(ExportMap::new()));
    let mut map = ExportMap::new();
    if let Some(module) = self.modules.get(&file).cloned() {
      let mut export_spans = module.export_spans.clone();
      for spec in &module.export_specs {
        match spec {
          ExportSpec::Local {
            name,
            exported_as,
            type_only,
            span,
          } => {
            self.add_local_export(
              &module,
              name,
              exported_as,
              *type_only,
              *span,
              &mut map,
              &mut export_spans,
            );
          }
          ExportSpec::ReExport {
            from,
            name,
            exported_as,
            type_only,
            span,
          } => {
            self.add_reexport(
              &module,
              *from,
              name,
              exported_as,
              *type_only,
              *span,
              &mut map,
              &mut export_spans,
            );
          }
          ExportSpec::ExportAll {
            from,
            type_only,
            span,
          } => {
            self.add_export_all(
              &module,
              *from,
              *type_only,
              *span,
              &mut map,
              &mut export_spans,
            );
          }
        }
        self
          .export_cache
          .insert(file, ExportStatus::InProgress(map.clone()));
      }
      if let Some(module) = self.modules.get_mut(&file) {
        module.export_spans = export_spans.clone();
      }
    }

    self
      .export_cache
      .insert(file, ExportStatus::Done(map.clone()));
    if let Some(module) = self.modules.get_mut(&file) {
      module.exports = map.clone();
    }
    map
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
  ) {
    if let Some(import) = module.imports.get(name) {
      if let Some(from) = import.from {
        let target_name = match &import.imported {
          ImportItem::Named(n) => n.clone(),
          ImportItem::Default => "default".to_string(),
          ImportItem::Namespace => name.to_string(),
        };
        let target_exports = self.exports_for(from);
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
            insert_export(
              map,
              export_spans,
              exported_as,
              origin_span,
              group,
              &mut self.symbols,
              &mut self.diagnostics,
            );
            return;
          }
        } else {
          self.diagnostics.push(Diagnostic::error(
            "BIND1002",
            format!("cannot find export '{}' in module", target_name),
            origin_span,
          ));
          return;
        }
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
        insert_export(
          map,
          export_spans,
          exported_as,
          origin_span,
          g,
          &mut self.symbols,
          &mut self.diagnostics,
        );
      } else {
        self.diagnostics.push(Diagnostic::error(
          "BIND1002",
          format!("cannot export '{}': symbol not found", name),
          origin_span,
        ));
      }
    } else {
      self.diagnostics.push(Diagnostic::error(
        "BIND1002",
        format!("cannot export '{}': symbol not found", name),
        origin_span,
      ));
    }
  }

  fn add_reexport(
    &mut self,
    _module: &ModuleState,
    from: Option<FileId>,
    name: &str,
    exported_as: &str,
    type_only: bool,
    origin_span: Span,
    map: &mut ExportMap,
    export_spans: &mut BTreeMap<String, ExportNamespaceSpans>,
  ) {
    if let Some(target) = from {
      let target_exports = self.exports_for(target);
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
          insert_export(
            map,
            export_spans,
            exported_as,
            origin_span,
            group,
            &mut self.symbols,
            &mut self.diagnostics,
          );
        }
      } else {
        self.diagnostics.push(Diagnostic::error(
          "BIND1002",
          format!("cannot re-export '{}': not found", name),
          origin_span,
        ));
      }
    }
  }

  fn add_export_all(
    &mut self,
    _module: &ModuleState,
    from: Option<FileId>,
    type_only: bool,
    origin_span: Span,
    map: &mut ExportMap,
    export_spans: &mut BTreeMap<String, ExportNamespaceSpans>,
  ) {
    if let Some(target) = from {
      let target_exports = self.exports_for(target);
      for (name, entry) in target_exports.iter() {
        if name == "default" {
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
          insert_export(
            map,
            export_spans,
            name,
            origin_span,
            group,
            &mut self.symbols,
            &mut self.diagnostics,
          );
        }
      }
    }
  }

  fn bump_order(&mut self) -> u32 {
    let order = self.next_decl_order;
    self.next_decl_order += 1;
    order
  }
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

fn insert_export(
  map: &mut ExportMap,
  spans: &mut BTreeMap<String, ExportNamespaceSpans>,
  name: &str,
  origin_span: Span,
  group: SymbolGroup,
  symbols: &mut SymbolTable,
  diags: &mut Vec<Diagnostic>,
) {
  if let Some(existing) = map.get(name) {
    if let Some(existing_spans) = spans.get(name) {
      for bit in group.namespaces(symbols).iter_bits() {
        let existing_sym = symbol_for_namespace(existing, bit, symbols);
        let new_sym = symbol_for_namespace(&group, bit, symbols);
        if let (Some(existing_sym), Some(new_sym)) = (existing_sym, new_sym) {
          if existing_sym != new_sym {
            let previous = existing_spans.span_for(bit).unwrap_or(origin_span);
            diags.push(
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

  if let Some(existing) = map.remove(name) {
    let merged = merge_groups(existing, group, symbols);
    map.insert(name.to_string(), merged);
  } else {
    map.insert(name.to_string(), group);
  }

  let entry = spans.entry(name.to_string()).or_default();
  for bit in map
    .get(name)
    .expect("just inserted export")
    .namespaces(symbols)
    .iter_bits()
  {
    entry.set_if_empty(bit, origin_span);
  }
}

fn merge_groups(a: SymbolGroup, b: SymbolGroup, symbols: &mut SymbolTable) -> SymbolGroup {
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
