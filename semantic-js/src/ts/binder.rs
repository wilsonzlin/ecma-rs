use super::model::*;
use diagnostics::{sort_diagnostics, Diagnostic, Label, Span, TextRange};
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

#[derive(Clone, Debug)]
enum ExportStatus {
  InProgress(ExportMap),
  Done(ExportMap),
}

#[derive(Clone, Debug)]
struct ModuleState {
  owner: SymbolOwner,
  file_id: FileId,
  file_kind: FileKind,
  is_script: bool,
  symbols: SymbolGroups,
  imports: BTreeMap<String, ImportEntry>,
  import_module_refs: Vec<ModuleRefEntry>,
  export_specs: Vec<ExportSpec>,
  exports: ExportMap,
  export_spans: BTreeMap<String, ExportNamespaceSpans>,
  export_as_namespace: Vec<ExportAsNamespaceEntry>,
}

impl ModuleState {
  fn new(owner: SymbolOwner, file_id: FileId, file_kind: FileKind, is_script: bool) -> Self {
    Self {
      owner,
      file_id,
      file_kind,
      is_script,
      symbols: BTreeMap::new(),
      imports: BTreeMap::new(),
      import_module_refs: Vec::new(),
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
    from: ModuleRef,
    from_span: Span,
    name: String,
    exported_as: String,
    type_only: bool,
    span: Span,
  },
  ExportAll {
    from: ModuleRef,
    from_span: Span,
    type_only: bool,
    span: Span,
  },
  ExportAllAlias {
    from: ModuleRef,
    from_span: Span,
    exported_as: String,
    type_only: bool,
    span: Span,
  },
  ExportAssignment {
    target: String,
    span: Span,
  },
}

#[derive(Clone, Debug)]
struct ExportAsNamespaceEntry {
  name: String,
  span: Span,
}

#[derive(Clone, Debug)]
struct ModuleRefEntry {
  module: ModuleRef,
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
  bind_ts_program_with_cancellation(roots, resolver, hir_provider, None)
}

pub fn bind_ts_program_with_cancellation(
  roots: &[FileId],
  resolver: &dyn Resolver,
  hir_provider: impl Fn(FileId) -> Arc<HirFile>,
  cancelled: Option<&AtomicBool>,
) -> (TsProgramSemantics, Vec<Diagnostic>) {
  let mut binder = Binder {
    resolver,
    hir_provider: &hir_provider,
    cancelled,
    modules: BTreeMap::new(),
    ambient_modules: BTreeMap::new(),
    symbols: SymbolTable::new(),
    global_symbols: BTreeMap::new(),
    diagnostics: Vec::new(),
    export_cache: HashMap::new(),
    ambient_export_cache: HashMap::new(),
    pending_file_augmentations: Vec::new(),
  };
  binder.run(roots)
}

struct Binder<'a, HP: Fn(FileId) -> Arc<HirFile>> {
  resolver: &'a dyn Resolver,
  hir_provider: &'a HP,
  cancelled: Option<&'a AtomicBool>,
  modules: BTreeMap<FileId, ModuleState>,
  ambient_modules: BTreeMap<String, ModuleState>,
  symbols: SymbolTable,
  global_symbols: SymbolGroups,
  diagnostics: Vec<Diagnostic>,
  export_cache: HashMap<FileId, ExportStatus>,
  ambient_export_cache: HashMap<String, ExportStatus>,
  pending_file_augmentations: Vec<PendingModuleAugmentation>,
}

#[derive(Clone, Debug)]
struct PendingModuleAugmentation {
  target: FileId,
  origin: FileId,
  origin_file_kind: FileKind,
  module: AmbientModule,
}

impl<'a, HP: Fn(FileId) -> Arc<HirFile>> Binder<'a, HP> {
  #[inline]
  fn is_cancelled(&self) -> bool {
    self
      .cancelled
      .is_some_and(|cancelled| cancelled.load(Ordering::Relaxed))
  }

  fn run(&mut self, roots: &[FileId]) -> (TsProgramSemantics, Vec<Diagnostic>) {
    if self.is_cancelled() {
      return (TsProgramSemantics::empty(), Vec::new());
    }
    let mut queue: VecDeque<FileId> = roots.iter().cloned().collect();
    let mut seen = HashMap::new();
    while !queue.is_empty() || !self.pending_file_augmentations.is_empty() {
      while let Some(file_id) = queue.pop_front() {
        if self.is_cancelled() {
          return (TsProgramSemantics::empty(), Vec::new());
        }
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

      if !self.pending_file_augmentations.is_empty() {
        if self.is_cancelled() {
          return (TsProgramSemantics::empty(), Vec::new());
        }
        let deps = self.apply_pending_augmentations();
        queue.extend(deps);
      }
    }

    if self.is_cancelled() {
      return (TsProgramSemantics::empty(), Vec::new());
    }
    self.reconcile_unresolved();

    // Compute exports for every module.
    let files: Vec<FileId> = self.modules.keys().cloned().collect();
    for file in files {
      if self.is_cancelled() {
        return (TsProgramSemantics::empty(), Vec::new());
      }
      self.exports_for(file);
    }

    // Compute exports for ambient modules.
    let ambient_specs: Vec<String> = self.ambient_modules.keys().cloned().collect();
    for spec in ambient_specs {
      if self.is_cancelled() {
        return (TsProgramSemantics::empty(), Vec::new());
      }
      self.exports_for_ambient(&spec);
    }

    if self.is_cancelled() {
      return (TsProgramSemantics::empty(), Vec::new());
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

    let module_states: Vec<ModuleState> = self.modules.values().cloned().collect();
    let ambient_states: Vec<ModuleState> = self.ambient_modules.values().cloned().collect();
    let mut export_as_namespace_spans = BTreeMap::new();
    for state in module_states.iter() {
      if self.is_cancelled() {
        return (TsProgramSemantics::empty(), Vec::new());
      }
      self.handle_export_as_namespace(state, &mut export_as_namespace_spans);
    }
    for state in ambient_states.iter() {
      if self.is_cancelled() {
        return (TsProgramSemantics::empty(), Vec::new());
      }
      self.handle_export_as_namespace(state, &mut export_as_namespace_spans);
    }

    let global_symbols = self.global_symbols.clone();

    if self.is_cancelled() {
      return (TsProgramSemantics::empty(), Vec::new());
    }
    let mut def_to_symbol = BTreeMap::new();
    for sym in self.symbols.symbols.values() {
      if self.is_cancelled() {
        return (TsProgramSemantics::empty(), Vec::new());
      }
      for ns in [Namespace::VALUE, Namespace::TYPE, Namespace::NAMESPACE] {
        if !sym.namespaces.contains(ns) {
          continue;
        }
        for decl_id in sym.decls_for(ns).iter().copied() {
          let decl = self.symbols.decl(decl_id);
          def_to_symbol.entry((decl.def_id, ns)).or_insert(sym.id);
        }
      }
    }

    sort_diagnostics(&mut self.diagnostics);
    (
      TsProgramSemantics {
        symbols: self.symbols.clone(),
        module_symbols,
        module_exports,
        global_symbols,
        ambient_module_symbols,
        ambient_module_exports,
        def_to_symbol,
      },
      self.diagnostics.clone(),
    )
  }

  fn bind_file(&mut self, hir: Arc<HirFile>) -> Vec<FileId> {
    if self.is_cancelled() {
      return Vec::new();
    }
    let is_script = self.is_effective_script(
      hir.module_kind,
      hir.file_kind,
      &hir.imports,
      &hir.import_equals,
      &hir.exports,
      &hir.decls,
      &hir.export_as_namespace,
      &hir.ambient_modules,
    );
    let owner = SymbolOwner::Module(hir.file_id);
    let mut state = ModuleState::new(owner.clone(), hir.file_id, hir.file_kind, is_script);
    let mut deps = Vec::new();

    self.bind_module_items(
      &mut state,
      &owner,
      hir.file_id,
      hir.file_kind,
      hir.module_kind,
      is_script,
      false,
      &hir.decls,
      &hir.imports,
      &hir.import_equals,
      &hir.exports,
      &hir.export_as_namespace,
      &hir.ambient_modules,
      &mut deps,
    );

    for ambient in &hir.ambient_modules {
      if is_script {
        deps.extend(self.bind_ambient_module(hir.file_id, hir.file_kind, ambient));
        continue;
      }

      if let Some(target) = self.resolver.resolve(hir.file_id, &ambient.name) {
        self
          .pending_file_augmentations
          .push(PendingModuleAugmentation {
            target,
            origin: hir.file_id,
            origin_file_kind: hir.file_kind,
            module: ambient.clone(),
          });
        deps.push(target);
      } else {
        deps.extend(self.bind_ambient_module(hir.file_id, hir.file_kind, ambient));
      }
    }

    self.modules.insert(hir.file_id, state);
    deps
  }

  fn apply_pending_augmentations(&mut self) -> Vec<FileId> {
    if self.is_cancelled() {
      return Vec::new();
    }
    if self.pending_file_augmentations.is_empty() {
      return Vec::new();
    }

    self.pending_file_augmentations.sort_by(|a, b| {
      a.target
        .cmp(&b.target)
        .then_with(|| a.origin.cmp(&b.origin))
        .then_with(|| a.module.name_span.start.cmp(&b.module.name_span.start))
        .then_with(|| a.module.name_span.end.cmp(&b.module.name_span.end))
    });

    let pending = std::mem::take(&mut self.pending_file_augmentations);
    let mut deps = Vec::new();
    for aug in pending {
      if let Some(mut state) = self.modules.remove(&aug.target) {
        let owner = SymbolOwner::Module(aug.target);
        self.bind_module_items(
          &mut state,
          &owner,
          aug.origin,
          aug.origin_file_kind,
          ModuleKind::Module,
          false,
          false,
          &aug.module.decls,
          &aug.module.imports,
          &aug.module.import_equals,
          &aug.module.exports,
          &aug.module.export_as_namespace,
          &aug.module.ambient_modules,
          &mut deps,
        );

        for nested in &aug.module.ambient_modules {
          deps.extend(self.bind_ambient_module(aug.origin, aug.origin_file_kind, nested));
        }

        self.modules.insert(aug.target, state);
      }
    }

    deps
  }

  fn bind_ambient_module(
    &mut self,
    file_id: FileId,
    file_kind: FileKind,
    module: &AmbientModule,
  ) -> Vec<FileId> {
    if self.is_cancelled() {
      return Vec::new();
    }
    let mut deps = Vec::new();
    let owner = SymbolOwner::AmbientModule(module.name.clone());
    let mut state = self
      .ambient_modules
      .remove(&module.name)
      .unwrap_or_else(|| ModuleState::new(owner.clone(), file_id, file_kind, false));

    self.bind_module_items(
      &mut state,
      &owner,
      file_id,
      file_kind,
      ModuleKind::Module,
      false,
      true,
      &module.decls,
      &module.imports,
      &module.import_equals,
      &module.exports,
      &module.export_as_namespace,
      &module.ambient_modules,
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
    owner: &SymbolOwner,
    file_id: FileId,
    file_kind: FileKind,
    _module_kind: ModuleKind,
    is_script: bool,
    implicit_export: bool,
    decls: &[Decl],
    imports: &[Import],
    import_equals: &[ImportEquals],
    exports: &[Export],
    export_as_namespace: &[ExportAsNamespace],
    ambient_modules: &[AmbientModule],
    deps: &mut Vec<FileId>,
  ) {
    let mut has_exports = false;
    let mut first_export_span: Option<Span> = None;
    let mut has_export_assignment = false;
    let mut has_other_exports = false;
    let mut export_assignment_span: Option<Span> = None;
    let mut import_def_ids = HashMap::new();

    for decl in decls {
      if matches!(decl.kind, DeclKind::ImportBinding) {
        import_def_ids
          .entry(decl.name.clone())
          .or_insert(decl.def_id);
        continue;
      }
      let namespaces = decl.kind.namespaces();
      let order = decl.span.start;
      let decl_id = self.symbols.alloc_decl(
        file_id,
        decl.name.clone(),
        decl.kind.clone(),
        namespaces,
        decl.is_ambient,
        decl.is_global,
        order,
        Some(decl.def_id),
        None,
      );
      let _symbol_id = add_decl_to_groups(
        &mut state.symbols,
        &decl.name,
        decl_id,
        namespaces,
        &mut self.symbols,
        SymbolOrigin::Local,
        owner,
      );
      if self.decl_participates_in_global_kind(file_kind, decl, is_script) {
        add_decl_to_groups(
          &mut self.global_symbols,
          &decl.name,
          decl_id,
          namespaces,
          &mut self.symbols,
          SymbolOrigin::Local,
          &SymbolOwner::Global,
        );
      }
      match decl.exported {
         Exported::No => {
           if implicit_export {
             has_exports = true;
            has_other_exports = true;
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
          has_other_exports = true;
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
          has_other_exports = true;
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
    }

    for import in imports {
      let specifier_span = Span::new(file_id, import.specifier_span);
      let target = self.resolve_spec(
        file_id,
        &import.specifier,
        specifier_span,
        true,
        ambient_modules,
      );
      if let ModuleRef::File(t) = &target {
        deps.push(*t);
      }
      state.import_module_refs.push(ModuleRefEntry {
        module: target.clone(),
        span: specifier_span,
      });
      if let Some(default) = &import.default {
        let entry = ImportEntry {
          local: default.local.clone(),
          from: target.clone(),
          imported: ImportItem::Default,
          type_only: import.is_type_only || default.is_type_only,
          def_id: import_def_ids.get(&default.local).copied(),
          local_span: default.local_span,
          specifier_span,
          symbol: SymbolId(0),
        };
        self.add_import_binding(state, owner, file_id, entry);
      }
      if let Some(ns) = &import.namespace {
        let entry = ImportEntry {
          local: ns.local.clone(),
          from: target.clone(),
          imported: ImportItem::Namespace,
          type_only: import.is_type_only || ns.is_type_only,
          def_id: import_def_ids.get(&ns.local).copied(),
          local_span: ns.local_span,
          specifier_span,
          symbol: SymbolId(0),
        };
        self.add_import_binding(state, owner, file_id, entry);
      }
      for named in &import.named {
        let entry = ImportEntry {
          local: named.local.clone(),
          from: target.clone(),
          imported: ImportItem::Named(named.imported.clone()),
          type_only: import.is_type_only || named.is_type_only,
          def_id: import_def_ids.get(&named.local).copied(),
          local_span: named.local_span,
          specifier_span,
          symbol: SymbolId(0),
        };
        self.add_import_binding(state, owner, file_id, entry);
      }
    }

    for import in import_equals {
      match &import.target {
        ImportEqualsTarget::Require {
          specifier,
          specifier_span,
        } => {
          let span = Span::new(file_id, *specifier_span);
          let target = self.resolve_spec(file_id, specifier, span, true, ambient_modules);
          if let ModuleRef::File(t) = &target {
            deps.push(*t);
          }
          state.import_module_refs.push(ModuleRefEntry {
            module: target.clone(),
            span,
          });
          let entry = ImportEntry {
            local: import.local.clone(),
            from: target.clone(),
            imported: ImportItem::Namespace,
            type_only: false,
            def_id: import_def_ids.get(&import.local).copied(),
            local_span: import.local_span,
            specifier_span: span,
            symbol: SymbolId(0),
          };
          self.add_import_binding(state, owner, file_id, entry);
        }
        ImportEqualsTarget::EntityName { path, span } => {
          let namespaces = Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE;
          let order = import.local_span.start;
          let decl_id = self.symbols.alloc_decl(
            file_id,
            import.local.clone(),
            DeclKind::ImportBinding,
            namespaces,
            false,
            false,
            order,
            import_def_ids.get(&import.local).copied(),
            Some(AliasTarget::EntityName {
              path: path.clone(),
              span: *span,
            }),
          );
          add_decl_to_groups(
            &mut state.symbols,
            &import.local,
            decl_id,
            namespaces,
            &mut self.symbols,
            SymbolOrigin::Local,
            owner,
          );
        }
      }

      if import.is_exported {
        has_exports = true;
        let span = Span::new(file_id, import.local_span);
        first_export_span.get_or_insert(span);
        state.export_specs.push(ExportSpec::Local {
          name: import.local.clone(),
          exported_as: import.local.clone(),
          type_only: false,
          span,
        });
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
          let target = named.specifier.as_ref().map(|spec| {
            let spec_span = Span::new(file_id, span_range);
            let resolved = self.resolve_spec(file_id, spec, spec_span, false, ambient_modules);
            if let ModuleRef::File(t) = &resolved {
              deps.push(*t);
            }
            (resolved, spec_span)
          });
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
              let (from, from_span) = target.as_ref().expect("re-export has specifier");
              state.export_specs.push(ExportSpec::ReExport {
                from: from.clone(),
                from_span: *from_span,
                name: item.local.clone(),
                exported_as: item.exported.clone().unwrap_or_else(|| item.local.clone()),
                type_only: named.is_type_only,
                span,
              });
            }
          }
          has_exports |= !named.items.is_empty();
          has_other_exports |= !named.items.is_empty();
        }
        Export::All(all) => {
          let spec_span = Span::new(file_id, all.specifier_span);
          first_export_span.get_or_insert(spec_span);
          let target =
            self.resolve_spec(file_id, &all.specifier, spec_span, false, ambient_modules);
          if let ModuleRef::File(t) = &target {
            deps.push(*t);
          }
          if let Some(alias) = &all.alias {
            let alias_span = Span::new(file_id, all.alias_span.unwrap_or(all.specifier_span));
            first_export_span.get_or_insert(alias_span);
            state.export_specs.push(ExportSpec::ExportAllAlias {
              from: target.clone(),
              from_span: spec_span,
              exported_as: alias.clone(),
              type_only: all.is_type_only,
              span: alias_span,
            });
          } else {
            state.export_specs.push(ExportSpec::ExportAll {
              from: target.clone(),
              from_span: spec_span,
              type_only: all.is_type_only,
              span: spec_span,
            });
          }
          has_exports = true;
          has_other_exports = true;
        }
        Export::ExportAssignment { expr, span } => {
          let span = Span::new(file_id, *span);
          first_export_span.get_or_insert(span);
          if has_export_assignment {
            has_other_exports = true;
          }
          has_export_assignment = true;
          export_assignment_span.get_or_insert(span);
          if expr.is_empty() {
            if !is_script {
              self.diagnostics.push(Diagnostic::error(
                "BIND1003",
                "export assignment expressions other than identifiers are not supported yet",
                span,
              ));
            }
          } else {
            state.export_specs.push(ExportSpec::ExportAssignment {
              target: expr.clone(),
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
      has_other_exports = true;
    }

    if has_export_assignment && has_other_exports && !is_script {
      let span = export_assignment_span
        .or(first_export_span)
        .unwrap_or_else(|| Span::new(file_id, TextRange::new(0, 0)));
      self.diagnostics.push(Diagnostic::error(
        "BIND1005",
        "export assignments cannot be combined with other exports",
        span,
      ));
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
    _file_kind: FileKind,
    decl: &Decl,
    is_script: bool,
  ) -> bool {
    if is_script {
      return true;
    }
    decl.is_global
  }

  fn is_effective_script(
    &self,
    module_kind: ModuleKind,
    file_kind: FileKind,
    imports: &[Import],
    import_equals: &[ImportEquals],
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
          && import_equals
            .iter()
            .all(|ie| !matches!(ie.target, ImportEqualsTarget::Require { .. }))
          && exports.is_empty()
          && export_as_namespace.is_empty()
          && ambient_modules.is_empty()
          && decls
            .iter()
            .all(|decl| matches!(decl.exported, Exported::No))
      }
    }
  }

  fn reconcile_unresolved(&mut self) {
    let mut seen: BTreeSet<(FileId, TextRange)> = BTreeSet::new();
    let module_ids: Vec<FileId> = self.modules.keys().cloned().collect();
    for id in module_ids {
      if let Some(mut module) = self.modules.remove(&id) {
        self.reconcile_module_state(&mut module, &mut seen);
        self.modules.insert(id, module);
      }
    }
    let ambient_ids: Vec<String> = self.ambient_modules.keys().cloned().collect();
    for name in ambient_ids {
      if let Some(mut module) = self.ambient_modules.remove(&name) {
        self.reconcile_module_state(&mut module, &mut seen);
        self.ambient_modules.insert(name, module);
      }
    }
  }

  fn reconcile_module_state(
    &mut self,
    state: &mut ModuleState,
    seen: &mut BTreeSet<(FileId, TextRange)>,
  ) {
    for import in state.import_module_refs.iter_mut() {
      self.rewrite_module_ref(&mut import.module, import.span, true, seen);
    }

    for entry in state.imports.values_mut() {
      self.rewrite_module_ref(&mut entry.from, entry.specifier_span, true, seen);
      self.update_import_origin(entry);
    }

    for spec in state.export_specs.iter_mut() {
      match spec {
        ExportSpec::Local { .. } | ExportSpec::ExportAssignment { .. } => {}
        ExportSpec::ReExport {
          from, from_span, ..
        } => {
          self.rewrite_module_ref(from, *from_span, false, seen);
        }
        ExportSpec::ExportAll {
          from, from_span, ..
        } => {
          self.rewrite_module_ref(from, *from_span, false, seen);
        }
        ExportSpec::ExportAllAlias {
          from, from_span, ..
        } => {
          self.rewrite_module_ref(from, *from_span, false, seen);
        }
      }
    }
  }

  fn rewrite_module_ref(
    &mut self,
    reference: &mut ModuleRef,
    span: Span,
    is_import: bool,
    seen: &mut BTreeSet<(FileId, TextRange)>,
  ) {
    if let ModuleRef::Unresolved(spec) = reference {
      if self.ambient_modules.contains_key(spec) {
        *reference = ModuleRef::Ambient(spec.clone());
      } else if seen.insert((span.file, span.range)) {
        let message = format!(
          "unresolved {}: {}",
          if is_import { "import" } else { "export" },
          spec
        );
        self
          .diagnostics
          .push(Diagnostic::error("BIND1002", message, span));
      }
    }
  }

  fn update_import_origin(&mut self, entry: &ImportEntry) {
    let imported = match &entry.imported {
      ImportItem::Named(n) => n.clone(),
      ImportItem::Default => "default".to_string(),
      ImportItem::Namespace => "*".to_string(),
    };
    let symbol = self.symbols.symbol_mut(entry.symbol);
    symbol.origin = SymbolOrigin::Import {
      from: entry.from.clone(),
      imported,
    };
  }

  fn handle_export_as_namespace(&mut self, state: &ModuleState, seen: &mut BTreeMap<String, Span>) {
    for export in &state.export_as_namespace {
      if state.is_script {
        continue;
      }

      if state.file_kind != FileKind::Dts {
        self.diagnostics.push(Diagnostic::error(
          "BIND1003",
          "export as namespace is only supported in .d.ts files",
          export.span,
        ));
        continue;
      }

      if let Some(previous) = seen.get(&export.name) {
        if previous.file != export.span.file {
          self.diagnostics.push(
            Diagnostic::error(
              "BIND1006",
              format!(
                "conflicting export as namespace '{}' from multiple modules",
                export.name
              ),
              export.span,
            )
            .with_label(Label::secondary(
              *previous,
              "previous export as namespace here",
            )),
          );
        }
      } else {
        seen.insert(export.name.clone(), export.span);
      }

      self.insert_export_as_namespace_symbol(state, export);
    }
  }

  fn insert_export_as_namespace_symbol(
    &mut self,
    state: &ModuleState,
    export: &ExportAsNamespaceEntry,
  ) {
    let namespaces = Namespace::VALUE | Namespace::NAMESPACE | Namespace::TYPE;
    let decl_id = self.symbols.alloc_decl(
      export.span.file,
      export.name.clone(),
      DeclKind::ImportBinding,
      namespaces,
      true,
      true,
      export.span.range.start,
      None,
      None,
    );
    add_decl_to_groups(
      &mut self.global_symbols,
      &export.name,
      decl_id,
      namespaces,
      &mut self.symbols,
      SymbolOrigin::Import {
        from: ModuleRef::File(state.file_id),
        imported: "*".to_string(),
      },
      &SymbolOwner::Global,
    );
  }

  fn add_import_binding(
    &mut self,
    state: &mut ModuleState,
    owner: &SymbolOwner,
    file: FileId,
    mut entry: ImportEntry,
  ) {
    if let Some(existing) = state.imports.get(&entry.local) {
      let same_from = existing.from == entry.from;
      let same_item = existing.imported == entry.imported;
      if !(same_from && same_item) {
        let previous = Span::new(file, existing.local_span);
        let current = Span::new(file, entry.local_span);
        self.diagnostics.push(
          Diagnostic::error(
            "BIND1004",
            format!("duplicate import binding: '{}'", entry.local),
            current,
          )
          .with_label(Label::secondary(previous, "previous binding here")),
        );
      }
    }

    let is_namespace_import = matches!(&entry.imported, ImportItem::Namespace);
    let namespaces = if entry.type_only {
      if is_namespace_import {
        Namespace::TYPE | Namespace::NAMESPACE
      } else {
        Namespace::TYPE
      }
    } else if is_namespace_import {
      Namespace::VALUE | Namespace::NAMESPACE | Namespace::TYPE
    } else {
      Namespace::VALUE | Namespace::TYPE
    };
    let order = entry.local_span.start;
    let decl_id = self.symbols.alloc_decl(
      file,
      entry.local.clone(),
      DeclKind::ImportBinding,
      namespaces,
      false,
      false,
      order,
      entry.def_id,
      None,
    );
    let symbol = add_decl_to_groups(
      &mut state.symbols,
      &entry.local,
      decl_id,
      namespaces,
      &mut self.symbols,
      SymbolOrigin::Import {
        from: entry.from.clone(),
        imported: match &entry.imported {
          ImportItem::Named(n) => n.clone(),
          ImportItem::Default => "default".to_string(),
          ImportItem::Namespace => "*".to_string(),
        },
      },
      owner,
    );
    entry.symbol = symbol;
    state.imports.insert(entry.local.clone(), entry);
  }

  fn resolve_spec(
    &mut self,
    from: FileId,
    spec: &str,
    _span: Span,
    _is_import: bool,
    ambient_modules: &[AmbientModule],
  ) -> ModuleRef {
    if let Some(resolved) = self.resolver.resolve(from, spec) {
      return ModuleRef::File(resolved);
    }

    if self.ambient_modules.contains_key(spec) || has_ambient_module_named(spec, ambient_modules) {
      return ModuleRef::Ambient(spec.to_string());
    }

    ModuleRef::Unresolved(spec.to_string())
  }

  fn exports_for(&mut self, file: FileId) -> ExportMap {
    if self.is_cancelled() {
      return ExportMap::new();
    }
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
        if self.is_cancelled() {
          let empty = ExportMap::new();
          self
            .export_cache
            .insert(file, ExportStatus::Done(empty.clone()));
          return empty;
        }
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
            ..
          } => {
            self.add_reexport(
              &module,
              from,
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
            ..
          } => {
            self.add_export_all(
              &module,
              from,
              *type_only,
              *span,
              &mut map,
              &mut export_spans,
            );
          }
          ExportSpec::ExportAllAlias {
            from,
            exported_as,
            type_only,
            span,
            ..
          } => {
            self.add_export_all_alias(
              &module,
              from,
              exported_as,
              *type_only,
              *span,
              &mut map,
              &mut export_spans,
            );
          }
          ExportSpec::ExportAssignment { target, span } => {
            self.add_export_assignment(&module, target, *span, &mut map, &mut export_spans);
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

  fn exports_for_ambient(&mut self, name: &str) -> ExportMap {
    if self.is_cancelled() {
      return ExportMap::new();
    }
    if let Some(status) = self.ambient_export_cache.get(name) {
      return match status {
        ExportStatus::InProgress(m) | ExportStatus::Done(m) => m.clone(),
      };
    }
    self
      .ambient_export_cache
      .insert(name.to_string(), ExportStatus::InProgress(ExportMap::new()));
    let mut map = ExportMap::new();
    if let Some(module) = self.ambient_modules.get(name).cloned() {
      let mut export_spans = module.export_spans.clone();
      for spec in &module.export_specs {
        if self.is_cancelled() {
          let empty = ExportMap::new();
          self
            .ambient_export_cache
            .insert(name.to_string(), ExportStatus::Done(empty.clone()));
          return empty;
        }
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
            ..
          } => {
            self.add_reexport(
              &module,
              from,
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
            ..
          } => {
            self.add_export_all(
              &module,
              from,
              *type_only,
              *span,
              &mut map,
              &mut export_spans,
            );
          }
          ExportSpec::ExportAllAlias {
            from,
            exported_as,
            type_only,
            span,
            ..
          } => {
            self.add_export_all_alias(
              &module,
              from,
              exported_as,
              *type_only,
              *span,
              &mut map,
              &mut export_spans,
            );
          }
          ExportSpec::ExportAssignment { target, span } => {
            self.add_export_assignment(&module, target, *span, &mut map, &mut export_spans);
          }
        }
        self
          .ambient_export_cache
          .insert(name.to_string(), ExportStatus::InProgress(map.clone()));
      }
      if let Some(module) = self.ambient_modules.get_mut(name) {
        module.export_spans = export_spans.clone();
      }
    }

    self
      .ambient_export_cache
      .insert(name.to_string(), ExportStatus::Done(map.clone()));
    if let Some(module) = self.ambient_modules.get_mut(name) {
      module.exports = map.clone();
    }
    map
  }

  fn exports_for_ref(&mut self, reference: &ModuleRef) -> Option<ExportMap> {
    match reference {
      ModuleRef::File(file) => Some(self.exports_for(*file)),
      ModuleRef::Ambient(spec) => Some(self.exports_for_ambient(spec)),
      ModuleRef::Unresolved(_) => None,
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
  ) {
    if let Some(import) = module.imports.get(name) {
      if matches!(import.imported, ImportItem::Namespace) {
        if let Some(group) = module.symbols.get(name) {
          let filtered = filter_group(
            group.clone(),
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
        }
      } else {
        let target_name = match &import.imported {
          ImportItem::Named(n) => n.clone(),
          ImportItem::Default => "default".to_string(),
          ImportItem::Namespace => unreachable!("handled above"),
        };
        if let Some(target_exports) = self.exports_for_ref(&import.from) {
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
          } else if matches!(import.from, ModuleRef::File(_) | ModuleRef::Ambient(_)) {
            self.diagnostics.push(Diagnostic::error(
              "BIND1002",
              format!("cannot find export '{}' in module", target_name),
              origin_span,
            ));
            return;
          }
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
    from: &ModuleRef,
    name: &str,
    exported_as: &str,
    type_only: bool,
    origin_span: Span,
    map: &mut ExportMap,
    export_spans: &mut BTreeMap<String, ExportNamespaceSpans>,
  ) {
    if let Some(target_exports) = self.exports_for_ref(from) {
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
      } else if matches!(from, ModuleRef::File(_) | ModuleRef::Ambient(_)) {
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
    from: &ModuleRef,
    type_only: bool,
    origin_span: Span,
    map: &mut ExportMap,
    export_spans: &mut BTreeMap<String, ExportNamespaceSpans>,
  ) {
    if let Some(target_exports) = self.exports_for_ref(from) {
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

  fn add_export_all_alias(
    &mut self,
    module: &ModuleState,
    from: &ModuleRef,
    exported_as: &str,
    type_only: bool,
    origin_span: Span,
    map: &mut ExportMap,
    export_spans: &mut BTreeMap<String, ExportNamespaceSpans>,
  ) {
    let namespaces = if type_only {
      Namespace::TYPE
    } else {
      Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE
    };
    if matches!(from, ModuleRef::Unresolved(_)) {
      return;
    }
    let sym = self.symbols.alloc_symbol(
      &module.owner,
      exported_as,
      namespaces,
      SymbolOrigin::Import {
        from: from.clone(),
        imported: "*".to_string(),
      },
    );
    insert_export(
      map,
      export_spans,
      exported_as,
      origin_span,
      SymbolGroup::merged(sym),
      &mut self.symbols,
      &mut self.diagnostics,
    );
  }

  fn add_export_assignment(
    &mut self,
    module: &ModuleState,
    target: &str,
    origin_span: Span,
    map: &mut ExportMap,
    export_spans: &mut BTreeMap<String, ExportNamespaceSpans>,
  ) {
    if let Some(group) = module.symbols.get(target) {
      let type_only = module
        .imports
        .get(target)
        .map(|import| import.type_only)
        .unwrap_or(false);
      let mask = if type_only {
        Namespace::TYPE
      } else {
        Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE
      };
      if let Some(filtered) = filter_group(group.clone(), mask, &self.symbols) {
        insert_export(
          map,
          export_spans,
          "default",
          origin_span,
          filtered,
          &mut self.symbols,
          &mut self.diagnostics,
        );
        return;
      }
    }

    self.diagnostics.push(Diagnostic::error(
      "BIND1002",
      format!("cannot find export assignment target '{}'", target),
      origin_span,
    ));
  }
}

fn has_ambient_module_named(specifier: &str, modules: &[AmbientModule]) -> bool {
  modules.iter().any(|m| {
    m.name == specifier
      || (!m.ambient_modules.is_empty() && has_ambient_module_named(specifier, &m.ambient_modules))
  })
}

fn add_decl_to_groups(
  symbols: &mut SymbolGroups,
  name: &str,
  decl: DeclId,
  namespaces: Namespace,
  table: &mut SymbolTable,
  origin: SymbolOrigin,
  owner: &SymbolOwner,
) -> SymbolId {
  let group = symbols.remove(name).unwrap_or_else(SymbolGroup::empty);
  let (group, symbol_id) =
    merge_decl_into_group(group, name, decl, namespaces, table, origin, owner);
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
  owner: &SymbolOwner,
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
    let merged_sym = build_merged_symbol(
      &group,
      name,
      decl,
      namespaces,
      symbols,
      origin.clone(),
      owner,
    );
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
    let sym = symbols.alloc_symbol(owner, name, namespaces, origin.clone());
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
      owner,
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
  owner: &SymbolOwner,
) -> SymbolId {
  let mut decls: [Vec<DeclId>; 3] = Default::default();
  collect_decls(group, symbols, &mut decls);
  for bit in namespaces.iter_bits() {
    decls[ns_index(bit)].push(new_decl);
  }

  for d in decls.iter_mut() {
    d.sort_by(|a, b| {
      symbols
        .decl(*a)
        .order
        .cmp(&symbols.decl(*b).order)
        .then_with(|| a.cmp(b))
    });
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

  let sym = symbols.alloc_symbol(owner, name, mask, origin);
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

fn merge_symbol_bucket(
  bucket: &[SymbolId],
  ns: Namespace,
  symbols: &mut SymbolTable,
) -> Option<SymbolId> {
  if bucket.is_empty() {
    return None;
  }
  if bucket.len() == 1 {
    return Some(bucket[0]);
  }

  let first = symbols.symbol(bucket[0]).clone();
  let mut decls: Vec<DeclId> = bucket
    .iter()
    .flat_map(|sym| symbols.symbol(*sym).decls_for(ns).iter().copied())
    .collect();
  decls.sort_by(|a, b| {
    symbols
      .decl(*a)
      .order
      .cmp(&symbols.decl(*b).order)
      .then_with(|| a.cmp(b))
  });
  decls.dedup();

  let merged = symbols.alloc_symbol(&first.owner, &first.name, ns, first.origin.clone());
  for decl in decls {
    symbols.add_decl_to_symbol(merged, decl, ns);
  }
  Some(merged)
}

fn merge_group_symbols(
  group: &SymbolGroup,
  base: &SymbolData,
  symbols: &mut SymbolTable,
) -> SymbolId {
  let mut decls: [Vec<DeclId>; 3] = Default::default();
  collect_decls(group, symbols, &mut decls);

  for d in decls.iter_mut() {
    d.sort_by(|a, b| {
      symbols
        .decl(*a)
        .order
        .cmp(&symbols.decl(*b).order)
        .then_with(|| a.cmp(b))
    });
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

  let merged = symbols.alloc_symbol(&base.owner, &base.name, mask, base.origin.clone());
  for bit in mask.iter_bits() {
    for decl in decls[ns_index(bit)].iter() {
      symbols.add_decl_to_symbol(merged, *decl, bit);
    }
  }
  merged
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

  let value = merge_symbol_bucket(&temp[0], Namespace::VALUE, symbols);
  let ty = merge_symbol_bucket(&temp[1], Namespace::TYPE, symbols);
  let namespace = merge_symbol_bucket(&temp[2], Namespace::NAMESPACE, symbols);

  // If all namespaces use the same symbol and it contains them, keep merged.
  let same_symbol = value == ty && ty == namespace && value.is_some();
  if same_symbol {
    return SymbolGroup::merged(value.unwrap());
  }

  let result = SymbolGroup {
    kind: SymbolGroupKind::Separate {
      value,
      ty,
      namespace,
    },
  };

  if should_merge_value_namespace(&value, &namespace, symbols) {
    let base_symbol = value
      .or(namespace)
      .and_then(|id| symbols.symbols.get(&id).cloned())
      .expect("mergeable symbol present");
    let merged = merge_group_symbols(&result, &base_symbol, symbols);
    return SymbolGroup::merged(merged);
  }

  result
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
