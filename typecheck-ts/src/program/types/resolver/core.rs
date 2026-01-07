use super::*;

impl ProgramTypeResolver {
  pub(crate) fn new(
    host: Arc<dyn Host>,
    semantics: Arc<sem_ts::TsProgramSemantics>,
    def_kinds: Arc<HashMap<DefId, DefKind>>,
    def_files: Arc<HashMap<DefId, FileId>>,
    def_spans: Arc<HashMap<DefId, TextRange>>,
    registry: Arc<FileRegistry>,
    current_file: FileId,
    local_defs: HashMap<String, DefId>,
    exports: Arc<HashMap<FileId, ExportMap>>,
    module_namespace_defs: Arc<HashMap<FileId, DefId>>,
    namespace_members: Arc<NamespaceMemberIndex>,
    qualified_def_members: Arc<HashMap<(DefId, String, sem_ts::Namespace), DefId>>,
  ) -> Self {
    ProgramTypeResolver {
      semantics,
      def_kinds,
      def_files,
      def_spans,
      registry,
      host,
      current_file,
      local_defs,
      exports,
      module_namespace_defs,
      namespace_members,
      qualified_def_members,
    }
  }

  pub(super) fn matches_namespace(kind: &DefKind, ns: sem_ts::Namespace) -> bool {
    ProgramState::def_namespaces(kind).contains(ns)
  }

  pub(super) fn def_sort_key(&self, def: DefId, ns: sem_ts::Namespace) -> (u8, u8, u32, u32, u64) {
    let file = self
      .def_files
      .get(&def)
      .copied()
      .unwrap_or(FileId(u32::MAX));
    let origin = self.registry.lookup_origin(file);
    let origin_rank = if file == self.current_file {
      0
    } else if matches!(origin, Some(FileOrigin::Source)) {
      1
    } else {
      2
    };
    let pri = self.def_priority(def, ns);
    let span = self
      .def_spans
      .get(&def)
      .copied()
      .unwrap_or_else(|| TextRange::new(u32::MAX, u32::MAX));
    (origin_rank, pri, span.start, span.end, def.0)
  }

  pub(super) fn pick_best_def(
    &self,
    defs: impl IntoIterator<Item = DefId>,
    ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    let mut best: Option<(u8, u8, u32, u32, u64, DefId)> = None;
    for def in defs {
      let Some(kind) = self.def_kinds.get(&def) else {
        continue;
      };
      if !Self::matches_namespace(kind, ns) {
        continue;
      }
      let key = self.def_sort_key(def, ns);
      best = match best {
        Some((best_rank, best_pri, best_start, best_end, best_id, best_def))
          if (best_rank, best_pri, best_start, best_end, best_id) <= key =>
        {
          Some((best_rank, best_pri, best_start, best_end, best_id, best_def))
        }
        _ => Some((key.0, key.1, key.2, key.3, key.4, def)),
      };
    }
    best.map(|(_, _, _, _, _, def)| def)
  }

  pub(super) fn resolve_local(&self, name: &str, ns: sem_ts::Namespace) -> Option<DefId> {
    let def = self.local_defs.get(name).copied()?;
    let kind = self.def_kinds.get(&def)?;
    match kind {
      DefKind::ImportAlias(alias) => self
        .resolve_entity_name_path(&alias.path, ns)
        .or_else(|| Self::matches_namespace(kind, ns).then_some(def)),
      _ => Self::matches_namespace(kind, ns).then_some(def),
    }
  }

  pub(super) fn resolve_entity_name_path(
    &self,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    match path {
      [] => None,
      [name] => self.resolve_symbol_in_module(name, final_ns),
      _ => self
        .resolve_namespace_import_path(path, final_ns)
        .or_else(|| self.resolve_namespace_member_path(path, final_ns)),
    }
  }

  pub(super) fn collect_symbol_decls(
    &self,
    symbol: sem_ts::SymbolId,
    ns: sem_ts::Namespace,
  ) -> Vec<DefId> {
    let symbols = self.semantics.symbols();
    let mut defs: Vec<DefId> = self
      .semantics
      .symbol_decls(symbol, ns)
      .iter()
      .filter_map(|decl_id| {
        let decl = symbols.decl(*decl_id);
        let def = decl.def_id;
        self
          .def_kinds
          .get(&def)
          .and_then(|kind| Self::matches_namespace(kind, ns).then_some(def))
      })
      .collect();
    defs.sort_by_key(|id| id.0);
    defs.dedup();
    defs
  }

  pub(super) fn global_symbol(
    &self,
    name: &str,
    ns: sem_ts::Namespace,
  ) -> Option<sem_ts::SymbolId> {
    self
      .semantics
      .global_symbols()
      .get(name)
      .and_then(|group| group.symbol_for(ns, self.semantics.symbols()))
  }

  pub(super) fn symbol_owner_file(&self, symbol: sem_ts::SymbolId) -> Option<sem_ts::FileId> {
    let sym = self.semantics.symbols().symbol(symbol);
    match &sym.origin {
      sem_ts::SymbolOrigin::Import { from, .. } => match from {
        sem_ts::ModuleRef::File(file) => Some(*file),
        _ => None,
      },
      _ => match &sym.owner {
        sem_ts::SymbolOwner::Module(file) => Some(*file),
        _ => None,
      },
    }
  }

  pub(super) fn resolve_symbol_in_module(
    &self,
    name: &str,
    ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    // Local bindings (including imports) shadow global declarations.
    if let Some(local) = self.resolve_local(name, ns) {
      return Some(local);
    }
    self
      .semantics
      .resolve_in_module(sem_ts::FileId(self.current_file.0), name, ns)
      .and_then(|symbol| self.pick_decl(symbol, ns))
      .or_else(|| {
        self
          .global_symbol(name, ns)
          .and_then(|symbol| self.pick_decl(symbol, ns))
      })
  }

  pub(super) fn pick_decl(&self, symbol: sem_ts::SymbolId, ns: sem_ts::Namespace) -> Option<DefId> {
    let symbols = self.semantics.symbols();
    // Prefer a deterministic "canonical" declaration when a symbol has multiple
    // merged declarations (common in the upstream `lib.*.d.ts` set, e.g.
    // `interface Promise<T> {}` is augmented in several files).
    //
    // We intentionally do *not* use the semantic decl ordering as a tie-breaker
    // because it may depend on hash-map iteration order. Picking the lowest
    // `DefId` stabilizes resolution across callers and ensures that references
    // to merged globals (Promise, SymbolConstructor, ...) share the same
    // referenced definition identity.
    let mut best: Option<(u8, DefId)> = None;
    for decl_id in self.semantics.symbol_decls(symbol, ns).iter() {
      let decl = symbols.decl(*decl_id);
      let def = decl.def_id;
      let Some(kind) = self.def_kinds.get(&def) else {
        continue;
      };
      if !Self::matches_namespace(kind, ns) {
        continue;
      }
      let pri = self.def_priority(def, ns);
      best = match best {
        Some((best_pri, best_def)) if (best_pri, best_def.0) <= (pri, def.0) => {
          Some((best_pri, best_def))
        }
        _ => Some((pri, def)),
      };
    }
    best.map(|(_, def)| def)
  }

  pub(super) fn def_priority(&self, def: DefId, ns: sem_ts::Namespace) -> u8 {
    let Some(kind) = self.def_kinds.get(&def) else {
      return u8::MAX;
    };
    if !Self::matches_namespace(kind, ns) {
      return u8::MAX;
    }
    if ns.contains(sem_ts::Namespace::VALUE) {
      return match kind {
        DefKind::Function(_) | DefKind::Class(_) | DefKind::Enum(_) => 0,
        DefKind::Var(var) if var.body != MISSING_BODY => 1,
        DefKind::Namespace(_) | DefKind::Module(_) => 2,
        DefKind::Import(_) | DefKind::ImportAlias(_) => 3,
        DefKind::Var(_) => 4,
        DefKind::VarDeclarator(_) => 5,
        DefKind::Interface(_) | DefKind::TypeAlias(_) => 5,
      };
    }
    if ns.contains(sem_ts::Namespace::TYPE) {
      return match kind {
        DefKind::Interface(_) => 0,
        DefKind::TypeAlias(_) => 1,
        DefKind::Class(_) => 2,
        DefKind::Enum(_) => 3,
        DefKind::Import(_) | DefKind::ImportAlias(_) => 4,
        DefKind::VarDeclarator(_) => 5,
        _ => 5,
      };
    }
    if ns.contains(sem_ts::Namespace::NAMESPACE) {
      return match kind {
        DefKind::Namespace(_) | DefKind::Module(_) => 0,
        DefKind::Import(_) | DefKind::ImportAlias(_) => 1,
        DefKind::VarDeclarator(_) => 2,
        _ => 2,
      };
    }
    u8::MAX
  }

  pub(super) fn import_origin_file(&self, symbol: sem_ts::SymbolId) -> Option<sem_ts::FileId> {
    match &self.semantics.symbols().symbol(symbol).origin {
      sem_ts::SymbolOrigin::Import { from, .. } => match from {
        sem_ts::ModuleRef::File(file) => Some(*file),
        _ => None,
      },
      _ => None,
    }
  }
}
