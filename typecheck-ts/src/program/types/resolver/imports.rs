use super::*;

impl ProgramTypeResolver {
  pub(super) fn resolve_namespace_import_path(
    &self,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    if path.len() < 2 {
      return None;
    }
    let symbol = self
      .semantics
      .resolve_in_module(
        sem_ts::FileId(self.current_file.0),
        &path[0],
        sem_ts::Namespace::NAMESPACE,
      )
      .or_else(|| {
        self
          .semantics
          .resolve_in_module(sem_ts::FileId(self.current_file.0), &path[0], final_ns)
      })
      .or_else(|| {
        self.semantics.resolve_in_module(
          sem_ts::FileId(self.current_file.0),
          &path[0],
          sem_ts::Namespace::VALUE,
        )
      })
      .or_else(|| self.global_symbol(&path[0], sem_ts::Namespace::NAMESPACE))
      .or_else(|| self.global_symbol(&path[0], final_ns))
      .or_else(|| self.global_symbol(&path[0], sem_ts::Namespace::VALUE))?;
    let imported_name = match &self.semantics.symbols().symbol(symbol).origin {
      sem_ts::SymbolOrigin::Import { imported, .. } => Some(imported.clone()),
      _ => None,
    };

    if let sem_ts::SymbolOrigin::Import {
      from: sem_ts::ModuleRef::Ambient(specifier),
      imported,
    } = &self.semantics.symbols().symbol(symbol).origin
    {
      let origin = sem_ts::ModuleRef::Ambient(specifier.clone());
      if let Some(def) =
        self.resolve_export_path_in_module_ref(origin.clone(), &path[1..], final_ns)
      {
        return Some(def);
      }
      if imported != "*" {
        let mut segments = Vec::with_capacity(path.len());
        segments.push(imported.clone());
        segments.extend_from_slice(&path[1..]);
        return self.resolve_export_path_in_module_ref(origin, &segments, final_ns);
      }
      if let Some(export_assignment) =
        export_assignment_path_for_ambient_module(&self.semantics, specifier)
      {
        let mut combined = export_assignment;
        combined.extend_from_slice(&path[1..]);
        if let Some(def) =
          self.resolve_namespace_member_path_in_ambient_module(specifier, &combined, final_ns)
        {
          return Some(def);
        }
      }
      return None;
    }

    let Some(mut module) = self
      .import_origin_file(symbol)
      .or_else(|| self.symbol_owner_file(symbol))
    else {
      // `TsProgramSemantics` tracks exports across files/modules but does not
      // provide a direct way to traverse members of global `namespace`
      // declarations (e.g. `declare namespace JSX { interface Element {} }`).
      // These are still represented in the lowered definition tree with parent
      // links, so fall back to the canonical parent->member map derived from HIR.
      return self.resolve_qualified_def_member_path(symbol, path, final_ns);
    };
    let origin = module;
    if let Some(def) = self.resolve_export_path(&path[1..], &mut module, final_ns) {
      return Some(def);
    }

    // Named imports of a namespace re-export (e.g. `import { ns } from "./mod"; type T = ns.Foo`)
    // require following the namespace export edge before resolving the remaining segments.
    let Some(imported_name) = imported_name else {
      // Local (non-import) symbol whose export walk failed. JS expando
      // property-assignment members (`var Outer = {}; Outer.X = class {…}`)
      // hang off a plain var def in `qualified_def_members`; resolve those
      // without touching namespace/class heads (they resolve through
      // `resolve_namespace_member_path` as before).
      return self.resolve_var_head_qualified_member_path(symbol, path, final_ns);
    };
    if imported_name == "*" {
      if let Some(export_assignment) =
        export_assignment_path_for_file(self.semantics.as_ref(), origin)
      {
        let mut combined = export_assignment;
        combined.extend_from_slice(&path[1..]);
        if let Some(def) = self.resolve_namespace_member_path_in_file(origin, &combined, final_ns) {
          return Some(def);
        }
      }
      return None;
    }
    let mut segments = Vec::with_capacity(path.len());
    segments.push(imported_name);
    segments.extend_from_slice(&path[1..]);
    let mut module = origin;
    self
      .resolve_export_path(&segments, &mut module, final_ns)
      .or_else(|| self.resolve_namespace_member_path_in_file(origin, &segments, final_ns))
  }

  /// Walk `qualified_def_members` from the head decl of `symbol` through each
  /// path segment (intermediate segments resolve in the NAMESPACE namespace,
  /// the final one in `final_ns`).
  pub(super) fn resolve_qualified_def_member_path(
    &self,
    symbol: sem_ts::SymbolId,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    let mut current = self
      .pick_decl(symbol, sem_ts::Namespace::NAMESPACE)
      .or_else(|| self.pick_decl(symbol, final_ns))
      .or_else(|| self.pick_decl(symbol, sem_ts::Namespace::VALUE))?;

    for (idx, segment) in path.iter().enumerate().skip(1) {
      let is_last = idx + 1 == path.len();
      let ns = if is_last {
        final_ns
      } else {
        sem_ts::Namespace::NAMESPACE
      };
      current = *self
        .qualified_def_members
        .get(&(current, segment.clone(), ns))?;
    }

    Some(current)
  }

  /// Same walk as [`Self::resolve_qualified_def_member_path`], but only when
  /// the head resolves to a plain `var` or `function` def — the shape of a JS
  /// expando container (`var Outer = {}` / `function Outer() {}` with
  /// `Outer.X = class {…}`). Namespace/class heads keep their existing
  /// resolution paths.
  pub(super) fn resolve_var_head_qualified_member_path(
    &self,
    symbol: sem_ts::SymbolId,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    let head = self.pick_decl(symbol, sem_ts::Namespace::VALUE)?;
    if !matches!(
      self.def_kinds.get(&head),
      Some(DefKind::Var(_)) | Some(DefKind::Function(_))
    ) {
      return None;
    }
    let mut current = head;
    for (idx, segment) in path.iter().enumerate().skip(1) {
      let is_last = idx + 1 == path.len();
      let ns = if is_last {
        final_ns
      } else {
        sem_ts::Namespace::NAMESPACE
      };
      current = *self
        .qualified_def_members
        .get(&(current, segment.clone(), ns))?;
    }
    Some(current)
  }
}
