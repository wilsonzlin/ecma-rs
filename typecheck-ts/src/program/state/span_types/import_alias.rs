use super::*;

impl ProgramState {
  fn resolve_import_alias_target_in_namespace(
    &self,
    file: FileId,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    let resolve_via_semantics = || -> Option<DefId> {
      let semantics = self.semantics.as_ref()?;
      let sem_file = sem_ts::FileId(file.0);
      if path.is_empty() {
        return None;
      }

      let global_symbol = |name: &str, ns: sem_ts::Namespace| -> Option<sem_ts::SymbolId> {
        semantics
          .global_symbols()
          .get(name)
          .and_then(|group| group.symbol_for(ns, semantics.symbols()))
      };

      let symbol = semantics
        .resolve_in_module(sem_file, &path[0], sem_ts::Namespace::NAMESPACE)
        .or_else(|| semantics.resolve_in_module(sem_file, &path[0], final_ns))
        .or_else(|| semantics.resolve_in_module(sem_file, &path[0], sem_ts::Namespace::VALUE))
        .or_else(|| global_symbol(&path[0], sem_ts::Namespace::NAMESPACE))
        .or_else(|| global_symbol(&path[0], final_ns))
        .or_else(|| global_symbol(&path[0], sem_ts::Namespace::VALUE))?;

      let pick_def = |symbol: sem_ts::SymbolId, ns: sem_ts::Namespace| -> Option<DefId> {
        let symbols = semantics.symbols();
        let mut best: Option<(u8, usize, DefId)> = None;
        for (idx, decl_id) in semantics.symbol_decls(symbol, ns).iter().enumerate() {
          let decl = symbols.decl(*decl_id);
          let Some(def) = self.map_decl_to_program_def(decl, ns) else {
            continue;
          };
          let pri = self.def_priority(def, ns);
          if pri == u8::MAX {
            continue;
          }
          let key = (pri, idx, def);
          best = match best {
            Some((best_pri, best_idx, best_def)) if (best_pri, best_idx, best_def) <= key => {
              Some((best_pri, best_idx, best_def))
            }
            _ => Some(key),
          };
        }
        best.map(|(_, _, def)| def)
      };

      if path.len() == 1 {
        return pick_def(symbol, final_ns)
          .or_else(|| pick_def(symbol, sem_ts::Namespace::NAMESPACE))
          .or_else(|| pick_def(symbol, sem_ts::Namespace::VALUE));
      }

      let sym_data = semantics.symbols().symbol(symbol);
      let imported_name = match &sym_data.origin {
        sem_ts::SymbolOrigin::Import { imported, .. } => Some(imported.clone()),
        _ => None,
      };

      let module = match &sym_data.origin {
        sem_ts::SymbolOrigin::Import { from, .. } => match from {
          sem_ts::ModuleRef::File(file) => Some(*file),
          _ => None,
        },
        _ => match &sym_data.owner {
          sem_ts::SymbolOwner::Module(file) => Some(*file),
          _ => None,
        },
      };

      let resolve_export_path = |mut module: sem_ts::FileId,
                                 segments: &[String],
                                 final_ns: sem_ts::Namespace|
       -> Option<DefId> {
        for (idx, segment) in segments.iter().enumerate() {
          let is_last = idx + 1 == segments.len();
          let ns = if is_last {
            final_ns
          } else {
            sem_ts::Namespace::NAMESPACE
          };
          let symbol = semantics.resolve_export(module, segment, ns)?;
          if is_last {
            return pick_def(symbol, final_ns)
              .or_else(|| pick_def(symbol, sem_ts::Namespace::NAMESPACE))
              .or_else(|| pick_def(symbol, sem_ts::Namespace::VALUE));
          }
          match &semantics.symbols().symbol(symbol).origin {
            sem_ts::SymbolOrigin::Import { from, .. } => match from {
              sem_ts::ModuleRef::File(file) => module = *file,
              _ => return None,
            },
            _ => return None,
          }
        }
        None
      };

      let Some(origin) = module else {
        // Fall back to parent/member links when we can't resolve to a module export (e.g. global
        // `namespace` declarations that live outside of module graphs).
        let mut current = pick_def(symbol, sem_ts::Namespace::NAMESPACE)
          .or_else(|| pick_def(symbol, final_ns))
          .or_else(|| pick_def(symbol, sem_ts::Namespace::VALUE))?;
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
        return Some(current);
      };

      if let Some(def) = resolve_export_path(origin, &path[1..], final_ns) {
        return Some(def);
      }

      // Named imports of a namespace export (e.g. `import { ns } from "./mod"; import Foo = ns.Bar`)
      // need to hop through the imported export name.
      let Some(imported_name) = imported_name else {
        return None;
      };
      if imported_name == "*" {
        return None;
      }
      let mut segments = Vec::with_capacity(path.len());
      segments.push(imported_name);
      segments.extend_from_slice(&path[1..]);
      resolve_export_path(origin, &segments, final_ns)
    };

    if let Some(def) = resolve_via_semantics() {
      return Some(def);
    }
    if path.is_empty() {
      return None;
    }
    let lowered = self.hir_lowered.get(&file)?;
    let start_ns = if path.len() == 1 {
      final_ns
    } else {
      sem_ts::Namespace::NAMESPACE
    };
    let mut current: Option<DefId> = None;
    let mut best_pri = u8::MAX;
    for def in lowered.defs.iter() {
      if def.parent.is_some() {
        continue;
      }
      let Some(name) = lowered.names.resolve(def.name) else {
        continue;
      };
      if name != path[0].as_str() {
        continue;
      }
      let pri = self.def_priority(def.id, start_ns);
      if pri == u8::MAX {
        continue;
      }
      let replace = current
        .map(|best| pri < best_pri || (pri == best_pri && def.id < best))
        .unwrap_or(true);
      if replace {
        current = Some(def.id);
        best_pri = pri;
      }
    }
    let mut current = current.or_else(|| {
      let def = self
        .files
        .get(&file)?
        .bindings
        .get(&path[0])
        .and_then(|binding| binding.def)?;
      (self.def_priority(def, start_ns) != u8::MAX).then_some(def)
    })?;
    if path.len() == 1 {
      return Some(current);
    }
    for (idx, segment) in path.iter().enumerate().skip(1) {
      let is_last = idx + 1 == path.len();
      let ns = if is_last {
        final_ns
      } else {
        sem_ts::Namespace::NAMESPACE
      };
      let current_def = lowered.def(current)?;
      let hir_js::DefTypeInfo::Namespace { members } = current_def.type_info.as_ref()? else {
        return None;
      };
      let mut candidates: Vec<DefId> = Vec::new();
      for member_def in members.iter().copied() {
        let Some(member) = lowered.def(member_def) else {
          continue;
        };
        let Some(name) = lowered.names.resolve(member.name) else {
          continue;
        };
        if name == segment.as_str() {
          candidates.push(member_def);
        }
      }
      let mut best: Option<(u8, DefId)> = None;
      for def in candidates {
        let pri = self.def_priority(def, ns);
        if pri == u8::MAX {
          continue;
        }
        best = match best {
          Some((best_pri, best_def)) if best_pri < pri || (best_pri == pri && best_def <= def) => {
            Some((best_pri, best_def))
          }
          _ => Some((pri, def)),
        };
      }
      current = best.map(|(_, def)| def)?;
    }
    Some(current)
  }

  pub(in super::super) fn resolve_import_alias_target(
    &self,
    file: FileId,
    path: &[String],
  ) -> Option<DefId> {
    self
      .resolve_import_alias_target_in_namespace(file, path, sem_ts::Namespace::VALUE)
      .or_else(|| {
        self.resolve_import_alias_target_in_namespace(file, path, sem_ts::Namespace::TYPE)
      })
      .or_else(|| {
        self.resolve_import_alias_target_in_namespace(file, path, sem_ts::Namespace::NAMESPACE)
      })
  }

  fn resolve_ambient_import_alias_target_in_namespace(
    &self,
    specifier: &str,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    let semantics = self.semantics.as_ref()?;
    if path.is_empty() {
      return None;
    }

    let module_symbols = semantics.ambient_module_symbols().get(specifier)?;
    let group = module_symbols.get(&path[0])?;
    let symbol = group
      .symbol_for(sem_ts::Namespace::NAMESPACE, semantics.symbols())
      .or_else(|| group.symbol_for(final_ns, semantics.symbols()))
      .or_else(|| group.symbol_for(sem_ts::Namespace::VALUE, semantics.symbols()))?;

    let pick_def = |symbol: sem_ts::SymbolId, ns: sem_ts::Namespace| -> Option<DefId> {
      let symbols = semantics.symbols();
      let mut best: Option<(u8, usize, DefId)> = None;
      for (idx, decl_id) in semantics.symbol_decls(symbol, ns).iter().enumerate() {
        let decl = symbols.decl(*decl_id);
        let Some(def) = self.map_decl_to_program_def(decl, ns) else {
          continue;
        };
        let pri = self.def_priority(def, ns);
        if pri == u8::MAX {
          continue;
        }
        let key = (pri, idx, def);
        best = match best {
          Some((best_pri, best_idx, best_def)) if (best_pri, best_idx, best_def) <= key => {
            Some((best_pri, best_idx, best_def))
          }
          _ => Some(key),
        };
      }
      best.map(|(_, _, def)| def)
    };

    if path.len() == 1 {
      return pick_def(symbol, final_ns)
        .or_else(|| pick_def(symbol, sem_ts::Namespace::NAMESPACE))
        .or_else(|| pick_def(symbol, sem_ts::Namespace::VALUE));
    }

    let sym_data = semantics.symbols().symbol(symbol);
    let imported_name = match &sym_data.origin {
      sem_ts::SymbolOrigin::Import { imported, .. } => Some(imported.clone()),
      _ => None,
    };
    let module_ref = match &sym_data.origin {
      sem_ts::SymbolOrigin::Import { from, .. } => Some(from.clone()),
      _ => None,
    };

    let resolve_export_path = |mut module: sem_ts::ModuleRef,
                               segments: &[String],
                               final_ns: sem_ts::Namespace|
     -> Option<DefId> {
      for (idx, segment) in segments.iter().enumerate() {
        let is_last = idx + 1 == segments.len();
        let ns = if is_last {
          final_ns
        } else {
          sem_ts::Namespace::NAMESPACE
        };
        let symbol = match &module {
          sem_ts::ModuleRef::File(file) => semantics.resolve_export(*file, segment, ns)?,
          sem_ts::ModuleRef::Ambient(spec) => semantics
            .exports_of_ambient_module(spec)?
            .get(segment)?
            .symbol_for(ns, semantics.symbols())?,
          sem_ts::ModuleRef::Unresolved(_) => return None,
        };
        if is_last {
          return pick_def(symbol, final_ns)
            .or_else(|| pick_def(symbol, sem_ts::Namespace::NAMESPACE))
            .or_else(|| pick_def(symbol, sem_ts::Namespace::VALUE));
        }
        module = match &semantics.symbols().symbol(symbol).origin {
          sem_ts::SymbolOrigin::Import { from, .. } => from.clone(),
          _ => return None,
        };
      }
      None
    };

    let Some(origin) = module_ref else {
      let mut current = pick_def(symbol, sem_ts::Namespace::NAMESPACE)
        .or_else(|| pick_def(symbol, final_ns))
        .or_else(|| pick_def(symbol, sem_ts::Namespace::VALUE))?;
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
      return Some(current);
    };

    if let Some(def) = resolve_export_path(origin.clone(), &path[1..], final_ns) {
      return Some(def);
    }

    let Some(imported_name) = imported_name else {
      return None;
    };
    if imported_name == "*" {
      return None;
    }
    let mut segments = Vec::with_capacity(path.len());
    segments.push(imported_name);
    segments.extend_from_slice(&path[1..]);
    resolve_export_path(origin, &segments, final_ns)
  }

  pub(in super::super) fn resolve_ambient_import_alias_target(
    &self,
    specifier: &str,
    path: &[String],
  ) -> Option<DefId> {
    self
      .resolve_ambient_import_alias_target_in_namespace(specifier, path, sem_ts::Namespace::VALUE)
      .or_else(|| {
        self.resolve_ambient_import_alias_target_in_namespace(
          specifier,
          path,
          sem_ts::Namespace::TYPE,
        )
      })
      .or_else(|| {
        self.resolve_ambient_import_alias_target_in_namespace(
          specifier,
          path,
          sem_ts::Namespace::NAMESPACE,
        )
      })
  }
}
