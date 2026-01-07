use super::*;

impl ProgramState {
  pub(super) fn declared_type_for_span(
    &mut self,
    file: FileId,
    target: TextRange,
  ) -> Option<TypeId> {
    fn walk_namespace(
      state: &mut ProgramState,
      file: FileId,
      body: &NamespaceBody,
      target: TextRange,
    ) -> Option<TypeId> {
      match body {
        NamespaceBody::Block(stmts) => walk(state, file, stmts, target),
        NamespaceBody::Namespace(inner) => walk_namespace(state, file, &inner.stx.body, target),
      }
    }

    fn walk(
      state: &mut ProgramState,
      file: FileId,
      stmts: &[Node<Stmt>],
      target: TextRange,
    ) -> Option<TypeId> {
      for stmt in stmts {
        match stmt.stx.as_ref() {
          Stmt::AmbientVarDecl(var) => {
            let span = loc_to_span(file, stmt.loc).range;
            if span == target {
              if let Some(ann) = var.stx.type_annotation.as_ref() {
                return Some(state.lower_interned_type_expr(file, ann));
              }
            }
          }
          Stmt::VarDecl(var) => {
            // Most definitions use the binding pattern span, but some def IDs
            // (notably for local variables) may be keyed by a wider span (e.g.
            // the declarator span). Prefer the exact pattern match first, then
            // fall back to a single unambiguous declarator whose span contains
            // the target.
            for decl in var.stx.declarators.iter() {
              let pat_span = loc_to_span(file, decl.pattern.stx.pat.loc).range;
              if pat_span == target {
                if let Some(ann) = decl.type_annotation.as_ref() {
                  return Some(state.lower_interned_type_expr(file, ann));
                }
              }
            }

            let mut matching_decl = None;
            for decl in var.stx.declarators.iter() {
              let pat_span = loc_to_span(file, decl.pattern.stx.pat.loc).range;
              let end = decl
                .initializer
                .as_ref()
                .map(|init| loc_to_span(file, init.loc).range.end)
                .or_else(|| {
                  decl
                    .type_annotation
                    .as_ref()
                    .map(|ann| loc_to_span(file, ann.loc).range.end)
                })
                .unwrap_or(pat_span.end);
              let decl_span = TextRange::new(pat_span.start, end);
              // Some defs may be keyed by a span that covers the full declarator
              // (or even the full statement). Prefer matching those wider spans,
              // but avoid matching arbitrary sub-spans inside the pattern (e.g.
              // bindings within destructuring patterns).
              let matches = decl_span == target
                || (target.start <= decl_span.start && target.end >= decl_span.end)
                || (target.start == decl_span.start && target.end <= decl_span.end)
                || (target.start <= pat_span.start && target.end >= pat_span.end);
              if matches {
                if matching_decl.is_some() {
                  matching_decl = None;
                  break;
                }
                matching_decl = Some(decl);
              }
            }

            if let Some(decl) = matching_decl {
              if let Some(ann) = decl.type_annotation.as_ref() {
                return Some(state.lower_interned_type_expr(file, ann));
              }
            }
          }
          Stmt::Block(block) => {
            if let Some(ty) = walk(state, file, &block.stx.body, target) {
              return Some(ty);
            }
          }
          Stmt::NamespaceDecl(ns) => {
            if let Some(ty) = walk_namespace(state, file, &ns.stx.body, target) {
              return Some(ty);
            }
          }
          Stmt::ModuleDecl(module) => {
            if let Some(body) = &module.stx.body {
              if let Some(ty) = walk(state, file, body, target) {
                return Some(ty);
              }
            }
          }
          Stmt::GlobalDecl(global) => {
            if let Some(ty) = walk(state, file, &global.stx.body, target) {
              return Some(ty);
            }
          }
          _ => {}
        }
      }
      None
    }

    let ast = match self.asts.get(&file) {
      Some(ast) => ast.clone(),
      None => return None,
    };
    walk(self, file, &ast.stx.body, target)
  }

  fn lower_interned_type_expr(&mut self, file: FileId, expr: &Node<TypeExpr>) -> TypeId {
    let Some(store) = self.interned_store.clone() else {
      return self.type_from_type_expr(expr);
    };

    let prev_file = self.current_file;
    self.current_file = Some(file);

    let mut binding_defs = HashMap::new();
    if let Some(state) = self.files.get(&file) {
      for (name, binding) in state.bindings.iter() {
        if let Some(def) = binding.def {
          binding_defs.insert(name.clone(), def);
        }
      }
    }
    let resolver = self.build_type_resolver(&binding_defs);
    let mut lowerer = TypeLowerer::new(Arc::clone(&store));
    lowerer.set_file(file);
    lowerer.set_resolver(resolver);
    let ty = store.canon(lowerer.lower_type_expr(expr));
    self.diagnostics.extend(lowerer.take_diagnostics());

    self.current_file = prev_file;
    ty
  }

  pub(super) fn type_alias_type_for_span(
    &mut self,
    file: FileId,
    target: TextRange,
    name: &str,
  ) -> Option<TypeId> {
    fn walk_namespace(
      state: &mut ProgramState,
      file: FileId,
      body: &NamespaceBody,
      target: TextRange,
      name: &str,
    ) -> Option<TypeId> {
      match body {
        NamespaceBody::Block(stmts) => walk(state, file, stmts, target, name),
        NamespaceBody::Namespace(inner) => {
          walk_namespace(state, file, &inner.stx.body, target, name)
        }
      }
    }

    fn walk(
      state: &mut ProgramState,
      file: FileId,
      stmts: &[Node<Stmt>],
      target: TextRange,
      name: &str,
    ) -> Option<TypeId> {
      for stmt in stmts {
        match stmt.stx.as_ref() {
          Stmt::TypeAliasDecl(alias) => {
            let span = loc_to_span(file, stmt.loc).range;
            if span == target || alias.stx.name == name {
              let ty = state.lower_interned_type_expr(file, &alias.stx.type_expr);
              return Some(ty);
            }
          }
          Stmt::Block(block) => {
            if let Some(ty) = walk(state, file, &block.stx.body, target, name) {
              return Some(ty);
            }
          }
          Stmt::NamespaceDecl(ns) => {
            if let Some(ty) = walk_namespace(state, file, &ns.stx.body, target, name) {
              return Some(ty);
            }
          }
          Stmt::GlobalDecl(global) => {
            if let Some(ty) = walk(state, file, &global.stx.body, target, name) {
              return Some(ty);
            }
          }
          _ => {}
        }
      }
      None
    }

    let ast = match self.asts.get(&file) {
      Some(ast) => ast.clone(),
      None => return None,
    };
    walk(self, file, &ast.stx.body, target, name)
  }

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

  pub(super) fn resolve_import_alias_target(&self, file: FileId, path: &[String]) -> Option<DefId> {
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

  pub(super) fn resolve_ambient_import_alias_target(
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

  pub(super) fn module_namespace_object_type(
    &mut self,
    exports: &ExportMap,
  ) -> Result<TypeId, FatalError> {
    if let Some(store) = self.interned_store.as_ref().cloned() {
      let mut shape = tti::Shape::new();
      for (name, entry) in exports.iter() {
        if name == "*" {
          continue;
        }
        let resolved_def = entry
          .def
          .or_else(|| self.symbol_to_def.get(&entry.symbol).copied());
        if let Some(def) = resolved_def {
          if let Some(data) = self.def_data.get(&def) {
            if matches!(data.kind, DefKind::Interface(_) | DefKind::TypeAlias(_)) {
              continue;
            }
          }
        }
        let mut ty = entry.type_id;
        if ty.is_none() {
          if let Some(def) = resolved_def {
            ty = self.export_type_for_def(def)?;
            if ty.is_none() {
              ty = Some(self.type_of_def(def)?);
            }
          }
        }
        let ty = ty.unwrap_or(self.builtin.unknown);
        let ty = self.ensure_interned_type(ty);
        let key = PropKey::String(store.intern_name(name.clone()));
        shape.properties.push(Property {
          key,
          data: PropData {
            ty,
            optional: false,
            readonly: true,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      Ok(store.intern_type(tti::TypeKind::Object(obj_id)))
    } else {
      let mut obj = ObjectType::empty();
      for (name, entry) in exports.iter() {
        if name == "*" {
          continue;
        }
        let resolved_def = entry
          .def
          .or_else(|| self.symbol_to_def.get(&entry.symbol).copied());
        if let Some(def) = resolved_def {
          if let Some(data) = self.def_data.get(&def) {
            if matches!(data.kind, DefKind::Interface(_) | DefKind::TypeAlias(_)) {
              continue;
            }
          }
        }
        let mut ty = entry.type_id;
        if ty.is_none() {
          if let Some(def) = resolved_def {
            ty = self.export_type_for_def(def)?;
            if ty.is_none() {
              ty = Some(self.type_of_def(def)?);
            }
          }
        }
        let ty = ty.unwrap_or(self.builtin.unknown);
        obj.props.insert(
          name.clone(),
          ObjectProperty {
            typ: ty,
            optional: false,
            readonly: true,
          },
        );
      }
      Ok(self.type_store.object(obj))
    }
  }

  pub(super) fn module_namespace_type(&mut self, file: FileId) -> Result<TypeId, FatalError> {
    self.check_cancelled()?;
    let store = match self.interned_store.as_ref() {
      Some(store) => Arc::clone(store),
      None => {
        let store = tti::TypeStore::with_options((&self.compiler_options).into());
        self.interned_store = Some(Arc::clone(&store));
        store
      }
    };

    if let Some(cached) = self.module_namespace_types.get(&file).copied() {
      return Ok(cached);
    }

    let prim = store.primitive_ids();
    if self.module_namespace_in_progress.contains(&file) {
      return Ok(prim.unknown);
    }

    self.module_namespace_in_progress.insert(file);
    let computed = panic::catch_unwind(AssertUnwindSafe(|| {
      let exports = self.exports_of_file(file)?;
      let mut names: Vec<String> = if let Some(semantics) = self.semantics.as_ref() {
        semantics
          .exports_of_opt(sem_ts::FileId(file.0))
          .map(|exports| {
            exports
              .iter()
              .filter_map(|(name, group)| {
                group
                  .symbol_for(sem_ts::Namespace::VALUE, semantics.symbols())
                  .is_some()
                  .then_some(name.clone())
              })
              .collect()
          })
          .unwrap_or_default()
      } else {
        exports
          .iter()
          .filter_map(|(name, entry)| {
            let is_value = entry
              .def
              .and_then(|def| self.def_data.get(&def))
              .map(|data| !matches!(data.kind, DefKind::Interface(_) | DefKind::TypeAlias(_)))
              .unwrap_or(true);
            is_value.then_some(name.clone())
          })
          .collect()
      };
      names.sort();
      names.dedup();

      let mut shape = tti::Shape::new();
      let mut cache = HashMap::new();
      for name in names.into_iter() {
        let entry = exports.get(&name);
        let ty = entry
          .and_then(|entry| entry.type_id)
          .or_else(|| {
            entry
              .and_then(|entry| entry.def)
              .and_then(|def| self.export_type_for_def(def).ok().flatten())
          })
          .or_else(|| {
            entry
              .and_then(|entry| entry.def)
              .and_then(|def| self.def_types.get(&def).copied())
          })
          .unwrap_or(prim.unknown);
        let ty = if store.contains_type_id(ty) {
          store.canon(ty)
        } else {
          store.canon(convert_type_for_display(ty, self, &store, &mut cache))
        };
        let key = PropKey::String(store.intern_name(name.clone()));
        shape.properties.push(Property {
          key,
          data: PropData {
            ty,
            optional: false,
            readonly: true,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      Ok(store.canon(store.intern_type(tti::TypeKind::Object(obj_id))))
    }));
    self.module_namespace_in_progress.remove(&file);
    let ty = match computed {
      Ok(Ok(ty)) => ty,
      Ok(Err(err)) => return Err(err),
      Err(payload) => panic::resume_unwind(payload),
    };
    self.module_namespace_types.insert(file, ty);
    Ok(ty)
  }
}
