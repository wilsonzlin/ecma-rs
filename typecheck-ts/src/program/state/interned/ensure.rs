use super::*;

impl ProgramState {
  pub(in super::super) fn ensure_interned_types(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileKey],
  ) -> Result<(), FatalError> {
    self.ensure_analyzed_result(host, roots)?;
    self.check_cancelled()?;
    let store = Arc::clone(&self.store);
    // Keep the salsa type store input synchronized with the program-wide store.
    self
      .typecheck_db
      .set_type_store(crate::db::types::SharedTypeStore(Arc::clone(&store)));
    let prim = store.primitive_ids();
    let fingerprint = db::decl_types_fingerprint(&self.typecheck_db);
    if self.decl_types_fingerprint == Some(fingerprint) {
      return Ok(());
    }
    self.module_namespace_types.clear();
    self.module_namespace_in_progress.clear();
    // The interned type tables are rebuilt as a batch; invalidate any shared
    // caches that may have memoized partial ref expansions against the old
    // tables.
    self.checker_caches.invalidate_shared();
    self.interned_def_types.clear();
    self.interned_named_def_types.clear();
    self.interned_type_params.clear();
    self.interned_type_param_decls.clear();
    self.interned_intrinsics.clear();
    self.namespace_object_types.clear();
    self.check_cancelled()?;
    let mut def_types = HashMap::new();
    let mut type_params = HashMap::new();
    let mut type_param_decls = HashMap::new();
    let mut decl_files: Vec<_> = db::all_files(&self.typecheck_db).iter().copied().collect();
    decl_files.sort_by_key(|file| file.0);
    for (idx, file) in decl_files.iter().enumerate() {
      if (idx % 16) == 0 {
        self.check_cancelled()?;
      }
      let decls = db::decl_types(&self.typecheck_db, *file);
      for (def, ty) in decls.types.iter() {
        def_types
          .entry(*def)
          .and_modify(|existing| {
            *existing = ProgramState::merge_interned_decl_types(&store, *existing, *ty);
          })
          .or_insert(*ty);
      }
      for (def, params) in decls.type_params.iter() {
        if params.is_empty() {
          continue;
        }
        type_params.insert(*def, params.iter().map(|param| param.id).collect());
        type_param_decls.insert(*def, Arc::from(params.clone().into_boxed_slice()));
      }
      for (def, kind) in decls.intrinsics.iter() {
        self.interned_intrinsics.insert(*def, *kind);
      }
      self.diagnostics.extend(decls.diagnostics.iter().cloned());
    }
    // Lib `.d.ts` still ships `interface Array<T>` without an `out` annotation.
    // tsc measures variance (method params are bivariant) and treats those
    // containers as covariant. Unannotated same-def refs otherwise compare
    // invariantly in `relate` (needed for generic classes), so apply the
    // measured default here for the high-value lib containers.
    for (def, params) in type_param_decls.iter_mut() {
      let Some(name) = self.def_data.get(def).map(|d| d.name.as_str()) else {
        continue;
      };
      apply_default_covariant_container_variance(name, params);
    }
    let mut namespace_types: HashMap<(FileId, String), TypeId> = HashMap::new();
    let mut declared_type_cache: HashMap<(FileId, TextRange), Option<TypeId>> = HashMap::new();
    let def_by_name = self.canonical_defs()?;
    let mut qualified_def_members: HashMap<(DefId, String, sem_ts::Namespace), DefId> =
      HashMap::new();
    for ((_, parent, name, ns), def_id) in def_by_name.iter() {
      if let Some(parent) = *parent {
        qualified_def_members.insert((parent, name.clone(), *ns), *def_id);
      }
    }
    // JS expando property-assignment members (`var Outer = {}; Outer.X =
    // class {…}`) register under the canonical outer var def; the outer var's
    // type is augmented via `namespace_types` below.
    self.register_js_expando_members(
      &store,
      &mut qualified_def_members,
      &mut def_types,
      &mut namespace_types,
    )?;
    self.qualified_def_members = Arc::new(qualified_def_members);
    let mut hir_def_maps: HashMap<FileId, HashMap<HirDefId, DefId>> = HashMap::new();
    let hir_namespaces = |kind: HirDefKind| -> sem_ts::Namespace {
      match kind {
        HirDefKind::Class => sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE,
        HirDefKind::Enum => sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE,
        HirDefKind::Interface | HirDefKind::TypeAlias => sem_ts::Namespace::TYPE,
        HirDefKind::Namespace | HirDefKind::Module => {
          sem_ts::Namespace::VALUE | sem_ts::Namespace::NAMESPACE
        }
        HirDefKind::ImportBinding => {
          sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE | sem_ts::Namespace::NAMESPACE
        }
        _ => sem_ts::Namespace::VALUE,
      }
    };
    let ns_priority = |ns: &sem_ts::Namespace| {
      if ns.contains(sem_ts::Namespace::TYPE) {
        0
      } else if ns.contains(sem_ts::Namespace::VALUE) {
        1
      } else {
        2
      }
    };
    let mut ordered_defs: Vec<_> = def_by_name.iter().collect();
    ordered_defs.sort_by(|a, b| {
      let ((file_a, parent_a, name_a, ns_a), _) = a;
      let ((file_b, parent_b, name_b, ns_b), _) = b;
      (file_a.0, *parent_a, name_a, ns_priority(ns_a), ns_a.bits()).cmp(&(
        file_b.0,
        *parent_b,
        name_b,
        ns_priority(ns_b),
        ns_b.bits(),
      ))
    });
    let mut flat_defs: HashMap<(FileId, String), DefId> = HashMap::new();
    for ((file, parent, name, _), def_id) in ordered_defs.into_iter() {
      if parent.is_some() {
        continue;
      }
      flat_defs.entry((*file, name.clone())).or_insert(*def_id);
    }

    let mut lowered_entries: Vec<_> = self
      .hir_lowered
      .iter()
      .map(|(file, lowered)| (*file, lowered.clone()))
      .collect();
    lowered_entries.sort_by_key(|(file, _)| file.0);
    for (file, lowered) in lowered_entries.iter() {
      self.check_cancelled()?;
      let mut def_map: HashMap<DefId, DefId> = HashMap::new();
      for def in lowered.defs.iter() {
        if let Some(name) = lowered.names.resolve(def.name) {
          let name = name.to_string();
          let parent = def.parent;
          let namespaces = hir_namespaces(def.path.kind);
          let preferred = match def.path.kind {
            HirDefKind::Class
            | HirDefKind::Enum
            | HirDefKind::Interface
            | HirDefKind::TypeAlias => [
              sem_ts::Namespace::TYPE,
              sem_ts::Namespace::VALUE,
              sem_ts::Namespace::NAMESPACE,
            ],
            HirDefKind::Namespace | HirDefKind::Module => [
              sem_ts::Namespace::NAMESPACE,
              sem_ts::Namespace::VALUE,
              sem_ts::Namespace::TYPE,
            ],
            _ => [
              sem_ts::Namespace::VALUE,
              sem_ts::Namespace::TYPE,
              sem_ts::Namespace::NAMESPACE,
            ],
          };
          let mapped = preferred.into_iter().find_map(|ns| {
            namespaces
              .contains(ns)
              .then_some(())
              .and_then(|_| def_by_name.get(&(*file, parent, name.clone(), ns)).copied())
          });
          if let Some(mapped) = mapped {
            def_map.insert(def.id, mapped);
          }
        }
      }
      hir_def_maps.insert(*file, def_map);
    }

    self.collect_function_decl_types(&store, &flat_defs, &mut def_types, &mut type_params);
    self.check_class_implements(
      host,
      &store,
      &def_types,
      &type_params,
      &type_param_decls,
      &lowered_entries,
      &hir_def_maps,
      &def_by_name,
    )?;
    self.check_interface_extends(
      host,
      &store,
      &def_types,
      &type_params,
      &type_param_decls,
      &lowered_entries,
      &hir_def_maps,
      &def_by_name,
    )?;

    // Populate declared types for ambient value declarations (notably `.d.ts`
    // `declare const ...: ...` bindings). These do not appear in HIR `type_info`
    // and are required for expanding `typeof` references during expression
    // checking (e.g. `window.document.title`).
    let mut declared_value_defs: Vec<(DefId, FileId, TextRange)> = self
      .def_data
      .iter()
      .filter_map(|(def, data)| match data.kind {
        DefKind::Var(_) => Some((*def, data.file, data.span)),
        _ => None,
      })
      .collect();
    declared_value_defs.sort_by_key(|(def, file, span)| (file.0, span.start, span.end, def.0));
    for (def, file, span) in declared_value_defs.into_iter() {
      if let Some(declared) = self
        .hir_declared_type_for_def(def)
        .or_else(|| self.declared_type_for_span(file, span))
      {
        def_types
          .entry(def)
          .and_modify(|existing| {
            *existing = ProgramState::merge_interned_decl_types(&store, *existing, declared);
          })
          .or_insert(declared);
      }
    }

    let value_ns_priority = |ns: &sem_ts::Namespace| {
      if ns.contains(sem_ts::Namespace::VALUE) {
        0
      } else if ns.contains(sem_ts::Namespace::NAMESPACE) {
        1
      } else {
        2
      }
    };
    let mut value_defs_by_name: HashMap<(FileId, String), DefId> = HashMap::new();
    let mut ordered_value_defs: Vec<_> = def_by_name.iter().collect();
    ordered_value_defs.sort_by(|a, b| {
      let ((file_a, parent_a, name_a, ns_a), _) = a;
      let ((file_b, parent_b, name_b, ns_b), _) = b;
      (
        file_a.0,
        *parent_a,
        name_a,
        value_ns_priority(ns_a),
        ns_a.bits(),
      )
        .cmp(&(
          file_b.0,
          *parent_b,
          name_b,
          value_ns_priority(ns_b),
          ns_b.bits(),
        ))
    });
    for ((file, parent, name, ns), def_id) in ordered_value_defs.into_iter() {
      if parent.is_some() {
        continue;
      }
      if ns.contains(sem_ts::Namespace::VALUE) || ns.contains(sem_ts::Namespace::NAMESPACE) {
        value_defs_by_name
          .entry((*file, name.clone()))
          .or_insert(*def_id);
      }
    }

    #[derive(Clone)]
    struct NamespaceInfo {
      def: DefId,
      hir_def: HirDefId,
      file: FileId,
      name: String,
      members: Vec<(String, DefId, HirDefKind)>,
    }

    let mut hir_lookup_by_file: HashMap<FileId, HashMap<HirDefId, hir_js::DefData>> =
      HashMap::new();
    for (file, lowered) in lowered_entries.iter() {
      let mut map = HashMap::new();
      for def in lowered.defs.iter() {
        map.insert(def.id, def.clone());
      }
      hir_lookup_by_file.insert(*file, map);
    }

    let mut namespace_infos: Vec<NamespaceInfo> = Vec::new();

    for (file, lowered) in lowered_entries.iter() {
      let def_map = hir_def_maps.get(file);
      for ns_def in lowered
        .defs
        .iter()
        .filter(|d| matches!(d.path.kind, HirDefKind::Namespace | HirDefKind::Module))
      {
        let Some(ns_name) = lowered.names.resolve(ns_def.name) else {
          continue;
        };
        let mapped = def_by_name
          .get(&(
            *file,
            ns_def.parent,
            ns_name.to_string(),
            sem_ts::Namespace::NAMESPACE,
          ))
          .copied()
          .or_else(|| def_map.and_then(|map| map.get(&ns_def.id).copied()))
          .or_else(|| self.def_data.contains_key(&ns_def.id).then_some(ns_def.id))
          .or_else(|| {
            value_defs_by_name
              .get(&(*file, ns_name.to_string()))
              .copied()
          });
        let Some(def_id) = mapped else {
          continue;
        };
        namespace_infos.push(NamespaceInfo {
          def: def_id,
          hir_def: ns_def.id,
          file: *file,
          name: ns_name.to_string(),
          members: Vec::new(),
        });
      }
    }

    let lowered_by_file: HashMap<FileId, &LowerResult> = lowered_entries
      .iter()
      .map(|(file, lowered)| (*file, lowered.as_ref()))
      .collect();

    let mut namespace_parents: HashMap<DefId, DefId> = HashMap::new();
    let mut namespace_members: HashMap<DefId, Vec<(String, DefId, HirDefKind)>> = HashMap::new();

    for info in namespace_infos.iter() {
      let Some(lowered) = lowered_by_file.get(&info.file) else {
        continue;
      };
      let Some(lookup) = hir_lookup_by_file.get(&info.file) else {
        continue;
      };
      let Some(ns_def) = lookup.get(&info.hir_def) else {
        continue;
      };
      let Some(hir_js::DefTypeInfo::Namespace { members }) = ns_def.type_info.as_ref() else {
        continue;
      };

      let def_map = hir_def_maps.get(&info.file);
      for member_hir in members.iter().copied() {
        let Some(member_data) = lookup.get(&member_hir) else {
          continue;
        };
        if !ns_def.is_ambient && !member_data.is_exported {
          continue;
        }
        let Some(member_name) = lowered.names.resolve(member_data.name) else {
          continue;
        };
        let member_kind = member_data.path.kind;
        if !matches!(
          member_kind,
          HirDefKind::Var
            | HirDefKind::Function
            | HirDefKind::Class
            | HirDefKind::Enum
            | HirDefKind::Namespace
            | HirDefKind::Module
        ) {
          continue;
        }
        let target_ns = match member_kind {
          HirDefKind::Namespace | HirDefKind::Module => sem_ts::Namespace::NAMESPACE,
          _ => sem_ts::Namespace::VALUE,
        };
        let member_def = def_by_name
          .get(&(
            info.file,
            Some(info.hir_def),
            member_name.to_string(),
            target_ns,
          ))
          .copied()
          .or_else(|| def_map.and_then(|map| map.get(&member_hir).copied()))
          .or_else(|| {
            self
              .def_data
              .contains_key(&member_hir)
              .then_some(member_hir)
          })
          .or_else(|| {
            target_ns
              .contains(sem_ts::Namespace::VALUE)
              .then_some(())
              .and_then(|_| {
                value_defs_by_name
                  .get(&(info.file, member_name.to_string()))
                  .copied()
              })
          });
        let Some(member_def) = member_def else {
          continue;
        };
        namespace_members.entry(info.def).or_default().push((
          member_name.to_string(),
          member_def,
          member_kind,
        ));
        if matches!(member_kind, HirDefKind::Namespace | HirDefKind::Module) {
          namespace_parents.entry(member_def).or_insert(info.def);
        }
      }
    }

    fn namespace_depth_for(
      def: DefId,
      parents: &HashMap<DefId, DefId>,
      cache: &mut HashMap<DefId, usize>,
    ) -> usize {
      if let Some(depth) = cache.get(&def) {
        return *depth;
      }
      let depth = parents
        .get(&def)
        .map(|parent| 1 + namespace_depth_for(*parent, parents, cache))
        .unwrap_or(0);
      cache.insert(def, depth);
      depth
    }

    let mut depth_cache = HashMap::new();

    let mut namespace_infos: Vec<NamespaceInfo> = namespace_infos
      .into_iter()
      .map(|mut info| {
        // Multiple namespace declarations can share one canonical def
        // (cross-file and same-file declaration merging). Every participant
        // must see the *combined* member list — consuming it for the first
        // decl leaves the others with an empty object, and which one a body
        // seeds from is file-order dependent. Clone instead.
        let mut members = namespace_members
          .get(&info.def)
          .cloned()
          .unwrap_or_default();
        members.sort_by(|a, b| {
          let ord = a.0.cmp(&b.0);
          if ord == std::cmp::Ordering::Equal {
            a.1.cmp(&b.1)
          } else {
            ord
          }
        });
        members.dedup_by(|a, b| a.0 == b.0 && a.1 == b.1 && a.2 == b.2);
        info.members = members;
        info
      })
      .collect();

    namespace_infos.sort_by(|a, b| {
      let depth_a = namespace_depth_for(a.def, &namespace_parents, &mut depth_cache);
      let depth_b = namespace_depth_for(b.def, &namespace_parents, &mut depth_cache);
      (Reverse(depth_a), a.file.0, &a.name, a.def.0).cmp(&(
        Reverse(depth_b),
        b.file.0,
        &b.name,
        b.def.0,
      ))
    });

    let mut namespace_cache: HashMap<DefId, TypeId> = HashMap::new();
    for info in namespace_infos.iter() {
      let mut props: BTreeMap<String, (TypeId, bool)> = BTreeMap::new();
      for (name, member_def, member_kind) in info.members.iter() {
        // tsc: namespace members are writable unless declared `const`
        // (`foo.v = …` is legal; `foo.c = …` is TS2540).
        let readonly =
          matches!(member_kind, HirDefKind::Var) && self.def_is_readonly_const(*member_def);
        let prop_ty = match member_kind {
          HirDefKind::Namespace | HirDefKind::Module => namespace_cache
            .get(member_def)
            .copied()
            .or_else(|| namespace_types.get(&(info.file, name.clone())).copied())
            .unwrap_or(prim.any),
          HirDefKind::Var | HirDefKind::Function | HirDefKind::Class | HirDefKind::Enum => {
            // Class/enum members contribute their *value* side (the
            // constructor value stored under the synthetic value def), not
            // the instance type stored under the class def — tsc makes
            // `namespace N { export class C {} }` give `N.C` the constructor
            // (`new N.C(0)`), same pattern as `merging/canonical.rs`.
            let member_def = if matches!(member_kind, HirDefKind::Class | HirDefKind::Enum) {
              self
                .value_defs
                .get(member_def)
                .copied()
                .unwrap_or(*member_def)
            } else {
              *member_def
            };
            let member_declared_type = match self
              .def_data
              .get(&member_def)
              .map(|data| (data.file, data.span))
            {
              Some(key) => {
                if let Some(cached) = declared_type_cache.get(&key).copied() {
                  cached
                } else {
                  let declared = self
                    .hir_declared_type_for_def(member_def)
                    .or_else(|| self.declared_type_for_span(key.0, key.1));
                  declared_type_cache.insert(key, declared);
                  declared
                }
              }
              None => None,
            };
            let mut ty = member_declared_type
              .or_else(|| def_types.get(&member_def).copied())
              .unwrap_or(prim.unknown);
            ty = store.canon(ty);
            if matches!(store.type_kind(ty), tti::TypeKind::Unknown) {
              ty = store.canon(self.type_of_def(member_def)?);
            }
            if matches!(member_kind, HirDefKind::Class | HirDefKind::Enum)
              && matches!(store.type_kind(store.canon(ty)), tti::TypeKind::Unknown)
            {
              ty = prim.any;
            }
            def_types.insert(member_def, ty);
            ty
          }
          _ => continue,
        };
        props
          .entry(name.clone())
          .and_modify(|existing| {
            existing.0 = ProgramState::merge_interned_decl_types(&store, existing.0, prop_ty);
            existing.1 = existing.1 || readonly;
          })
          .or_insert((prop_ty, readonly));
      }

      let mut shape = tti::Shape::new();
      for (name, (prop_ty, readonly)) in props.into_iter() {
        let key = PropKey::String(store.intern_name(name.clone()));
        shape.properties.push(Property {
          key,
          data: PropData {
            ty: prop_ty,
            optional: false,
            readonly,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      let ty = store.intern_type(tti::TypeKind::Object(obj_id));
      namespace_cache.insert(info.def, ty);
      namespace_types
        .entry((info.file, info.name.clone()))
        .and_modify(|existing| {
          *existing = ProgramState::merge_interned_object_types(&store, *existing, ty);
        })
        .or_insert(ty);
    }

    if !namespace_types.is_empty() {
      let mut ns_entries: Vec<_> = namespace_types.into_iter().collect();
      ns_entries.sort_by(|a, b| (a.0 .0, &a.0 .1).cmp(&(b.0 .0, &b.0 .1)));
      self.namespace_object_types = ns_entries.iter().cloned().collect();
      for ((file, name), ns_ty) in ns_entries.into_iter() {
        let mapped = [sem_ts::Namespace::NAMESPACE, sem_ts::Namespace::VALUE]
          .into_iter()
          .find_map(|ns| def_by_name.get(&(file, None, name.clone(), ns)).copied());
        if let Some(def) = mapped {
          def_types
            .entry(def)
            .and_modify(|existing| {
              *existing = ProgramState::merge_interned_decl_types(&store, *existing, ns_ty);
            })
            .or_insert(ns_ty);
        }
        for (def_id, data) in self.def_data.iter() {
          if data.file == file
            && data.name == name
            && matches!(data.kind, DefKind::Namespace(_) | DefKind::Module(_))
          {
            def_types
              .entry(*def_id)
              .and_modify(|existing| {
                *existing = ProgramState::merge_interned_decl_types(&store, *existing, ns_ty);
              })
              .or_insert(ns_ty);
          }
        }
      }
    }

    let import_defs: Vec<_> = self
      .def_data
      .iter()
      .filter_map(|(def, data)| {
        matches!(data.kind, DefKind::Import(_)).then_some((*def, data.clone()))
      })
      .collect();
    for (def_id, data) in import_defs {
      if def_types.contains_key(&def_id) {
        continue;
      }
      let DefKind::Import(import) = data.kind else {
        continue;
      };
      let exports = match self.exports_for_import(&import) {
        Ok(exports) => exports,
        Err(_) => continue,
      };
      let Some(entry) = exports.get(&import.original) else {
        continue;
      };
      let ty = if let Some(target_def) = entry.def {
        def_types.get(&target_def).copied().unwrap_or(prim.unknown)
      } else if let Some(ty) = entry.type_id {
        store.canon(ty)
      } else {
        continue;
      };
      def_types.insert(def_id, ty);
    }

    let mut module_namespace_entries: Vec<_> = self
      .module_namespace_defs
      .iter()
      .map(|(file, def)| (*file, *def))
      .collect();
    module_namespace_entries.sort_by_key(|(file, def)| (file.0, def.0));
    let unknown = prim.unknown;
    for (file, namespace_def) in module_namespace_entries.into_iter() {
      let mut shape = tti::Shape::new();
      let sem_exports = self
        .semantics
        .as_ref()
        .and_then(|semantics| semantics.exports_of_opt(sem_ts::FileId(file.0)));
      if let (Some(semantics), Some(exports)) = (self.semantics.as_deref(), sem_exports) {
        let symbols = semantics.symbols();
        for (name, group) in exports.iter() {
          if name == "default" {
            continue;
          }
          let Some(symbol) = group.symbol_for(sem_ts::Namespace::VALUE, symbols) else {
            continue;
          };

          let mut best_def: Option<(u8, DefId)> = None;
          for decl_id in semantics.symbol_decls(symbol, sem_ts::Namespace::VALUE) {
            let decl = symbols.decl(*decl_id);
            let Some(def) = self.map_decl_to_program_def(decl, sem_ts::Namespace::VALUE) else {
              continue;
            };
            let pri = self.def_priority(def, sem_ts::Namespace::VALUE);
            if pri == u8::MAX {
              continue;
            }
            best_def = match best_def {
              Some((best_pri, best)) if best_pri < pri || (best_pri == pri && best < def) => {
                Some((best_pri, best))
              }
              _ => Some((pri, def)),
            };
          }

          let ty = if let Some((_, def)) = best_def {
            def_types.get(&def).copied().unwrap_or(unknown)
          } else if let sem_ts::SymbolOrigin::Import { from, imported } =
            &symbols.symbol(symbol).origin
          {
            if imported == "*" {
              match from {
                sem_ts::ModuleRef::File(dep_file) => self
                  .module_namespace_defs
                  .get(&FileId(dep_file.0))
                  .copied()
                  .map(|dep_def| {
                    store.canon(store.intern_type(tti::TypeKind::Ref {
                      def: tti::DefId(dep_def.0),
                      args: Vec::new(),
                    }))
                  })
                  .unwrap_or(unknown),
                _ => unknown,
              }
            } else {
              unknown
            }
          } else {
            unknown
          };

          let key = PropKey::String(store.intern_name(name.clone()));
          shape.properties.push(Property {
            key,
            data: PropData {
              ty,
              optional: false,
              // tsc: namespace members are writable unless declared `const`
              // (`foo.v = …` / `foo.f = …` are legal; `foo.c = …` is TS2540).
              readonly: best_def
                .map(|(_, def)| self.def_is_readonly_const(def))
                .unwrap_or_default(),
              accessibility: None,
              is_method: false,
              origin: None,
              declared_on: None,
            },
          });
        }
      } else if let Some(file_state) = self.files.get(&file) {
        for (name, entry) in file_state.exports.iter() {
          let is_value_export = self
            .semantics
            .as_ref()
            .and_then(|semantics| {
              semantics.resolve_export(sem_ts::FileId(file.0), name, sem_ts::Namespace::VALUE)
            })
            .is_some()
            || entry
              .def
              .and_then(|def| self.def_data.get(&def))
              .map(|data| !matches!(data.kind, DefKind::Interface(_) | DefKind::TypeAlias(_)))
              .unwrap_or(false);
          if !is_value_export {
            continue;
          }
          let ty = entry
            .def
            .and_then(|def| def_types.get(&def).copied())
            .or_else(|| entry.type_id.map(|ty| store.canon(ty)))
            .unwrap_or(unknown);
          let key = PropKey::String(store.intern_name(name.clone()));
          shape.properties.push(Property {
            key,
            data: PropData {
              ty,
              optional: false,
              readonly: entry
                .def
                .map(|def| self.def_is_readonly_const(def))
                .unwrap_or_default(),
              accessibility: None,
              is_method: false,
              origin: None,
              declared_on: None,
            },
          });
        }
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      let ty = store.canon(store.intern_type(tti::TypeKind::Object(obj_id)));
      def_types.insert(namespace_def, ty);
    }

    // `canonical_defs` may map merged global interface declarations (e.g.
    // `SymbolConstructor`, `Promise`) across multiple `.d.ts` files onto a
    // single canonical `DefId`. During the initial lowering pass above we store
    // the merged type only under that canonical key.
    //
    // Later, interface-merging passes iterate the original interface definition
    // IDs from semantic symbol groups. If those defs are missing entries in
    // `interned_def_types`, we lose information about merged declarations.
    //
    // Copy the canonical types (and their parameter lists) back onto the
    // original interface defs so the merge steps stay lossless.
    for def_map in hir_def_maps.values() {
      for (hir_def, mapped) in def_map.iter() {
        if hir_def == mapped {
          continue;
        }
        if !self
          .def_data
          .get(hir_def)
          .is_some_and(|data| matches!(data.kind, DefKind::Interface(_)))
        {
          continue;
        }
        if !def_types.contains_key(hir_def) {
          if let Some(ty) = def_types.get(mapped).copied() {
            def_types.insert(*hir_def, ty);
          }
        }
        if !type_params.contains_key(hir_def) {
          if let Some(params) = type_params.get(mapped).cloned() {
            type_params.insert(*hir_def, params);
          }
        }
      }
    }

    // Module/global augmentation in `.d.ts` ecosystems relies heavily on
    // declaration merging across files. `semantic-js` already merges
    // declarations into shared symbols, but we also need to merge the computed
    // declared types so any declaration (base or augmentation) expands to the
    // same merged type.
    //
    // For the high-value 95% case, focus on interface merging (used heavily by
    // module augmentation and `declare global`). Other merge kinds (functions,
    // namespaces, value+namespace) are handled by dedicated passes.
    if let Some(semantics) = self.semantics.as_ref() {
      let symbols = semantics.symbols();
      let mut interface_groups: BTreeMap<sem_ts::SymbolId, Vec<DefId>> = BTreeMap::new();
      for (def, data) in self.def_data.iter() {
        if !matches!(data.kind, DefKind::Interface(_)) {
          continue;
        }
        let Some(symbol) = semantics.symbol_for_def(sem_ts::DefId(def.0), sem_ts::Namespace::TYPE)
        else {
          continue;
        };
        interface_groups.entry(symbol).or_default().push(*def);
      }

      // `semantic-js` exposes merged global declarations (especially the TS
      // `lib.*.d.ts` ecosystem) via `global_symbols`. The per-def `symbol_for_def`
      // mapping does not always point at the merged global symbol, so merge
      // interface declarations grouped by the global symbol as well.
      for group in semantics.global_symbols().values() {
        let Some(symbol) = group.symbol_for(sem_ts::Namespace::TYPE, symbols) else {
          continue;
        };
        let decls = semantics.symbol_decls(symbol, sem_ts::Namespace::TYPE);
        if decls.len() <= 1 {
          continue;
        }
        for decl_id in decls.iter().copied() {
          let decl = symbols.decl(decl_id);
          if !matches!(decl.kind, sem_ts::DeclKind::Interface) {
            continue;
          }
          if let Some(def) = self.map_decl_to_program_def(decl, sem_ts::Namespace::TYPE) {
            interface_groups.entry(symbol).or_default().push(def);
          }
        }
      }

      for defs in interface_groups.values_mut() {
        defs.sort_by_key(|def| {
          self
            .def_data
            .get(def)
            .map(|data| (data.file.0, data.span.start, data.span.end, def.0))
            .unwrap_or((u32::MAX, u32::MAX, u32::MAX, def.0))
        });
        defs.dedup();
      }

      for defs in interface_groups.values() {
        if defs.len() <= 1 {
          continue;
        }
        // tsc requires merged generic interfaces to declare identical type
        // parameters (TS2428), so positional unification is safe: substitute
        // later declarations' params onto the first declaration's ids,
        // otherwise the merged overload set keeps a second, free `T`
        // (`twoMergedInterfacesWithDifferingOverloads`).
        let canonical_params: Vec<TypeParamId> =
          type_params.get(&defs[0]).cloned().unwrap_or_default();
        let mut merged: Option<tti::TypeId> = None;
        for (idx, def) in defs.iter().copied().enumerate() {
          let Some(incoming) = def_types.get(&def).copied() else {
            continue;
          };
          let incoming = if idx == 0 {
            incoming
          } else {
            unify_interface_type_params(&store, incoming, type_params.get(&def), &canonical_params)
          };
          merged = Some(match merged {
            Some(existing) => ProgramState::merge_interned_decl_types(&store, existing, incoming),
            None => incoming,
          });
        }
        let Some(merged) = merged else {
          continue;
        };
        for def in defs.iter().copied() {
          def_types.insert(def, merged);
          if !canonical_params.is_empty() {
            type_params.insert(def, canonical_params.clone());
          }
        }
      }
    }

    // Namespace-nested interfaces merge across declarations too (cross-file
    // lib augmentation: `Intl.PluralRulesConstructor` is declared in both
    // `lib.es2018.intl` and `lib.es2020.intl`; tsc merges them into one
    // overload set). Nested defs carry no semantic symbols (the binder only
    // collects top-level/global decls), so group by (canonical namespace def,
    // name) and fold like the top-level pass above. Iterate `def_data` (not
    // `def_by_name`, which is one slot per key) so same-file duplicate
    // declarations are seen too.
    {
      let mut parent_of: HashMap<DefId, DefId> = HashMap::new();
      for (_file, lowered) in self.hir_lowered.iter() {
        for def in lowered.defs.iter() {
          if let Some(parent) = def.parent {
            parent_of.insert(def.id, parent);
          }
        }
      }
      let mut nested_groups: BTreeMap<(DefId, String), Vec<DefId>> = BTreeMap::new();
      for (def_id, data) in self.def_data.iter() {
        if !matches!(data.kind, DefKind::Interface(_)) {
          continue;
        }
        let Some(raw_parent) = parent_of.get(def_id).copied() else {
          continue;
        };
        let Some(parent_data) = self.def_data.get(&raw_parent) else {
          continue;
        };
        if !matches!(parent_data.kind, DefKind::Namespace(_) | DefKind::Module(_)) {
          continue;
        }
        let canonical_parent = def_by_name
          .get(&(
            data.file,
            None,
            parent_data.name.clone(),
            sem_ts::Namespace::NAMESPACE,
          ))
          .copied()
          .unwrap_or(raw_parent);
        nested_groups
          .entry((canonical_parent, data.name.clone()))
          .or_default()
          .push(*def_id);
      }
      for defs in nested_groups.values_mut() {
        defs.sort_by_key(|def| {
          self
            .def_data
            .get(def)
            .map(|data| (data.file.0, data.span.start, data.span.end, def.0))
            .unwrap_or((u32::MAX, u32::MAX, u32::MAX, def.0))
        });
        defs.dedup();
      }
      for defs in nested_groups.values() {
        if defs.len() <= 1 {
          continue;
        }
        let canonical_params: Vec<TypeParamId> =
          type_params.get(&defs[0]).cloned().unwrap_or_default();
        let mut merged: Option<tti::TypeId> = None;
        for (idx, def) in defs.iter().copied().enumerate() {
          let Some(incoming) = def_types.get(&def).copied() else {
            continue;
          };
          let incoming = if idx == 0 {
            incoming
          } else {
            unify_interface_type_params(&store, incoming, type_params.get(&def), &canonical_params)
          };
          merged = Some(match merged {
            Some(existing) => ProgramState::merge_interned_decl_types(&store, existing, incoming),
            None => incoming,
          });
        }
        let Some(merged) = merged else {
          continue;
        };
        for def in defs.iter().copied() {
          def_types.insert(def, merged);
          if !canonical_params.is_empty() {
            type_params.insert(def, canonical_params.clone());
          }
        }
      }
    }

    // Class+interface merge parks interface `new (): T` on the instance TYPE
    // (tsc). Sync VALUE constructor returns onto that merged instance so
    // `const y = new C(); new y()` sees the construct signatures.
    ProgramState::sync_class_value_ctor_returns_to_instance_type(
      &store,
      &self.value_defs,
      &mut def_types,
    );

    self.interned_def_types = def_types;
    self.interned_type_params = type_params;
    self.interned_type_param_decls = type_param_decls;
    self.merge_callable_overload_types();
    self.merge_namespace_value_types()?;
    self.merge_interface_symbol_types_all()?;
    self.refresh_import_def_types()?;
    self.rebuild_interned_named_def_types();
    self.recompute_global_bindings();
    // After class shapes exist, replace unknown accessor properties with
    // inferred getter return / setter param types (avoids TC3000 on `this.g`).
    self.refine_class_accessor_property_types()?;
    // Infer unannotated method returns (`getInstance() { return new C() }` → `C`)
    // so private access on the result can emit TS18013.
    self.refine_class_method_property_types()?;
    // Infer unannotated static fields from static-block / initializer
    // assignments (`static x;` + `static { this.x = 1 }` → `number`). Runs
    // before the instance-field refine: that pass calls `type_of_def` on every
    // field, which would otherwise cache the still-unknown field type (and
    // emit TS7008) before this synthesis registers the assignment-based one.
    self.refine_class_static_field_types_from_assignments()?;
    // Infer unannotated field initializers (`three = 3` → `number`, numeric
    // keys included) so reads through the declared instance type are precise.
    self.refine_class_field_property_types()?;
    codes::normalize_diagnostics(&mut self.diagnostics);
    self.decl_types_fingerprint = Some(fingerprint);
    Ok(())
  }
}

/// Mark the primary type parameter of known covariant lib containers as `out`
/// when the source declaration left variance unannotated.
fn apply_default_covariant_container_variance(name: &str, params: &mut Arc<[tti::TypeParamDecl]>) {
  const COVARIANT_CONTAINERS: &[&str] = &[
    "Array",
    "ReadonlyArray",
    "ArrayLike",
    "Promise",
    "PromiseLike",
    "Iterable",
    "Iterator",
    "AsyncIterable",
    "AsyncIterator",
  ];
  if !COVARIANT_CONTAINERS.contains(&name) {
    return;
  }
  let Some(first) = params.first() else {
    return;
  };
  if first.variance.is_some() {
    return;
  }
  let mut owned = params.to_vec();
  owned[0].variance = Some(tti::TypeParamVariance::Out);
  *params = Arc::from(owned.into_boxed_slice());
}

/// Positional type-param unification for merged generic interfaces (tsc
/// TS2428 requires identical type-parameter lists across declarations).
fn unify_interface_type_params(
  store: &Arc<tti::TypeStore>,
  ty: tti::TypeId,
  from: Option<&Vec<TypeParamId>>,
  to: &[TypeParamId],
) -> tti::TypeId {
  let Some(from) = from else {
    return ty;
  };
  if from.as_slice() == to {
    return ty;
  }
  let subst: HashMap<TypeParamId, tti::TypeId> = from
    .iter()
    .zip(to.iter())
    .map(|(f, t)| (*f, store.intern_type(tti::TypeKind::TypeParam(*t))))
    .collect();
  let mut substituter = crate::check::instantiate::Substituter::new(Arc::clone(store), subst);
  substituter.substitute_type(ty)
}

impl ProgramState {
  /// Whether a namespace member def is a `const` binding (tsc: only those are
  /// read-only through the namespace object; `var`/`let`/functions are
  /// writable — `foo.v = …` is legal).
  pub(crate) fn def_is_readonly_const(&self, def: DefId) -> bool {
    matches!(
      self.def_data.get(&def).map(|data| &data.kind),
      Some(DefKind::Var(var)) if matches!(var.mode, VarDeclMode::Const)
    )
  }
}
