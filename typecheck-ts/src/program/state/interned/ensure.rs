use super::*;

impl ProgramState {
  pub(in super::super) fn ensure_interned_types(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileKey],
  ) -> Result<(), FatalError> {
    self.ensure_analyzed_result(host, roots)?;
    self.check_cancelled()?;
    let store = self.interned_store.clone().unwrap_or_else(|| {
      let store = tti::TypeStore::with_options((&self.compiler_options).into());
      self.interned_store = Some(Arc::clone(&store));
      self
        .typecheck_db
        .set_type_store(crate::db::types::SharedTypeStore(Arc::clone(&store)));
      store
    });
    self
      .typecheck_db
      .set_type_store(crate::db::types::SharedTypeStore(Arc::clone(&store)));
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
    }
    let mut namespace_types: HashMap<(FileId, String), (tti::TypeId, TypeId)> = HashMap::new();
    let mut declared_type_cache: HashMap<(FileId, TextRange), Option<TypeId>> = HashMap::new();
    let def_by_name = self.canonical_defs()?;
    let mut qualified_def_members: HashMap<(DefId, String, sem_ts::Namespace), DefId> =
      HashMap::new();
    for ((_, parent, name, ns), def_id) in def_by_name.iter() {
      if let Some(parent) = *parent {
        qualified_def_members.insert((parent, name.clone(), *ns), *def_id);
      }
    }
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
      if let Some(declared) = self.declared_type_for_span(file, span) {
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
        let mut members = namespace_members.remove(&info.def).unwrap_or_default();
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

    let mut namespace_cache: HashMap<DefId, (tti::TypeId, TypeId)> = HashMap::new();
    for info in namespace_infos.iter() {
      let mut props: BTreeMap<String, (tti::TypeId, TypeId)> = BTreeMap::new();
      for (name, member_def, member_kind) in info.members.iter() {
        let (prop_interned, prop_store) = match member_kind {
          HirDefKind::Namespace | HirDefKind::Module => namespace_cache
            .get(member_def)
            .copied()
            .or_else(|| namespace_types.get(&(info.file, name.clone())).copied())
            .unwrap_or((store.primitive_ids().any, self.builtin.any)),
          HirDefKind::Var | HirDefKind::Function | HirDefKind::Class | HirDefKind::Enum => {
            let member_declared_type = match self.def_data.get(member_def) {
              Some(data) => {
                let key = (data.file, data.span);
                if let Some(cached) = declared_type_cache.get(&key).copied() {
                  cached
                } else {
                  let declared = self.declared_type_for_span(data.file, data.span);
                  declared_type_cache.insert(key, declared);
                  declared
                }
              }
              None => None,
            };
            let mut store_ty = member_declared_type
              .or_else(|| self.def_types.get(member_def).copied())
              .unwrap_or(self.builtin.unknown);
            if self.is_unknown_type_id(store_ty) {
              if let Ok(fresh) = self.type_of_def(*member_def) {
                store_ty = fresh;
              }
            }
            let interned = def_types
              .get(member_def)
              .copied()
              .unwrap_or_else(|| self.ensure_interned_type(store_ty));
            let kind = store.type_kind(interned);
            let (interned, store_ty) =
              if matches!(member_kind, HirDefKind::Class | HirDefKind::Enum)
                && matches!(kind, tti::TypeKind::Unknown)
              {
                (store.primitive_ids().any, self.builtin.any)
              } else {
                if !self.def_types.contains_key(member_def) && store.contains_type_id(interned) {
                  store_ty = self.import_interned_type(interned);
                }
                (interned, store_ty)
              };
            def_types.insert(*member_def, interned);
            (interned, store_ty)
          }
          _ => continue,
        };
        props
          .entry(name.clone())
          .and_modify(|(existing_interned, existing_store)| {
            *existing_interned =
              ProgramState::merge_interned_decl_types(&store, *existing_interned, prop_interned);
            *existing_store = self.merge_namespace_store_types(*existing_store, prop_store);
          })
          .or_insert((prop_interned, prop_store));
      }

      let mut shape = tti::Shape::new();
      let mut obj = ObjectType::empty();
      for (name, (prop_interned, prop_store)) in props.into_iter() {
        let key = PropKey::String(store.intern_name(name.clone()));
        shape.properties.push(Property {
          key,
          data: PropData {
            ty: prop_interned,
            optional: false,
            readonly: true,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
        obj.props.entry(name).or_insert(ObjectProperty {
          typ: prop_store,
          optional: false,
          readonly: true,
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      let interned = store.intern_type(tti::TypeKind::Object(obj_id));
      let store_ty = self.type_store.object(obj);
      namespace_cache.insert(info.def, (interned, store_ty));
      namespace_types
        .entry((info.file, info.name.clone()))
        .and_modify(|(existing_interned, existing_store)| {
          *existing_interned =
            ProgramState::merge_interned_object_types(&store, *existing_interned, interned);
          *existing_store = self.merge_namespace_store_types(*existing_store, store_ty);
        })
        .or_insert((interned, store_ty));
    }

    if !namespace_types.is_empty() {
      let mut ns_entries: Vec<_> = namespace_types.into_iter().collect();
      ns_entries.sort_by(|a, b| (a.0 .0, &a.0 .1).cmp(&(b.0 .0, &b.0 .1)));
      self.namespace_object_types = ns_entries.iter().cloned().collect();
      for ((file, name), (interned, store_ty)) in ns_entries.into_iter() {
        let mapped = [sem_ts::Namespace::NAMESPACE, sem_ts::Namespace::VALUE]
          .into_iter()
          .find_map(|ns| def_by_name.get(&(file, None, name.clone(), ns)).copied());
        if let Some(def) = mapped {
          def_types
            .entry(def)
            .and_modify(|existing| {
              *existing = ProgramState::merge_interned_decl_types(&store, *existing, interned);
            })
            .or_insert(interned);
          self.def_types.entry(def).or_insert(store_ty);
        }
        for (def_id, data) in self.def_data.iter() {
          if data.file == file
            && data.name == name
            && matches!(data.kind, DefKind::Namespace(_) | DefKind::Module(_))
          {
            let replace_store = self
              .def_types
              .get(def_id)
              .map(|existing| {
                matches!(
                  self.type_store.kind(*existing),
                  TypeKind::Unknown | TypeKind::Any
                )
              })
              .unwrap_or(true);
            if replace_store {
              self.def_types.insert(*def_id, store_ty);
            }
            def_types
              .entry(*def_id)
              .and_modify(|existing| {
                *existing = ProgramState::merge_interned_decl_types(&store, *existing, interned);
              })
              .or_insert(interned);
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
      let mut cache = HashMap::new();
      let ty = if let Some(target_def) = entry.def {
        let ty = def_types
          .get(&target_def)
          .copied()
          .or_else(|| self.interned_def_types.get(&target_def).copied())
          .or_else(|| {
            self.def_types.get(&target_def).copied().map(|store_ty| {
              store.canon(convert_type_for_display(store_ty, self, &store, &mut cache))
            })
          });
        ty.unwrap_or(store.primitive_ids().unknown)
      } else if let Some(ty) = entry.type_id {
        if store.contains_type_id(ty) {
          ty
        } else {
          store.canon(convert_type_for_display(ty, self, &store, &mut cache))
        }
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
    let unknown = store.primitive_ids().unknown;
    let mut convert_cache = HashMap::new();
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
              readonly: true,
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
            .or_else(|| {
              entry.type_id.and_then(|ty| {
                if store.contains_type_id(ty) {
                  Some(store.canon(ty))
                } else {
                  Some(store.canon(convert_type_for_display(
                    ty,
                    self,
                    &store,
                    &mut convert_cache,
                  )))
                }
              })
            })
            .unwrap_or(unknown);
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
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      let ty = store.canon(store.intern_type(tti::TypeKind::Object(obj_id)));
      def_types.insert(namespace_def, ty);
    }

    // `lower_decl_types` canonicalizes declarations with the same name within a
    // file (e.g. multiple `interface Foo { ... }` blocks) by mapping them onto a
    // single `DefId`. In that case the non-canonical defs have no entry in
    // `decls.types`, and later declaration-merging passes would fall back to
    // converting legacy types for display (which is lossy for features like
    // `unique symbol`).
    //
    // Copy the canonical types (and their parameter lists) onto only the
    // *missing* interface defs so the merge steps stay lossless without
    // clobbering distinct augmentations in other files.
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
        let mut merged: Option<tti::TypeId> = None;
        for def in defs.iter().copied() {
          let Some(incoming) = def_types.get(&def).copied() else {
            continue;
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
        }
      }
    }

    self.interned_store = Some(store);
    self.interned_def_types = def_types;
    self.interned_type_params = type_params;
    self.interned_type_param_decls = type_param_decls;
    self.merge_callable_overload_types();
    self.merge_namespace_value_types()?;
    self.merge_interface_symbol_types_all()?;
    self.refresh_import_def_types()?;
    self.rebuild_interned_named_def_types();
    let interned_entries: Vec<_> = self.interned_def_types.clone().into_iter().collect();
    for (def, ty) in interned_entries {
      let imported = self.import_interned_type(ty);
      let mapped = if imported == self.builtin.unknown {
        ty
      } else {
        imported
      };
      self.def_types.insert(def, mapped);
    }
    self.recompute_global_bindings();
    codes::normalize_diagnostics(&mut self.diagnostics);
    self.decl_types_fingerprint = Some(fingerprint);
    Ok(())
  }
}
