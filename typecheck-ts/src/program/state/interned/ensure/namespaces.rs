use super::*;

pub(super) fn populate_namespace_object_types(
  state: &mut ProgramState,
  store: &Arc<tti::TypeStore>,
  lowered_entries: &[(FileId, Arc<LowerResult>)],
  hir_def_maps: &HashMap<FileId, HashMap<HirDefId, DefId>>,
  def_by_name: &HashMap<(FileId, Option<DefId>, String, sem_ts::Namespace), DefId>,
  def_types: &mut HashMap<DefId, tti::TypeId>,
) {
  let mut namespace_types: HashMap<(FileId, String), (tti::TypeId, TypeId)> = HashMap::new();
  let mut declared_type_cache: HashMap<(FileId, TextRange), Option<TypeId>> = HashMap::new();

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

  let mut hir_lookup_by_file: HashMap<FileId, HashMap<HirDefId, hir_js::DefData>> = HashMap::new();
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
        .or_else(|| state.def_data.contains_key(&ns_def.id).then_some(ns_def.id))
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
          state
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
          .unwrap_or((store.primitive_ids().any, state.builtin.any)),
        HirDefKind::Var | HirDefKind::Function | HirDefKind::Class | HirDefKind::Enum => {
          let member_declared_type = match state.def_data.get(member_def) {
            Some(data) => {
              let key = (data.file, data.span);
              if let Some(cached) = declared_type_cache.get(&key).copied() {
                cached
              } else {
                let declared = state.declared_type_for_span(data.file, data.span);
                declared_type_cache.insert(key, declared);
                declared
              }
            }
            None => None,
          };
          let mut store_ty = member_declared_type
            .or_else(|| state.def_types.get(member_def).copied())
            .unwrap_or(state.builtin.unknown);
          if state.is_unknown_type_id(store_ty) {
            if let Ok(fresh) = state.type_of_def(*member_def) {
              store_ty = fresh;
            }
          }
          let interned = def_types
            .get(member_def)
            .copied()
            .unwrap_or_else(|| state.ensure_interned_type(store_ty));
          let kind = store.type_kind(interned);
          let (interned, store_ty) = if matches!(member_kind, HirDefKind::Class | HirDefKind::Enum)
            && matches!(kind, tti::TypeKind::Unknown)
          {
            (store.primitive_ids().any, state.builtin.any)
          } else {
            if !state.def_types.contains_key(member_def) && store.contains_type_id(interned) {
              store_ty = state.import_interned_type(interned);
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
            ProgramState::merge_interned_decl_types(store, *existing_interned, prop_interned);
          *existing_store = state.merge_namespace_store_types(*existing_store, prop_store);
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
    let store_ty = state.type_store.object(obj);
    namespace_cache.insert(info.def, (interned, store_ty));
    namespace_types
      .entry((info.file, info.name.clone()))
      .and_modify(|(existing_interned, existing_store)| {
        *existing_interned =
          ProgramState::merge_interned_object_types(store, *existing_interned, interned);
        *existing_store = state.merge_namespace_store_types(*existing_store, store_ty);
      })
      .or_insert((interned, store_ty));
  }

  if !namespace_types.is_empty() {
    let mut ns_entries: Vec<_> = namespace_types.into_iter().collect();
    ns_entries.sort_by(|a, b| (a.0 .0, &a.0 .1).cmp(&(b.0 .0, &b.0 .1)));
    state.namespace_object_types = ns_entries.iter().cloned().collect();
    for ((file, name), (interned, store_ty)) in ns_entries.into_iter() {
      let mapped = [sem_ts::Namespace::NAMESPACE, sem_ts::Namespace::VALUE]
        .into_iter()
        .find_map(|ns| def_by_name.get(&(file, None, name.clone(), ns)).copied());
      if let Some(def) = mapped {
        def_types
          .entry(def)
          .and_modify(|existing| {
            *existing = ProgramState::merge_interned_decl_types(store, *existing, interned);
          })
          .or_insert(interned);
        state.def_types.entry(def).or_insert(store_ty);
      }
      for (def_id, data) in state.def_data.iter() {
        if data.file == file
          && data.name == name
          && matches!(data.kind, DefKind::Namespace(_) | DefKind::Module(_))
        {
          let replace_store = state
            .def_types
            .get(def_id)
            .map(|existing| {
              matches!(
                state.type_store.kind(*existing),
                TypeKind::Unknown | TypeKind::Any
              )
            })
            .unwrap_or(true);
          if replace_store {
            state.def_types.insert(*def_id, store_ty);
          }
          def_types
            .entry(*def_id)
            .and_modify(|existing| {
              *existing = ProgramState::merge_interned_decl_types(store, *existing, interned);
            })
            .or_insert(interned);
        }
      }
    }
  }
}
