use super::*;

impl ProgramState {
  pub(in super::super) fn merge_interned_object_types(
    store: &Arc<tti::TypeStore>,
    existing: tti::TypeId,
    incoming: tti::TypeId,
  ) -> tti::TypeId {
    match (store.type_kind(existing), store.type_kind(incoming)) {
      (tti::TypeKind::Object(obj_a), tti::TypeKind::Object(obj_b)) => {
        let mut shape = store.shape(store.object(obj_a).shape);
        let other = store.shape(store.object(obj_b).shape);
        let mut merged = Vec::new();
        for prop in shape
          .properties
          .into_iter()
          .chain(other.properties.into_iter())
        {
          if let Some(existing) = merged
            .iter_mut()
            .find(|p: &&mut Property| p.key == prop.key)
          {
            *existing = prop;
          } else {
            merged.push(prop);
          }
        }
        shape.properties = merged;
        shape.call_signatures.extend(other.call_signatures);
        shape
          .construct_signatures
          .extend(other.construct_signatures);
        shape.indexers.extend(other.indexers);
        let shape_id = store.intern_shape(shape);
        let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
        store.intern_type(tti::TypeKind::Object(obj_id))
      }
      _ => store.intersection(vec![existing, incoming]),
    }
  }

  fn merge_callable_with_object(
    store: &Arc<tti::TypeStore>,
    overloads: &[tti::SignatureId],
    object: tti::ObjectId,
    object_ty: tti::TypeId,
  ) -> tti::TypeId {
    let shape = store.shape(store.object(object).shape);
    let mut merged = overloads.to_vec();
    merged.extend(shape.call_signatures.iter().copied());
    let mut seen = HashSet::new();
    merged.retain(|sig| seen.insert(*sig));
    let callable = store.intern_type(tti::TypeKind::Callable { overloads: merged });
    let has_extras = !shape.properties.is_empty()
      || !shape.construct_signatures.is_empty()
      || !shape.indexers.is_empty();
    if has_extras {
      store.intersection(vec![callable, object_ty])
    } else {
      callable
    }
  }

  /// After class+interface declaration merging, interface `new (): T` sigs land
  /// on the class *instance* TYPE (tsc keeps them there so `const y = new C();
  /// new y()` works). The VALUE constructor still returns the pre-merge
  /// structural instance, which lacks those sigs.
  ///
  /// When the instance TYPE has construct signatures, rewrite VALUE construct
  /// signature returns that still point at a non-constructable object to the
  /// merged instance TYPE so `new C()` carries them.
  pub(in super::super) fn sync_class_value_ctor_returns_to_instance_type(
    store: &Arc<tti::TypeStore>,
    value_defs: &HashMap<DefId, DefId>,
    def_types: &mut HashMap<DefId, tti::TypeId>,
  ) {
    let mut entries: Vec<(DefId, DefId)> = value_defs
      .iter()
      .map(|(type_def, value_def)| (*type_def, *value_def))
      .collect();
    entries.sort_by_key(|(type_def, value_def)| (type_def.0, value_def.0));

    for (type_def, value_def) in entries {
      let Some(type_ty) = def_types.get(&type_def).copied() else {
        continue;
      };
      let type_ty = store.canon(type_ty);
      let type_ctors = ProgramState::construct_sigs_of(store, type_ty);
      if type_ctors.is_empty() {
        continue;
      }

      let Some(value_ty) = def_types.get(&value_def).copied() else {
        continue;
      };
      let value_ty = store.canon(value_ty);
      let value_ctors = ProgramState::construct_sigs_of(store, value_ty);
      if value_ctors.is_empty() {
        continue;
      }

      let mut new_sigs = Vec::with_capacity(value_ctors.len());
      let mut changed = false;
      for sig_id in value_ctors.iter().copied() {
        let mut sig = store.signature(sig_id);
        let ret = store.canon(sig.ret);
        if ret == type_ty {
          new_sigs.push(sig_id);
          continue;
        }
        // Stale structural instance: object-like, no construct sigs of its own.
        let ret_ctors = ProgramState::construct_sigs_of(store, ret);
        let ret_is_object = matches!(
          store.type_kind(ret),
          tti::TypeKind::Object(_) | tti::TypeKind::Intersection(_)
        );
        if ret_ctors.is_empty() && ret_is_object {
          sig.ret = type_ty;
          new_sigs.push(store.intern_signature(sig));
          changed = true;
        } else {
          new_sigs.push(sig_id);
        }
      }
      if changed {
        def_types.insert(
          value_def,
          ProgramState::with_construct_signatures(store, value_ty, &new_sigs),
        );
      }
    }
  }

  fn construct_sigs_of(store: &Arc<tti::TypeStore>, ty: tti::TypeId) -> Vec<tti::SignatureId> {
    match store.type_kind(ty) {
      tti::TypeKind::Object(obj_id) => store.shape(store.object(obj_id).shape).construct_signatures,
      tti::TypeKind::Intersection(members) => {
        let mut out = Vec::new();
        for member in members.iter().copied() {
          out.extend(ProgramState::construct_sigs_of(store, store.canon(member)));
        }
        out
      }
      _ => Vec::new(),
    }
  }

  fn with_construct_signatures(
    store: &Arc<tti::TypeStore>,
    ty: tti::TypeId,
    sigs: &[tti::SignatureId],
  ) -> tti::TypeId {
    match store.type_kind(ty) {
      tti::TypeKind::Object(obj_id) => {
        let mut shape = store.shape(store.object(obj_id).shape);
        shape.construct_signatures = sigs.to_vec();
        let shape_id = store.intern_shape(shape);
        let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
        store.intern_type(tti::TypeKind::Object(obj_id))
      }
      _ => {
        let mut shape = tti::Shape::new();
        shape.construct_signatures = sigs.to_vec();
        let shape_id = store.intern_shape(shape);
        let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
        store.intern_type(tti::TypeKind::Object(obj_id))
      }
    }
  }

  pub(in super::super) fn merge_interned_decl_types(
    store: &Arc<tti::TypeStore>,
    existing: tti::TypeId,
    incoming: tti::TypeId,
  ) -> tti::TypeId {
    match (store.type_kind(existing), store.type_kind(incoming)) {
      (tti::TypeKind::Callable { overloads: a }, tti::TypeKind::Callable { overloads: b }) => {
        // Prefer a complete declaration-order overload set over appending a
        // single prior signature in front (e.g. existing `[E]` + incoming
        // `[Object, E]` must stay `[Object, E]`, not become `[E, Object]`).
        let a_set: HashSet<_> = a.iter().copied().collect();
        let b_set: HashSet<_> = b.iter().copied().collect();
        if a_set.is_subset(&b_set) && b.len() >= a.len() {
          let mut unique = b;
          let mut seen_ids = HashSet::new();
          unique.retain(|sig| seen_ids.insert(*sig));
          return store.intern_type(tti::TypeKind::Callable { overloads: unique });
        }
        if b_set.is_subset(&a_set) && a.len() >= b.len() {
          let mut unique = a;
          let mut seen_ids = HashSet::new();
          unique.retain(|sig| seen_ids.insert(*sig));
          return store.intern_type(tti::TypeKind::Callable { overloads: unique });
        }
        let mut merged = Vec::with_capacity(a.len() + b.len());
        merged.extend(a);
        merged.extend(b.into_iter());
        let mut seen_ids = HashSet::new();
        merged.retain(|sig| seen_ids.insert(*sig));
        let mut unique = Vec::new();
        let mut seen: HashMap<
          (
            Vec<(tti::TypeId, bool, bool)>,
            Vec<tti::TypeParamDecl>,
            Option<tti::TypeId>,
          ),
          (tti::SignatureId, bool, bool),
        > = HashMap::new();
        for id in merged.into_iter() {
          let sig = store.signature(id);
          let key = (
            sig
              .params
              .iter()
              .map(|p| (p.ty, p.optional, p.rest))
              .collect::<Vec<_>>(),
            sig.type_params.clone(),
            sig.this_param,
          );
          let has_names = sig.params.iter().any(|p| p.name.is_some());
          let ret_kind = store.type_kind(sig.ret);
          let ret_unknown = matches!(ret_kind, tti::TypeKind::Unknown | tti::TypeKind::Any);
          if let Some((prev, prev_named, prev_unknown)) = seen.get(&key).copied() {
            let mut replace = false;
            if prev_unknown && !ret_unknown {
              replace = true;
            } else if !prev_named && has_names && prev_unknown == ret_unknown {
              replace = true;
            }
            if replace {
              if let Some(pos) = unique.iter().position(|s| *s == prev) {
                unique[pos] = id;
              }
              seen.insert(key, (id, has_names, ret_unknown));
            }
          } else {
            seen.insert(key.clone(), (id, has_names, ret_unknown));
            unique.push(id);
          }
        }
        store.intern_type(tti::TypeKind::Callable { overloads: unique })
      }
      (tti::TypeKind::Callable { overloads }, tti::TypeKind::Object(obj)) => {
        ProgramState::merge_callable_with_object(store, &overloads, obj, incoming)
      }
      (tti::TypeKind::Object(obj), tti::TypeKind::Callable { overloads }) => {
        ProgramState::merge_callable_with_object(store, &overloads, obj, existing)
      }
      (tti::TypeKind::Object(_), tti::TypeKind::Object(_)) => {
        ProgramState::merge_interned_object_types(store, existing, incoming)
      }
      _ => store.intersection(vec![existing, incoming]),
    }
  }
}
