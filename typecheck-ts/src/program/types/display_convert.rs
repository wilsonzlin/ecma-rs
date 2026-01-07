use super::*;

pub(in super::super) fn display_type_from_state(
  state: &ProgramState,
  ty: TypeId,
) -> (Arc<tti::TypeStore>, tti::TypeId) {
  if let Some(store) = state.interned_store.as_ref() {
    if store.contains_type_id(ty) {
      return (Arc::clone(store), store.canon(ty));
    }
    if let Some(mapped) = state.def_types.iter().find_map(|(def, stored_ty)| {
      if *stored_ty == ty {
        state.interned_def_types.get(def).copied()
      } else {
        None
      }
    }) {
      return (Arc::clone(store), store.canon(mapped));
    }
  }

  let store = tti::TypeStore::with_options((&state.compiler_options).into());
  let mut cache = HashMap::new();
  let interned = convert_type_for_display(ty, state, &store, &mut cache);
  (store, interned)
}

pub(in super::super) fn convert_type_for_display(
  ty: TypeId,
  state: &ProgramState,
  store: &Arc<tti::TypeStore>,
  cache: &mut HashMap<TypeId, tti::TypeId>,
) -> tti::TypeId {
  // `TypeId` is a shared public identifier (interned) but we still have a
  // legacy `TypeStore` in this module that uses small indices stored in the
  // same `TypeId` newtype. Avoid lossy `as usize` casts: prefer the interned
  // store when it recognizes the ID, otherwise treat it as a legacy index.
  if store.contains_type_id(ty) && !state.type_store.contains_id(ty) {
    return store.canon(ty);
  }
  if let Some(mapped) = cache.get(&ty) {
    return *mapped;
  }
  let primitives = store.primitive_ids();
  cache.insert(ty, primitives.unknown);
  let kind = if state.type_store.contains_id(ty) {
    state.type_store.kind(ty).clone()
  } else {
    return primitives.unknown;
  };
  let mapped = match kind {
    TypeKind::Any => primitives.any,
    TypeKind::Unknown => primitives.unknown,
    TypeKind::Never => primitives.never,
    TypeKind::Void => primitives.void,
    TypeKind::Number => primitives.number,
    TypeKind::String => primitives.string,
    TypeKind::Boolean => primitives.boolean,
    TypeKind::Null => primitives.null,
    TypeKind::Undefined => primitives.undefined,
    TypeKind::LiteralString(name) => {
      let name = store.intern_name(name);
      store.intern_type(tti::TypeKind::StringLiteral(name))
    }
    TypeKind::LiteralNumber(value) => match value.parse::<f64>() {
      Ok(num) => store.intern_type(tti::TypeKind::NumberLiteral(OrderedFloat(num))),
      Err(_) => primitives.number,
    },
    TypeKind::LiteralBoolean(value) => store.intern_type(tti::TypeKind::BooleanLiteral(value)),
    TypeKind::Tuple(elems, readonly) => {
      let members: Vec<_> = elems
        .into_iter()
        .map(|ty| tti::TupleElem {
          ty: convert_type_for_display(ty, state, store, cache),
          optional: false,
          rest: false,
          readonly,
        })
        .collect();
      store.intern_type(tti::TypeKind::Tuple(members))
    }
    TypeKind::Array(inner) => {
      let inner = convert_type_for_display(inner, state, store, cache);
      store.intern_type(tti::TypeKind::Array {
        ty: inner,
        readonly: false,
      })
    }
    TypeKind::Union(types) => {
      let members: Vec<_> = types
        .into_iter()
        .map(|t| convert_type_for_display(t, state, store, cache))
        .collect();
      store.union(members)
    }
    TypeKind::Function { params, ret } => {
      let params: Vec<_> = params
        .into_iter()
        .map(|param| tti::Param {
          name: None,
          ty: convert_type_for_display(param, state, store, cache),
          optional: false,
          rest: false,
        })
        .collect();
      let sig = tti::Signature::new(params, convert_type_for_display(ret, state, store, cache));
      let sig_id = store.intern_signature(sig);
      store.intern_type(tti::TypeKind::Callable {
        overloads: vec![sig_id],
      })
    }
    TypeKind::Predicate {
      parameter,
      asserted,
      asserts,
    } => {
      let param = if parameter.is_empty() {
        None
      } else if parameter == "this" {
        Some(tti::PredicateParam::This)
      } else {
        // `TypeKind::Function` in this compact display representation does not
        // preserve parameter names, so a type predicate's target can only be
        // approximated. Default to the first positional argument to keep the
        // output deterministic.
        Some(tti::PredicateParam::Param(0))
      };
      let asserted = asserted.map(|ty| convert_type_for_display(ty, state, store, cache));
      store.intern_type(tti::TypeKind::Predicate {
        parameter: param,
        asserted,
        asserts,
      })
    }
    TypeKind::Mapped { source, value } => {
      let param = tti::TypeParamId(0);
      let source = convert_type_for_display(source, state, store, cache);
      let value = convert_type_for_display(value, state, store, cache);
      let mapped = tti::MappedType {
        param,
        source,
        value,
        readonly: tti::MappedModifier::Preserve,
        optional: tti::MappedModifier::Preserve,
        name_type: None,
        as_type: None,
      };
      store.intern_type(tti::TypeKind::Mapped(mapped))
    }
    TypeKind::Object(obj) => {
      let mut shape = tti::Shape::new();
      for (name, prop) in obj.props {
        let key = tti::PropKey::String(store.intern_name(name));
        let data = tti::PropData {
          ty: convert_type_for_display(prop.typ, state, store, cache),
          optional: prop.optional,
          readonly: prop.readonly,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        };
        shape.properties.push(tti::Property { key, data });
      }
      if let Some(value_type) = obj.string_index {
        shape.indexers.push(tti::Indexer {
          key_type: primitives.string,
          value_type: convert_type_for_display(value_type, state, store, cache),
          readonly: false,
        });
      }
      if let Some(value_type) = obj.number_index {
        shape.indexers.push(tti::Indexer {
          key_type: primitives.number,
          value_type: convert_type_for_display(value_type, state, store, cache),
          readonly: false,
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      store.intern_type(tti::TypeKind::Object(obj_id))
    }
  };
  cache.insert(ty, mapped);
  mapped
}

pub(in super::super) fn callable_return_is_unknown(
  store: &Arc<tti::TypeStore>,
  ty: TypeId,
) -> bool {
  let prim = store.primitive_ids();
  let mut seen = HashSet::new();
  let mut pending = vec![store.canon(ty)];
  while let Some(ty) = pending.pop() {
    if !seen.insert(ty) {
      continue;
    }
    match store.type_kind(ty) {
      tti::TypeKind::Callable { overloads } => {
        if overloads
          .iter()
          .any(|sig_id| store.signature(*sig_id).ret == prim.unknown)
        {
          return true;
        }
      }
      tti::TypeKind::Union(members) | tti::TypeKind::Intersection(members) => {
        pending.extend(members.iter().copied());
      }
      _ => {}
    }
  }
  false
}
