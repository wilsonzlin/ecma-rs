use super::*;

impl ProgramState {
  pub(in super::super) fn import_interned_type(&mut self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref().cloned() else {
      return self.builtin.unknown;
    };
    use tti::TypeKind as InternedKind;
    match store.type_kind(ty) {
      InternedKind::Any => self.builtin.any,
      InternedKind::Unknown => self.builtin.unknown,
      InternedKind::Never => self.builtin.never,
      InternedKind::Void => self.builtin.void,
      InternedKind::Null => self.builtin.null,
      InternedKind::Undefined => self.builtin.undefined,
      InternedKind::Boolean => self.builtin.boolean,
      InternedKind::Number => self.builtin.number,
      InternedKind::String => self.builtin.string,
      InternedKind::BooleanLiteral(value) => self.type_store.literal_boolean(value),
      InternedKind::NumberLiteral(value) => self.type_store.literal_number(value.to_string()),
      InternedKind::StringLiteral(name) => {
        let name = store.name(name);
        self.type_store.literal_string(name)
      }
      InternedKind::Tuple(elems) => {
        let readonly = elems.iter().all(|elem| elem.readonly);
        let members: Vec<_> = elems
          .iter()
          .map(|elem| self.import_interned_type(elem.ty))
          .collect();
        self.type_store.tuple(members, readonly)
      }
      InternedKind::Array { ty, .. } => {
        let inner = self.import_interned_type(ty);
        self.type_store.array(inner)
      }
      InternedKind::Union(types) => {
        let mapped: Vec<_> = types
          .iter()
          .map(|t| self.import_interned_type(*t))
          .collect();
        self.type_store.union(mapped, &self.builtin)
      }
      InternedKind::Object(obj) => {
        let obj = store.object(obj);
        let shape = store.shape(obj.shape);
        let mut legacy = ObjectType::empty();
        for prop in shape.properties {
          let name = match prop.key {
            tti::PropKey::String(id) | tti::PropKey::Symbol(id) => Some(store.name(id)),
            tti::PropKey::Number(num) => Some(num.to_string()),
          };
          if let Some(name) = name {
            legacy.props.insert(
              name,
              ObjectProperty {
                typ: self.import_interned_type(prop.data.ty),
                optional: prop.data.optional,
                readonly: prop.data.readonly,
              },
            );
          }
        }
        for indexer in shape.indexers {
          let value = self.import_interned_type(indexer.value_type);
          match store.type_kind(indexer.key_type) {
            InternedKind::String => legacy.string_index = Some(value),
            InternedKind::Number => legacy.number_index = Some(value),
            _ => {}
          }
        }
        self.type_store.object(legacy)
      }
      InternedKind::Predicate {
        parameter,
        asserted,
        asserts,
      } => {
        let param = match parameter {
          Some(tti::PredicateParam::This) => "this".to_string(),
          _ => String::new(),
        };
        let asserted = asserted.map(|ty| self.import_interned_type(ty));
        self.type_store.predicate(param, asserted, asserts)
      }
      InternedKind::Callable { overloads } => {
        let mut fns = Vec::new();
        for sig_id in overloads {
          let sig = store.signature(sig_id);
          let params = sig
            .params
            .iter()
            .map(|param| self.import_interned_type(param.ty))
            .collect();
          let ret = self.import_interned_type(sig.ret);
          fns.push(self.type_store.function(params, ret));
        }
        if fns.is_empty() {
          self.builtin.unknown
        } else {
          self.type_store.union(fns, &self.builtin)
        }
      }
      _ => self.builtin.unknown,
    }
  }

  pub(in super::super) fn ensure_interned_type(&mut self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref() else {
      return ty;
    };
    if store.contains_type_id(ty) {
      return store.canon(ty);
    }
    if let Some(mapped) = self.def_types.iter().find_map(|(def, stored_ty)| {
      if *stored_ty == ty {
        self.interned_def_types.get(def).copied()
      } else {
        None
      }
    }) {
      return store.canon(mapped);
    }
    let mut cache = HashMap::new();
    let interned = convert_type_for_display(ty, self, store, &mut cache);
    store.canon(interned)
  }

  pub(in super::super) fn is_unknown_type_id(&self, ty: TypeId) -> bool {
    if self.type_store.contains_id(ty) {
      return matches!(self.type_store.kind(ty), TypeKind::Unknown);
    }
    if let Some(store) = self.interned_store.as_ref() {
      if store.contains_type_id(ty) {
        return matches!(store.type_kind(store.canon(ty)), tti::TypeKind::Unknown);
      }
    }
    true
  }

}
