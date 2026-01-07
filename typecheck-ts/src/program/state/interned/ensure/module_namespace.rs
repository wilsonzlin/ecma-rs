use super::*;

pub(super) fn populate_module_namespace_types(
  state: &mut ProgramState,
  store: &Arc<tti::TypeStore>,
  def_types: &mut HashMap<DefId, tti::TypeId>,
) {
  let mut module_namespace_entries: Vec<_> = state
    .module_namespace_defs
    .iter()
    .map(|(file, def)| (*file, *def))
    .collect();
  module_namespace_entries.sort_by_key(|(file, def)| (file.0, def.0));
  let unknown = store.primitive_ids().unknown;
  let mut convert_cache = HashMap::new();
  for (file, namespace_def) in module_namespace_entries.into_iter() {
    let mut shape = tti::Shape::new();
    let sem_exports = state
      .semantics
      .as_ref()
      .and_then(|semantics| semantics.exports_of_opt(sem_ts::FileId(file.0)));
    if let (Some(semantics), Some(exports)) = (state.semantics.as_deref(), sem_exports) {
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
          let Some(def) = state.map_decl_to_program_def(decl, sem_ts::Namespace::VALUE) else {
            continue;
          };
          let pri = state.def_priority(def, sem_ts::Namespace::VALUE);
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
        } else if let sem_ts::SymbolOrigin::Import { from, imported } = &symbols.symbol(symbol).origin
        {
          if imported == "*" {
            match from {
              sem_ts::ModuleRef::File(dep_file) => state
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
    } else if let Some(file_state) = state.files.get(&file) {
      for (name, entry) in file_state.exports.iter() {
        let is_value_export = state
          .semantics
          .as_ref()
          .and_then(|semantics| {
            semantics.resolve_export(sem_ts::FileId(file.0), name, sem_ts::Namespace::VALUE)
          })
          .is_some()
          || entry
            .def
            .and_then(|def| state.def_data.get(&def))
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
                Some(store.canon(convert_type_for_display(ty, state, store, &mut convert_cache)))
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
}

