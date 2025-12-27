use super::super::{
  semantic_js, DefId, DefKind, ExportEntry, ExportMap, FatalError, FileId, ProgramState, TypeId,
};
use ::semantic_js::ts as sem_ts;
use std::sync::Arc;
use types_ts_interned as tti;

/// Build [`ExportMap`] for a file using `semantic-js` binder output.
pub(crate) fn exports_from_semantics(
  state: &mut ProgramState,
  semantics: &sem_ts::TsProgramSemantics,
  file: FileId,
) -> Result<ExportMap, FatalError> {
  let sem_file = sem_ts::FileId(file.0);
  let fallback_exports = state
    .files
    .get(&file)
    .map(|state| state.exports.clone())
    .unwrap_or_default();
  let Some(exports) = semantics.exports_of_opt(sem_file) else {
    return Ok(fallback_exports);
  };
  if exports.is_empty() {
    return Ok(fallback_exports);
  }
  let symbols = semantics.symbols();
  let mut mapped = fallback_exports;

  for (name, group) in exports.iter() {
    let candidates = [
      sem_ts::Namespace::VALUE,
      sem_ts::Namespace::NAMESPACE,
      sem_ts::Namespace::TYPE,
    ];
    for ns in candidates {
      if let Some(symbol_id) = group.symbol_for(ns, symbols) {
        let mapped_export = map_export(state, semantics, Some(sem_file), symbol_id, ns)?;
        let merged = if let Some(existing) = mapped.get(name).cloned() {
          let mut merged = mapped_export;
          if merged.def.is_none() {
            merged.def = existing.def;
          }
          if merged.type_id.is_none() {
            merged.type_id = existing.type_id;
          }
          merged
        } else {
          mapped_export
        };
        mapped.insert(name.clone(), merged);
        break;
      }
    }
  }

  Ok(mapped)
}

/// Build [`ExportMap`] for an ambient module specifier using `semantic-js` binder output.
pub(crate) fn exports_of_ambient_module(
  state: &mut ProgramState,
  semantics: &sem_ts::TsProgramSemantics,
  specifier: &str,
) -> Result<ExportMap, FatalError> {
  let Some(exports) = semantics.exports_of_ambient_module(specifier) else {
    return Ok(ExportMap::new());
  };
  if exports.is_empty() {
    return Ok(ExportMap::new());
  }
  let symbols = semantics.symbols();
  let mut mapped = ExportMap::new();

  for (name, group) in exports.iter() {
    let candidates = [
      sem_ts::Namespace::VALUE,
      sem_ts::Namespace::NAMESPACE,
      sem_ts::Namespace::TYPE,
    ];
    for ns in candidates {
      if let Some(symbol_id) = group.symbol_for(ns, symbols) {
        let mapped_export = map_export(state, semantics, None, symbol_id, ns)?;
        let merged = if let Some(existing) = mapped.get(name).cloned() {
          let mut merged = mapped_export;
          if merged.def.is_none() {
            merged.def = existing.def;
          }
          if merged.type_id.is_none() {
            merged.type_id = existing.type_id;
          }
          merged
        } else {
          mapped_export
        };
        mapped.insert(name.clone(), merged);
        break;
      }
    }
  }

  Ok(mapped)
}

fn map_export(
  state: &mut ProgramState,
  semantics: &sem_ts::TsProgramSemantics,
  sem_file: Option<sem_ts::FileId>,
  symbol_id: sem_ts::SymbolId,
  ns: sem_ts::Namespace,
) -> Result<ExportEntry, FatalError> {
  let merged_type = |state: &mut ProgramState, defs: &[DefId]| -> Option<TypeId> {
    if defs.is_empty() {
      return None;
    }
    let store = state.interned_store.clone().unwrap_or_else(|| {
      let store = tti::TypeStore::new();
      state.interned_store = Some(store.clone());
      store
    });
    let mut overload_sigs: Vec<tti::SignatureId> = Vec::new();
    let has_overload_decl = defs.iter().any(|def| {
      matches!(
        state.def_data.get(def),
        Some(data) if matches!(&data.kind, DefKind::Function(func) if func.body.is_none())
      )
    });
    let mut components: Vec<tti::TypeId> = Vec::new();
    for def in defs.iter().copied() {
      let (is_callable, is_implementation) = match state.def_data.get(&def) {
        Some(data) => match &data.kind {
          DefKind::Function(func) => (true, func.body.is_some()),
          _ => (false, false),
        },
        None => (false, false),
      };
      let Some(ty) = state.export_type_for_def(def) else {
        continue;
      };
      let interned = state.ensure_interned_type(ty);
      match store.type_kind(interned) {
        tti::TypeKind::Callable { overloads: sigs } => {
          if is_implementation && has_overload_decl && is_callable {
            continue;
          }
          overload_sigs.extend(sigs);
        }
        _ => components.push(interned),
      }
    }
    if overload_sigs.len() > 1 {
      let relate = tti::RelateCtx::new(Arc::clone(&store), store.options());
      let existing_sigs = overload_sigs.clone();
      overload_sigs.retain(|sig_id| {
        let sig = store.signature(*sig_id);
        let is_broader = existing_sigs.iter().any(|other_id| {
          if other_id == sig_id {
            return false;
          }
          let other = store.signature(*other_id);
          if other.params.len() != sig.params.len() {
            return false;
          }
          other
            .params
            .iter()
            .zip(sig.params.iter())
            .all(|(other_param, sig_param)| relate.is_assignable(other_param.ty, sig_param.ty))
        });
        !is_broader
      });
    }
    if !overload_sigs.is_empty() {
      overload_sigs.sort();
      overload_sigs.dedup();
      components.push(store.intern_type(tti::TypeKind::Callable {
        overloads: overload_sigs,
      }));
    }
    components.sort();
    components.dedup();
    let merged = match components.as_slice() {
      [] => None,
      [single] => Some(*single),
      _ => Some(store.intersection(components)),
    };
    if let Some(merged_ty) = merged {
      if let Some(store_ref) = state.interned_store.as_ref() {
        for def in defs.iter() {
          state
            .interned_def_types
            .entry(*def)
            .and_modify(|existing| *existing = store_ref.intersection(vec![*existing, merged_ty]))
            .or_insert(merged_ty);
        }
      }
    }
    merged
  };

  let symbols = semantics.symbols();
  let mut local_defs: Vec<DefId> = Vec::new();
  let mut all_defs: Vec<DefId> = Vec::new();
  for decl_id in semantics.symbol_decls(symbol_id, ns) {
    let decl = symbols.decl(*decl_id);
    if let Some(def) = state.map_decl_to_program_def(decl, ns) {
      all_defs.push(def);
      if sem_file.map_or(false, |file| decl.file == file) {
        local_defs.push(def);
      }
    }
  }
  local_defs.sort_by_key(|d| d.0);
  local_defs.dedup();
  all_defs.sort_by_key(|d| d.0);
  all_defs.dedup();

  let filter_overload_decls = |defs: &mut Vec<DefId>, state: &ProgramState| {
    let has_overload_decl = defs.iter().any(|def| {
      matches!(
        state.def_data.get(def),
        Some(data) if matches!(&data.kind, DefKind::Function(func) if func.body.is_none())
      )
    });
    if has_overload_decl {
      defs.retain(|def| {
        matches!(
          state.def_data.get(def),
          Some(data) if matches!(&data.kind, DefKind::Function(func) if func.body.is_none())
        )
      });
    }
  };
  filter_overload_decls(&mut local_defs, state);
  filter_overload_decls(&mut all_defs, state);

  let pick_best = |defs: &[DefId]| -> Option<DefId> {
    let mut best: Option<(u8, DefId)> = None;
    for def in defs.iter().copied() {
      let priority = state.def_priority(def, ns);
      best = match best {
        Some((best_pri, best_def))
          if best_pri < priority || (best_pri == priority && best_def < def) =>
        {
          Some((best_pri, best_def))
        }
        _ => Some((priority, def)),
      };
    }
    best.map(|(_, def)| def)
  };

  let preferred = pick_best(&local_defs).or_else(|| pick_best(&all_defs));
  let type_id = merged_type(state, &local_defs).or_else(|| merged_type(state, &all_defs));
  let symbol = preferred
    .and_then(|def| state.def_data.get(&def).map(|d| d.symbol))
    .unwrap_or_else(|| semantic_js::SymbolId::from(symbol_id));
  let local_def = preferred.and_then(|def| local_defs.contains(&def).then_some(def));

  Ok(ExportEntry {
    symbol,
    def: local_def,
    type_id,
  })
}
