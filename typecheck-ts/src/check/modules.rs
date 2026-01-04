extern crate semantic_js as semantic_js_crate;

use super::super::{semantic_js, DefId, ExportEntry, ExportMap, FileId, ProgramState, TypeId};
use semantic_js_crate::ts as sem_ts;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use types_ts_interned as tti;

/// Build [`ExportMap`] for a file using `semantic-js` binder output.
pub(crate) fn exports_from_semantics(
  state: &mut ProgramState,
  semantics: &sem_ts::TsProgramSemantics,
  file: FileId,
) -> Result<ExportMap, crate::FatalError> {
  let sem_file = sem_ts::FileId(file.0);
  let Some(exports) = semantics.exports_of_opt(sem_file) else {
    return Ok(
      state
        .files
        .get(&file)
        .map(|state| state.exports.clone())
        .unwrap_or_default(),
    );
  };
  if exports.is_empty() {
    return Ok(
      state
        .files
        .get(&file)
        .map(|state| state.exports.clone())
        .unwrap_or_default(),
    );
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
        mapped.insert(
          name.clone(),
          map_export(state, semantics, Some(sem_file), name, symbol_id, ns)?,
        );
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
) -> Result<ExportMap, crate::FatalError> {
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
        let entry = map_export(state, semantics, None, name, symbol_id, ns)?;
        mapped.insert(name.clone(), entry);
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
  name: &str,
  symbol_id: sem_ts::SymbolId,
  ns: sem_ts::Namespace,
) -> Result<ExportEntry, crate::FatalError> {
  if let Some(sem_ts::AliasTarget::ExportAssignment { path, .. }) =
    semantics.symbol_alias_target(symbol_id, ns)
  {
    match sem_file {
      Some(sem_file) => {
        let file_id = FileId(sem_file.0);
        if let Some(def) = state.resolve_import_alias_target(file_id, path) {
          let type_id = match state.export_type_for_def(def)? {
            Some(ty) => Some(ty),
            None => Some(state.type_of_def(def)?),
          };
          let symbol = state
            .def_data
            .get(&def)
            .map(|data| data.symbol)
            .unwrap_or_else(|| semantic_js::SymbolId::from(symbol_id));
          return Ok(ExportEntry {
            symbol,
            def: Some(def),
            type_id,
          });
        }
      }
      None => {
        if let sem_ts::SymbolOwner::AmbientModule(specifier) =
          &semantics.symbols().symbol(symbol_id).owner
        {
          if let Some(def) = state.resolve_ambient_import_alias_target(specifier, path) {
            let type_id = match state.export_type_for_def(def)? {
              Some(ty) => Some(ty),
              None => Some(state.type_of_def(def)?),
            };
            let symbol = state
              .def_data
              .get(&def)
              .map(|data| data.symbol)
              .unwrap_or_else(|| semantic_js::SymbolId::from(symbol_id));
            return Ok(ExportEntry {
              symbol,
              def: Some(def),
              type_id,
            });
          }
        }
      }
    }
  }

  let symbols = semantics.symbols();
  let mut local_defs: Vec<DefId> = Vec::new();
  let mut all_defs: Vec<DefId> = Vec::new();
  let mut seen_defs = HashSet::new();
  for decl_id in semantics.symbol_decls(symbol_id, ns) {
    let decl = symbols.decl(*decl_id);
    if let Some(def) = map_decl_to_program_def(state, decl, ns) {
      if seen_defs.insert(def) {
        all_defs.push(def);
        if sem_file.map_or(false, |file| decl.file == file) {
          local_defs.push(def);
        }
      }
    }
  }
  if let Some(sem_file) = sem_file {
    for (def, _data) in state
      .def_data
      .iter()
      .filter(|(_, data)| data.file == FileId(sem_file.0) && data.name == name)
    {
      if seen_defs.insert(*def) {
        all_defs.push(*def);
        local_defs.push(*def);
      }
    }
  }
  local_defs.sort_by_key(|d| d.0);
  local_defs.dedup();
  all_defs.sort_by_key(|d| d.0);
  all_defs.dedup();

  for def in all_defs.iter().copied() {
    let _ = state.type_of_def(def);
  }

  let pick_best = |defs: &[DefId], ns: sem_ts::Namespace| -> Option<DefId> {
    let mut best: Option<(u8, DefId)> = None;
    for def in defs.iter().copied() {
      let priority = state.def_priority(def, ns);
      if priority == u8::MAX {
        continue;
      }
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

  let preferred_local = pick_best(&local_defs, ns);
  let preferred = preferred_local.or_else(|| pick_best(&all_defs, ns));
  let preferred_value_local = pick_best(&local_defs, sem_ts::Namespace::VALUE);
  let preferred_value =
    preferred_value_local.or_else(|| pick_best(&all_defs, sem_ts::Namespace::VALUE));
  let preferred_def = preferred_value_local.or(preferred_local);
  let preferred_any = preferred_value.or(preferred);
  let mut type_id: Option<TypeId> = None;
  if ns.contains(sem_ts::Namespace::VALUE) && all_defs.len() > 1 {
    let store = {
      let entry = state
        .interned_store
        .get_or_insert_with(|| tti::TypeStore::with_options((&state.compiler_options).into()));
      Arc::clone(entry)
    };
    let mut cache = HashMap::new();
    let callable_defs: Vec<_> = all_defs
      .iter()
      .copied()
      .filter(|def| match state.def_data.get(def).map(|data| &data.kind) {
        Some(crate::program::DefKind::Function(_)) => true,
        _ => false,
      })
      .collect();
    if callable_defs.len() > 1 {
      if let Some(merged) = state.merged_overload_callable_type(&callable_defs, &store, &mut cache)
      {
        for def in callable_defs.iter().copied() {
          state.interned_def_types.insert(def, merged);
        }
        type_id = Some(merged);
      }
    }
  }
  if type_id.is_none() {
    type_id = match preferred_any {
      Some(def) => state.export_type_for_def(def)?,
      None => None,
    };
  }
  if type_id.is_none() && ns.contains(sem_ts::Namespace::VALUE) {
    if let sem_ts::SymbolOrigin::Import { from, imported } = &symbols.symbol(symbol_id).origin {
      if imported == "*" {
        match from {
          sem_ts::ModuleRef::File(from_file) => {
            type_id = Some(state.module_namespace_type(FileId(from_file.0))?);
          }
          sem_ts::ModuleRef::Ambient(_) | sem_ts::ModuleRef::Unresolved(_) => {}
        }
      }
    }
  }
  let symbol = preferred_any
    .and_then(|def| state.def_data.get(&def).map(|d| d.symbol))
    .unwrap_or_else(|| semantic_js::SymbolId::from(symbol_id));

  let mut entry = ExportEntry {
    symbol,
    def: preferred_def,
    type_id,
  };

  if entry.type_id.is_none() {
    if let Some(def) = preferred_any {
      entry.type_id = state.export_type_for_def(def)?;
    }
  }

  Ok(entry)
}

fn map_decl_to_program_def(
  state: &ProgramState,
  decl: &sem_ts::DeclData,
  ns: sem_ts::Namespace,
) -> Option<DefId> {
  let direct = DefId(decl.def_id.0);
  if state.def_data.contains_key(&direct) {
    return Some(direct);
  }

  let mut best: Option<(u8, DefId)> = None;
  for (id, data) in state.def_data.iter() {
    if data.file == FileId(decl.file.0) && data.name == decl.name {
      let pri = state.def_priority(*id, ns);
      best = best
        .map(|(best_pri, best_id)| {
          if pri < best_pri || (pri == best_pri && id < &best_id) {
            (pri, *id)
          } else {
            (best_pri, best_id)
          }
        })
        .or(Some((pri, *id)));
    }
  }
  best.map(|(_, id)| id)
}
