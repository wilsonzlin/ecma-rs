use super::super::{semantic_js, DefId, ExportEntry, ExportMap, FileId, ProgramState, TypeId};
use ::semantic_js::ts as sem_ts;

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
          map_export(state, semantics, sem_file, symbol_id, ns)?,
        );
        break;
      }
    }
  }

  Ok(mapped)
}

fn map_export(
  state: &mut ProgramState,
  semantics: &sem_ts::TsProgramSemantics,
  sem_file: sem_ts::FileId,
  symbol_id: sem_ts::SymbolId,
  ns: sem_ts::Namespace,
) -> Result<ExportEntry, crate::FatalError> {
  let symbols = semantics.symbols();
  let mut local_defs: Vec<DefId> = Vec::new();
  let mut all_defs: Vec<DefId> = Vec::new();
  for decl_id in semantics.symbol_decls(symbol_id, ns) {
    let decl = symbols.decl(*decl_id);
    if let Some(def) = state.map_decl_to_program_def(decl, ns) {
      all_defs.push(def);
      if decl.file == sem_file {
        local_defs.push(def);
      }
    }
  }
  local_defs.sort_by_key(|d| d.0);
  local_defs.dedup();
  all_defs.sort_by_key(|d| d.0);
  all_defs.dedup();

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
  let type_id: Option<TypeId> = match preferred {
    Some(def) => state.export_type_for_def(def)?,
    None => None,
  };
  let symbol = preferred
    .and_then(|def| state.def_data.get(&def).map(|d| d.symbol))
    .unwrap_or_else(|| semantic_js::SymbolId::from(symbol_id));
  let local_def = preferred.and_then(|def| {
    if local_defs.contains(&def) {
      Some(def)
    } else {
      None
    }
  });

  Ok(ExportEntry {
    symbol,
    def: local_def,
    type_id,
  })
}
