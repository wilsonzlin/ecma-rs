use super::super::{
  semantic_js, DefId, DefKind, ExportEntry, ExportMap, FileId, ProgramState, TypeId,
};
use ::semantic_js::ts as sem_ts;

/// Build [`ExportMap`] for a file using `semantic-js` binder output.
pub(crate) fn exports_from_semantics(
  state: &mut ProgramState,
  semantics: &sem_ts::TsProgramSemantics,
  file: FileId,
) -> ExportMap {
  let sem_file = sem_ts::FileId(file.0);
  let exports = semantics.exports_of(sem_file);
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
        if matches!(ns, sem_ts::Namespace::TYPE) {
          continue;
        }
        let entry = map_export(state, semantics, sem_file, symbol_id, ns);
        if let Some(def) = entry.def {
          if let Some(data) = state.def_data.get(&def) {
            if matches!(data.kind, DefKind::TypeAlias(_) | DefKind::Interface(_)) {
              continue;
            }
          }
        }
        mapped.insert(name.clone(), entry);
        break;
      }
    }
  }

  if let Some(fallback) = state.files.get(&file) {
    for (name, entry) in fallback.exports.iter() {
      if mapped.contains_key(name) {
        continue;
      }
      if let Some(def) = entry.def {
        if let Some(data) = state.def_data.get(&def) {
          if matches!(data.kind, DefKind::TypeAlias(_) | DefKind::Interface(_)) {
            continue;
          }
        }
      }
      mapped.insert(name.clone(), entry.clone());
    }
  }

  mapped
}

fn map_export(
  state: &mut ProgramState,
  semantics: &sem_ts::TsProgramSemantics,
  sem_file: sem_ts::FileId,
  symbol_id: sem_ts::SymbolId,
  ns: sem_ts::Namespace,
) -> ExportEntry {
  let symbols = semantics.symbols();
  let mut local_defs: Vec<DefId> = Vec::new();
  let mut all_defs: Vec<DefId> = Vec::new();
  for decl_id in semantics.symbol_decls(symbol_id, ns) {
    let decl = symbols.decl(*decl_id);
    if let Some(def) = map_decl_to_program_def(state, decl) {
      let canonical = state.canonical_def(def).unwrap_or(def);
      all_defs.push(canonical);
      if decl.file == sem_file {
        local_defs.push(canonical);
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
  let type_id: Option<TypeId> = preferred.map(|def| state.type_of_def(def));
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

  ExportEntry {
    symbol,
    def: local_def,
    type_id,
  }
}

fn map_decl_to_program_def(state: &ProgramState, decl: &sem_ts::DeclData) -> Option<DefId> {
  let direct = DefId(decl.def_id.0);
  if state.def_data.contains_key(&direct) {
    return Some(direct);
  }

  let mut best: Option<DefId> = None;
  for (id, data) in state.def_data.iter() {
    if data.file == FileId(decl.file.0) && data.name == decl.name {
      if best.map_or(true, |current| id < &current) {
        best = Some(*id);
      }
    }
  }
  best
}
