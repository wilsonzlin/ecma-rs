use super::super::{semantic_js, DefId, ExportEntry, ExportMap, FileId, ProgramState, TypeId};
use ::semantic_js::ts as sem_ts;

/// Build an [`ExportMap`] for a file using `semantic-js` binder output.
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
    if let Some(symbol_id) = group.symbol_for(sem_ts::Namespace::VALUE, symbols) {
      mapped.insert(
        name.clone(),
        map_export(state, semantics, sem_file, symbol_id),
      );
    }
  }

  mapped
}

fn map_export(
  state: &mut ProgramState,
  semantics: &sem_ts::TsProgramSemantics,
  sem_file: sem_ts::FileId,
  symbol_id: sem_ts::SymbolId,
) -> ExportEntry {
  let symbols = semantics.symbols();
  let mut local_def: Option<DefId> = None;
  let mut any_def: Option<DefId> = None;
  for decl_id in semantics.symbol_decls(symbol_id, sem_ts::Namespace::VALUE) {
    let decl = symbols.decl(*decl_id);
    let Some(def) = map_decl_to_program_def(state, decl) else {
      continue;
    };
    any_def.get_or_insert(def);
    if decl.file == sem_file && local_def.is_none() {
      local_def = Some(def);
    }
  }

  let def_for_type = local_def.or(any_def);
  let type_id: Option<TypeId> = def_for_type.map(|def| state.type_of_def(def));
  let symbol = local_def
    .and_then(|def| state.def_data.get(&def).map(|d| d.symbol))
    .unwrap_or_else(|| semantic_js::SymbolId::from(symbol_id));

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
