use super::super::{semantic_js, DefId, ExportEntry, Exports, FileId, ProgramState, TypeId};
use ::semantic_js::ts as sem_ts;

/// Build [`Exports`] for a file using `semantic-js` binder output, preserving
/// value/type/namespace splits in the TS symbol model.
pub(crate) fn exports_from_semantics(
  state: &mut ProgramState,
  semantics: &sem_ts::TsProgramSemantics,
  file: FileId,
) -> Exports {
  let sem_file = sem_ts::FileId(file.0);
  let exports = semantics.exports_of(sem_file);
  let symbols = semantics.symbols();
  let mut mapped = Exports::default();

  for (name, group) in exports.iter() {
    if let Some(symbol_id) = group.symbol_for(sem_ts::Namespace::VALUE, symbols) {
      mapped.values.insert(
        name.clone(),
        map_export(
          state,
          semantics,
          sem_file,
          symbol_id,
          sem_ts::Namespace::VALUE,
        ),
      );
    }
    if let Some(symbol_id) = group.symbol_for(sem_ts::Namespace::TYPE, symbols) {
      mapped.types.insert(
        name.clone(),
        map_export(
          state,
          semantics,
          sem_file,
          symbol_id,
          sem_ts::Namespace::TYPE,
        ),
      );
    }
    if let Some(symbol_id) = group.symbol_for(sem_ts::Namespace::NAMESPACE, symbols) {
      mapped.namespaces.insert(
        name.clone(),
        map_export(
          state,
          semantics,
          sem_file,
          symbol_id,
          sem_ts::Namespace::NAMESPACE,
        ),
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
  ns: sem_ts::Namespace,
) -> ExportEntry {
  let symbols = semantics.symbols();
  let mut local_def: Option<DefId> = None;
  let mut any_def: Option<DefId> = None;
  for decl_id in semantics.symbol_decls(symbol_id, ns) {
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
