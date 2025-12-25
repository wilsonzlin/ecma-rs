use super::super::{semantic_js, DefId, ExportEntry, ExportMap, FileId, ProgramState, TypeId};
use ::semantic_js::ts as sem_ts;

/// Build an [`ExportMap`] for a file using `semantic-js` binder output. Only the
/// value namespace participates so type-only exports/imports are filtered out.
pub(crate) fn exports_from_semantics(
  state: &mut ProgramState,
  semantics: &sem_ts::TsProgramSemantics,
  file: FileId,
) -> ExportMap {
  let sem_file = sem_ts::FileId(file.0);
  let exports = semantics.exports_of(sem_file);
  let symbols = semantics.symbols();
  let mut map = ExportMap::new();

  for (name, group) in exports.iter() {
    let Some(symbol_id) = group.symbol_for(sem_ts::Namespace::VALUE, symbols) else {
      continue;
    };

    let mut local_def: Option<DefId> = None;
    let mut any_def: Option<DefId> = None;
    for decl_id in semantics.symbol_decls(symbol_id, sem_ts::Namespace::VALUE) {
      let decl = symbols.decl(*decl_id);
      let def = DefId(decl.def_id.0);
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

    map.insert(
      name.clone(),
      ExportEntry {
        symbol,
        def: local_def,
        type_id,
      },
    );
  }

  map
}
