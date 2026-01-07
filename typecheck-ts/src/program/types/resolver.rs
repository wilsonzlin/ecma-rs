use super::*;

#[path = "resolver/core.rs"]
mod core;
#[path = "resolver/exports.rs"]
mod exports;
#[path = "resolver/imports.rs"]
mod imports;
#[path = "resolver/namespaces.rs"]
mod namespaces;
#[path = "resolver/type_resolver.rs"]
mod type_resolver;

#[derive(Clone)]
pub(crate) struct ProgramTypeResolver {
  semantics: Arc<sem_ts::TsProgramSemantics>,
  def_kinds: Arc<HashMap<DefId, DefKind>>,
  def_files: Arc<HashMap<DefId, FileId>>,
  def_spans: Arc<HashMap<DefId, TextRange>>,
  registry: Arc<FileRegistry>,
  host: Arc<dyn Host>,
  current_file: FileId,
  local_defs: HashMap<String, DefId>,
  exports: Arc<HashMap<FileId, ExportMap>>,
  module_namespace_defs: Arc<HashMap<FileId, DefId>>,
  namespace_members: Arc<NamespaceMemberIndex>,
  qualified_def_members: Arc<HashMap<(DefId, String, sem_ts::Namespace), DefId>>,
}

pub(in super::super) fn export_assignment_path_for_file(
  semantics: &sem_ts::TsProgramSemantics,
  file: sem_ts::FileId,
) -> Option<Vec<String>> {
  let exports = semantics.exports_of_opt(file)?;
  let group = exports.get("export=")?;
  let symbols = semantics.symbols();
  for ns in [
    sem_ts::Namespace::VALUE,
    sem_ts::Namespace::NAMESPACE,
    sem_ts::Namespace::TYPE,
  ] {
    let Some(sym) = group.symbol_for(ns, symbols) else {
      continue;
    };
    if let Some(sem_ts::AliasTarget::ExportAssignment { path, .. }) =
      semantics.symbol_alias_target(sym, ns)
    {
      return Some(path.clone());
    }
  }
  None
}

fn export_assignment_path_for_ambient_module(
  semantics: &sem_ts::TsProgramSemantics,
  specifier: &str,
) -> Option<Vec<String>> {
  let exports = semantics.exports_of_ambient_module(specifier)?;
  let group = exports.get("export=")?;
  let symbols = semantics.symbols();
  for ns in [
    sem_ts::Namespace::VALUE,
    sem_ts::Namespace::NAMESPACE,
    sem_ts::Namespace::TYPE,
  ] {
    let Some(sym) = group.symbol_for(ns, symbols) else {
      continue;
    };
    if let Some(sem_ts::AliasTarget::ExportAssignment { path, .. }) =
      semantics.symbol_alias_target(sym, ns)
    {
      return Some(path.clone());
    }
  }
  None
}
