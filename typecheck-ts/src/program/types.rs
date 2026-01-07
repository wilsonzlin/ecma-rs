extern crate semantic_js as semantic_js_crate;

use crate::api::{DefId, FileId, TextRange};
use crate::check::type_expr::TypeResolver;
use crate::files::{FileOrigin, FileRegistry};
use hir_js::ids::MISSING_BODY;
use ordered_float::OrderedFloat;
use semantic_js_crate::ts as sem_ts;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use types_ts_interned as tti;
use types_ts_interned::{PropKey, TypeId, TypeParamId};

use super::{DefKind, ExportMap, Host, ProgramState, TypeKind};

/// Helper returned from [`Program::display_type`].
///
/// When the optional `serde` feature is enabled this serializes to the rendered
/// string form for easy inclusion in JSON outputs.
#[derive(Clone)]
pub struct TypeDisplay {
  pub(super) store: Arc<tti::TypeStore>,
  pub(super) ty: tti::TypeId,
  pub(super) resolver: Option<Arc<dyn Fn(tti::DefId) -> Option<String> + Send + Sync>>,
}

/// Structured explanation for why one type is not assignable to another.
///
/// This is powered by the `types-ts-interned` relation engine and is intended
/// for diagnostics, debugging, and tooling (e.g. CLI output).
pub type ExplainTree = tti::ReasonNode;

impl std::fmt::Display for TypeDisplay {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let display = if let Some(resolver) = self.resolver.as_ref() {
      tti::TypeDisplay::new(&self.store, self.ty).with_ref_resolver(Arc::clone(resolver))
    } else {
      tti::TypeDisplay::new(&self.store, self.ty)
    };
    display.fmt(f)
  }
}

#[cfg(feature = "serde")]
impl serde::Serialize for TypeDisplay {
  fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(&self.to_string())
  }
}

#[derive(Clone, Copy)]
pub(super) struct ProgramTypeExpander<'a> {
  pub(super) def_types: &'a HashMap<DefId, TypeId>,
  pub(super) type_params: &'a HashMap<DefId, Vec<TypeParamId>>,
  pub(super) intrinsics: &'a HashMap<DefId, tti::IntrinsicKind>,
}

impl<'a> tti::TypeExpander for ProgramTypeExpander<'a> {
  fn expand(
    &self,
    store: &tti::TypeStore,
    def: DefId,
    args: &[TypeId],
  ) -> Option<tti::ExpandedType> {
    if let Some(kind) = self.intrinsics.get(&def).copied() {
      let operand = args
        .first()
        .copied()
        .unwrap_or_else(|| store.primitive_ids().unknown);
      let ty = store.intern_type(tti::TypeKind::Intrinsic { kind, ty: operand });
      return Some(tti::ExpandedType {
        params: Vec::new(),
        ty,
      });
    }
    let ty = *self.def_types.get(&def)?;
    let params = self.type_params.get(&def).cloned().unwrap_or_else(Vec::new);
    Some(tti::ExpandedType { params, ty })
  }
}

pub(super) fn display_type_from_state(
  state: &ProgramState,
  ty: TypeId,
) -> (Arc<tti::TypeStore>, tti::TypeId) {
  if let Some(store) = state.interned_store.as_ref() {
    if store.contains_type_id(ty) {
      return (Arc::clone(store), store.canon(ty));
    }
    if let Some(mapped) = state.def_types.iter().find_map(|(def, stored_ty)| {
      if *stored_ty == ty {
        state.interned_def_types.get(def).copied()
      } else {
        None
      }
    }) {
      return (Arc::clone(store), store.canon(mapped));
    }
  }

  let store = tti::TypeStore::with_options((&state.compiler_options).into());
  let mut cache = HashMap::new();
  let interned = convert_type_for_display(ty, state, &store, &mut cache);
  (store, interned)
}

pub(super) fn convert_type_for_display(
  ty: TypeId,
  state: &ProgramState,
  store: &Arc<tti::TypeStore>,
  cache: &mut HashMap<TypeId, tti::TypeId>,
) -> tti::TypeId {
  // `TypeId` is a shared public identifier (interned) but we still have a
  // legacy `TypeStore` in this module that uses small indices stored in the
  // same `TypeId` newtype. Avoid lossy `as usize` casts: prefer the interned
  // store when it recognizes the ID, otherwise treat it as a legacy index.
  if store.contains_type_id(ty) && !state.type_store.contains_id(ty) {
    return store.canon(ty);
  }
  if let Some(mapped) = cache.get(&ty) {
    return *mapped;
  }
  let primitives = store.primitive_ids();
  cache.insert(ty, primitives.unknown);
  let kind = if state.type_store.contains_id(ty) {
    state.type_store.kind(ty).clone()
  } else {
    return primitives.unknown;
  };
  let mapped = match kind {
    TypeKind::Any => primitives.any,
    TypeKind::Unknown => primitives.unknown,
    TypeKind::Never => primitives.never,
    TypeKind::Void => primitives.void,
    TypeKind::Number => primitives.number,
    TypeKind::String => primitives.string,
    TypeKind::Boolean => primitives.boolean,
    TypeKind::Null => primitives.null,
    TypeKind::Undefined => primitives.undefined,
    TypeKind::LiteralString(name) => {
      let name = store.intern_name(name);
      store.intern_type(tti::TypeKind::StringLiteral(name))
    }
    TypeKind::LiteralNumber(value) => match value.parse::<f64>() {
      Ok(num) => store.intern_type(tti::TypeKind::NumberLiteral(OrderedFloat(num))),
      Err(_) => primitives.number,
    },
    TypeKind::LiteralBoolean(value) => store.intern_type(tti::TypeKind::BooleanLiteral(value)),
    TypeKind::Tuple(elems, readonly) => {
      let members: Vec<_> = elems
        .into_iter()
        .map(|ty| tti::TupleElem {
          ty: convert_type_for_display(ty, state, store, cache),
          optional: false,
          rest: false,
          readonly,
        })
        .collect();
      store.intern_type(tti::TypeKind::Tuple(members))
    }
    TypeKind::Array(inner) => {
      let inner = convert_type_for_display(inner, state, store, cache);
      store.intern_type(tti::TypeKind::Array {
        ty: inner,
        readonly: false,
      })
    }
    TypeKind::Union(types) => {
      let members: Vec<_> = types
        .into_iter()
        .map(|t| convert_type_for_display(t, state, store, cache))
        .collect();
      store.union(members)
    }
    TypeKind::Function { params, ret } => {
      let params: Vec<_> = params
        .into_iter()
        .map(|param| tti::Param {
          name: None,
          ty: convert_type_for_display(param, state, store, cache),
          optional: false,
          rest: false,
        })
        .collect();
      let sig = tti::Signature::new(params, convert_type_for_display(ret, state, store, cache));
      let sig_id = store.intern_signature(sig);
      store.intern_type(tti::TypeKind::Callable {
        overloads: vec![sig_id],
      })
    }
    TypeKind::Predicate {
      parameter,
      asserted,
      asserts,
    } => {
      let param = if parameter.is_empty() {
        None
      } else if parameter == "this" {
        Some(tti::PredicateParam::This)
      } else {
        // `TypeKind::Function` in this compact display representation does not
        // preserve parameter names, so a type predicate's target can only be
        // approximated. Default to the first positional argument to keep the
        // output deterministic.
        Some(tti::PredicateParam::Param(0))
      };
      let asserted = asserted.map(|ty| convert_type_for_display(ty, state, store, cache));
      store.intern_type(tti::TypeKind::Predicate {
        parameter: param,
        asserted,
        asserts,
      })
    }
    TypeKind::Mapped { source, value } => {
      let param = tti::TypeParamId(0);
      let source = convert_type_for_display(source, state, store, cache);
      let value = convert_type_for_display(value, state, store, cache);
      let mapped = tti::MappedType {
        param,
        source,
        value,
        readonly: tti::MappedModifier::Preserve,
        optional: tti::MappedModifier::Preserve,
        name_type: None,
        as_type: None,
      };
      store.intern_type(tti::TypeKind::Mapped(mapped))
    }
    TypeKind::Object(obj) => {
      let mut shape = tti::Shape::new();
      for (name, prop) in obj.props {
        let key = tti::PropKey::String(store.intern_name(name));
        let data = tti::PropData {
          ty: convert_type_for_display(prop.typ, state, store, cache),
          optional: prop.optional,
          readonly: prop.readonly,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        };
        shape.properties.push(tti::Property { key, data });
      }
      if let Some(value_type) = obj.string_index {
        shape.indexers.push(tti::Indexer {
          key_type: primitives.string,
          value_type: convert_type_for_display(value_type, state, store, cache),
          readonly: false,
        });
      }
      if let Some(value_type) = obj.number_index {
        shape.indexers.push(tti::Indexer {
          key_type: primitives.number,
          value_type: convert_type_for_display(value_type, state, store, cache),
          readonly: false,
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      store.intern_type(tti::TypeKind::Object(obj_id))
    }
  };
  cache.insert(ty, mapped);
  mapped
}

pub(super) fn callable_return_is_unknown(store: &Arc<tti::TypeStore>, ty: TypeId) -> bool {
  let prim = store.primitive_ids();
  match store.type_kind(ty) {
    tti::TypeKind::Callable { overloads } => overloads
      .iter()
      .any(|sig_id| store.signature(*sig_id).ret == prim.unknown),
    _ => false,
  }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct NamespaceMemberIndex {
  // (parent def, namespace bit) -> (member name -> candidate defs)
  by_parent: HashMap<(DefId, sem_ts::Namespace), HashMap<String, Vec<DefId>>>,
}

impl NamespaceMemberIndex {
  pub(super) fn insert(&mut self, parent: DefId, ns: sem_ts::Namespace, name: String, def: DefId) {
    self
      .by_parent
      .entry((parent, ns))
      .or_default()
      .entry(name)
      .or_default()
      .push(def);
  }

  pub(super) fn members(
    &self,
    parent: DefId,
    ns: sem_ts::Namespace,
    name: &str,
  ) -> Option<&[DefId]> {
    self
      .by_parent
      .get(&(parent, ns))
      .and_then(|map| map.get(name))
      .map(|defs| defs.as_slice())
  }

  pub(super) fn finalize(&mut self) {
    for map in self.by_parent.values_mut() {
      for defs in map.values_mut() {
        defs.sort_by_key(|id| id.0);
        defs.dedup();
      }
    }
  }
}

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

pub(super) fn export_assignment_path_for_file(
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

impl ProgramTypeResolver {
  pub(crate) fn new(
    host: Arc<dyn Host>,
    semantics: Arc<sem_ts::TsProgramSemantics>,
    def_kinds: Arc<HashMap<DefId, DefKind>>,
    def_files: Arc<HashMap<DefId, FileId>>,
    def_spans: Arc<HashMap<DefId, TextRange>>,
    registry: Arc<FileRegistry>,
    current_file: FileId,
    local_defs: HashMap<String, DefId>,
    exports: Arc<HashMap<FileId, ExportMap>>,
    module_namespace_defs: Arc<HashMap<FileId, DefId>>,
    namespace_members: Arc<NamespaceMemberIndex>,
    qualified_def_members: Arc<HashMap<(DefId, String, sem_ts::Namespace), DefId>>,
  ) -> Self {
    ProgramTypeResolver {
      semantics,
      def_kinds,
      def_files,
      def_spans,
      registry,
      host,
      current_file,
      local_defs,
      exports,
      module_namespace_defs,
      namespace_members,
      qualified_def_members,
    }
  }

  fn matches_namespace(kind: &DefKind, ns: sem_ts::Namespace) -> bool {
    ProgramState::def_namespaces(kind).contains(ns)
  }

  fn def_sort_key(&self, def: DefId, ns: sem_ts::Namespace) -> (u8, u8, u32, u32, u64) {
    let file = self
      .def_files
      .get(&def)
      .copied()
      .unwrap_or(FileId(u32::MAX));
    let origin = self.registry.lookup_origin(file);
    let origin_rank = if file == self.current_file {
      0
    } else if matches!(origin, Some(FileOrigin::Source)) {
      1
    } else {
      2
    };
    let pri = self.def_priority(def, ns);
    let span = self
      .def_spans
      .get(&def)
      .copied()
      .unwrap_or_else(|| TextRange::new(u32::MAX, u32::MAX));
    (origin_rank, pri, span.start, span.end, def.0)
  }

  fn pick_best_def(
    &self,
    defs: impl IntoIterator<Item = DefId>,
    ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    let mut best: Option<(u8, u8, u32, u32, u64, DefId)> = None;
    for def in defs {
      let Some(kind) = self.def_kinds.get(&def) else {
        continue;
      };
      if !Self::matches_namespace(kind, ns) {
        continue;
      }
      let key = self.def_sort_key(def, ns);
      best = match best {
        Some((best_rank, best_pri, best_start, best_end, best_id, best_def))
          if (best_rank, best_pri, best_start, best_end, best_id) <= key =>
        {
          Some((best_rank, best_pri, best_start, best_end, best_id, best_def))
        }
        _ => Some((key.0, key.1, key.2, key.3, key.4, def)),
      };
    }
    best.map(|(_, _, _, _, _, def)| def)
  }

  fn resolve_local(&self, name: &str, ns: sem_ts::Namespace) -> Option<DefId> {
    let def = self.local_defs.get(name).copied()?;
    let kind = self.def_kinds.get(&def)?;
    match kind {
      DefKind::ImportAlias(alias) => self
        .resolve_entity_name_path(&alias.path, ns)
        .or_else(|| Self::matches_namespace(kind, ns).then_some(def)),
      _ => Self::matches_namespace(kind, ns).then_some(def),
    }
  }

  fn resolve_entity_name_path(
    &self,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    match path {
      [] => None,
      [name] => self.resolve_symbol_in_module(name, final_ns),
      _ => self
        .resolve_namespace_import_path(path, final_ns)
        .or_else(|| self.resolve_namespace_member_path(path, final_ns)),
    }
  }

  fn collect_symbol_decls(&self, symbol: sem_ts::SymbolId, ns: sem_ts::Namespace) -> Vec<DefId> {
    let symbols = self.semantics.symbols();
    let mut defs: Vec<DefId> = self
      .semantics
      .symbol_decls(symbol, ns)
      .iter()
      .filter_map(|decl_id| {
        let decl = symbols.decl(*decl_id);
        let def = decl.def_id;
        self
          .def_kinds
          .get(&def)
          .and_then(|kind| Self::matches_namespace(kind, ns).then_some(def))
      })
      .collect();
    defs.sort_by_key(|id| id.0);
    defs.dedup();
    defs
  }

  fn resolve_namespace_symbol_defs(&self, name: &str) -> Option<Vec<DefId>> {
    if let Some(local_def) = self.resolve_local(name, sem_ts::Namespace::NAMESPACE) {
      if let Some(symbol) = self
        .semantics
        .symbol_for_def(local_def, sem_ts::Namespace::NAMESPACE)
      {
        let defs = self.collect_symbol_decls(symbol, sem_ts::Namespace::NAMESPACE);
        if !defs.is_empty() {
          return Some(defs);
        }
      }
      return Some(vec![local_def]);
    }

    let symbol = self
      .semantics
      .resolve_in_module(
        sem_ts::FileId(self.current_file.0),
        name,
        sem_ts::Namespace::NAMESPACE,
      )
      .or_else(|| self.global_symbol(name, sem_ts::Namespace::NAMESPACE))?;
    let defs = self.collect_symbol_decls(symbol, sem_ts::Namespace::NAMESPACE);
    (!defs.is_empty()).then_some(defs)
  }

  fn resolve_namespace_member_path(
    &self,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    if path.len() < 2 {
      return None;
    }
    let mut parents = self.resolve_namespace_symbol_defs(&path[0])?;
    // Resolve intermediate namespace segments (excluding final segment).
    for segment in path.iter().take(path.len() - 1).skip(1) {
      let mut next: Vec<DefId> = Vec::new();
      let mut seen: HashSet<DefId> = HashSet::new();
      for parent in parents.iter().copied() {
        if let Some(members) =
          self
            .namespace_members
            .members(parent, sem_ts::Namespace::NAMESPACE, segment)
        {
          for member in members.iter().copied() {
            if seen.insert(member) {
              next.push(member);
            }
          }
        }
      }
      if next.is_empty() {
        return None;
      }
      next.sort_by_key(|id| id.0);
      next.dedup();
      parents = next;
    }

    let final_segment = path.last()?;
    let mut candidates: Vec<DefId> = Vec::new();
    let mut seen: HashSet<DefId> = HashSet::new();
    for parent in parents.iter().copied() {
      if let Some(members) = self
        .namespace_members
        .members(parent, final_ns, final_segment)
      {
        for member in members.iter().copied() {
          if seen.insert(member) {
            candidates.push(member);
          }
        }
      }
    }
    self.pick_best_def(candidates, final_ns)
  }

  fn resolve_namespace_symbol_defs_in_file(
    &self,
    file: sem_ts::FileId,
    name: &str,
  ) -> Option<Vec<DefId>> {
    let symbol = self
      .semantics
      .resolve_in_module(file, name, sem_ts::Namespace::NAMESPACE)
      .or_else(|| self.global_symbol(name, sem_ts::Namespace::NAMESPACE))?;
    let defs = self.collect_symbol_decls(symbol, sem_ts::Namespace::NAMESPACE);
    (!defs.is_empty()).then_some(defs)
  }

  fn resolve_namespace_member_path_in_file(
    &self,
    file: sem_ts::FileId,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    if path.len() < 2 {
      return None;
    }
    let mut parents = self.resolve_namespace_symbol_defs_in_file(file, &path[0])?;
    for segment in path.iter().take(path.len() - 1).skip(1) {
      let mut next: Vec<DefId> = Vec::new();
      let mut seen: HashSet<DefId> = HashSet::new();
      for parent in parents.iter().copied() {
        if let Some(members) =
          self
            .namespace_members
            .members(parent, sem_ts::Namespace::NAMESPACE, segment)
        {
          for member in members.iter().copied() {
            if seen.insert(member) {
              next.push(member);
            }
          }
        }
      }
      if next.is_empty() {
        return None;
      }
      next.sort_by_key(|id| id.0);
      next.dedup();
      parents = next;
    }

    let final_segment = path.last()?;
    let mut candidates: Vec<DefId> = Vec::new();
    let mut seen: HashSet<DefId> = HashSet::new();
    for parent in parents.iter().copied() {
      if let Some(members) = self
        .namespace_members
        .members(parent, final_ns, final_segment)
      {
        for member in members.iter().copied() {
          if seen.insert(member) {
            candidates.push(member);
          }
        }
      }
    }
    self.pick_best_def(candidates, final_ns)
  }

  fn resolve_namespace_symbol_defs_in_ambient_module(
    &self,
    specifier: &str,
    name: &str,
  ) -> Option<Vec<DefId>> {
    let group = self
      .semantics
      .ambient_module_symbols()
      .get(specifier)?
      .get(name)?;
    let symbol = group.symbol_for(sem_ts::Namespace::NAMESPACE, self.semantics.symbols())?;
    let defs = self.collect_symbol_decls(symbol, sem_ts::Namespace::NAMESPACE);
    (!defs.is_empty()).then_some(defs)
  }

  fn resolve_namespace_member_path_in_ambient_module(
    &self,
    specifier: &str,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    if path.len() < 2 {
      return None;
    }
    let mut parents = self.resolve_namespace_symbol_defs_in_ambient_module(specifier, &path[0])?;
    for segment in path.iter().take(path.len() - 1).skip(1) {
      let mut next: Vec<DefId> = Vec::new();
      let mut seen: HashSet<DefId> = HashSet::new();
      for parent in parents.iter().copied() {
        if let Some(members) =
          self
            .namespace_members
            .members(parent, sem_ts::Namespace::NAMESPACE, segment)
        {
          for member in members.iter().copied() {
            if seen.insert(member) {
              next.push(member);
            }
          }
        }
      }
      if next.is_empty() {
        return None;
      }
      next.sort_by_key(|id| id.0);
      next.dedup();
      parents = next;
    }

    let final_segment = path.last()?;
    let mut candidates: Vec<DefId> = Vec::new();
    let mut seen: HashSet<DefId> = HashSet::new();
    for parent in parents.iter().copied() {
      if let Some(members) = self
        .namespace_members
        .members(parent, final_ns, final_segment)
      {
        for member in members.iter().copied() {
          if seen.insert(member) {
            candidates.push(member);
          }
        }
      }
    }
    self.pick_best_def(candidates, final_ns)
  }

  fn global_symbol(&self, name: &str, ns: sem_ts::Namespace) -> Option<sem_ts::SymbolId> {
    self
      .semantics
      .global_symbols()
      .get(name)
      .and_then(|group| group.symbol_for(ns, self.semantics.symbols()))
  }

  fn symbol_owner_file(&self, symbol: sem_ts::SymbolId) -> Option<sem_ts::FileId> {
    let sym = self.semantics.symbols().symbol(symbol);
    match &sym.origin {
      sem_ts::SymbolOrigin::Import { from, .. } => match from {
        sem_ts::ModuleRef::File(file) => Some(*file),
        _ => None,
      },
      _ => match &sym.owner {
        sem_ts::SymbolOwner::Module(file) => Some(*file),
        _ => None,
      },
    }
  }

  fn resolve_symbol_in_module(&self, name: &str, ns: sem_ts::Namespace) -> Option<DefId> {
    // Local bindings (including imports) shadow global declarations.
    if let Some(local) = self.resolve_local(name, ns) {
      return Some(local);
    }
    self
      .semantics
      .resolve_in_module(sem_ts::FileId(self.current_file.0), name, ns)
      .and_then(|symbol| self.pick_decl(symbol, ns))
      .or_else(|| {
        self
          .global_symbol(name, ns)
          .and_then(|symbol| self.pick_decl(symbol, ns))
      })
  }

  fn resolve_namespace_import_path(
    &self,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    if path.len() < 2 {
      return None;
    }
    let symbol = self
      .semantics
      .resolve_in_module(
        sem_ts::FileId(self.current_file.0),
        &path[0],
        sem_ts::Namespace::NAMESPACE,
      )
      .or_else(|| {
        self
          .semantics
          .resolve_in_module(sem_ts::FileId(self.current_file.0), &path[0], final_ns)
      })
      .or_else(|| {
        self.semantics.resolve_in_module(
          sem_ts::FileId(self.current_file.0),
          &path[0],
          sem_ts::Namespace::VALUE,
        )
      })
      .or_else(|| self.global_symbol(&path[0], sem_ts::Namespace::NAMESPACE))
      .or_else(|| self.global_symbol(&path[0], final_ns))
      .or_else(|| self.global_symbol(&path[0], sem_ts::Namespace::VALUE))?;
    let imported_name = match &self.semantics.symbols().symbol(symbol).origin {
      sem_ts::SymbolOrigin::Import { imported, .. } => Some(imported.clone()),
      _ => None,
    };

    if let sem_ts::SymbolOrigin::Import {
      from: sem_ts::ModuleRef::Ambient(specifier),
      imported,
    } = &self.semantics.symbols().symbol(symbol).origin
    {
      let origin = sem_ts::ModuleRef::Ambient(specifier.clone());
      if let Some(def) =
        self.resolve_export_path_in_module_ref(origin.clone(), &path[1..], final_ns)
      {
        return Some(def);
      }
      if imported != "*" {
        let mut segments = Vec::with_capacity(path.len());
        segments.push(imported.clone());
        segments.extend_from_slice(&path[1..]);
        return self.resolve_export_path_in_module_ref(origin, &segments, final_ns);
      }
      if let Some(export_assignment) =
        export_assignment_path_for_ambient_module(&self.semantics, specifier)
      {
        let mut combined = export_assignment;
        combined.extend_from_slice(&path[1..]);
        if let Some(def) =
          self.resolve_namespace_member_path_in_ambient_module(specifier, &combined, final_ns)
        {
          return Some(def);
        }
      }
      return None;
    }

    let Some(mut module) = self
      .import_origin_file(symbol)
      .or_else(|| self.symbol_owner_file(symbol))
    else {
      // `TsProgramSemantics` tracks exports across files/modules but does not
      // provide a direct way to traverse members of global `namespace`
      // declarations (e.g. `declare namespace JSX { interface Element {} }`).
      // These are still represented in the lowered definition tree with parent
      // links, so fall back to the canonical parent->member map derived from HIR.
      let mut current = self
        .pick_decl(symbol, sem_ts::Namespace::NAMESPACE)
        .or_else(|| self.pick_decl(symbol, final_ns))
        .or_else(|| self.pick_decl(symbol, sem_ts::Namespace::VALUE))?;

      for (idx, segment) in path.iter().enumerate().skip(1) {
        let is_last = idx + 1 == path.len();
        let ns = if is_last {
          final_ns
        } else {
          sem_ts::Namespace::NAMESPACE
        };
        current = *self
          .qualified_def_members
          .get(&(current, segment.clone(), ns))?;
      }

      return Some(current);
    };
    let origin = module;
    if let Some(def) = self.resolve_export_path(&path[1..], &mut module, final_ns) {
      return Some(def);
    }

    // Named imports of a namespace re-export (e.g. `import { ns } from "./mod"; type T = ns.Foo`)
    // require following the namespace export edge before resolving the remaining segments.
    let Some(imported_name) = imported_name else {
      return None;
    };
    if imported_name == "*" {
      if let Some(export_assignment) =
        export_assignment_path_for_file(self.semantics.as_ref(), origin)
      {
        let mut combined = export_assignment;
        combined.extend_from_slice(&path[1..]);
        if let Some(def) = self.resolve_namespace_member_path_in_file(origin, &combined, final_ns) {
          return Some(def);
        }
      }
      return None;
    }
    let mut segments = Vec::with_capacity(path.len());
    segments.push(imported_name);
    segments.extend_from_slice(&path[1..]);
    let mut module = origin;
    self
      .resolve_export_path(&segments, &mut module, final_ns)
      .or_else(|| self.resolve_namespace_member_path_in_file(origin, &segments, final_ns))
  }

  fn resolve_export_path(
    &self,
    segments: &[String],
    module: &mut sem_ts::FileId,
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    for (idx, segment) in segments.iter().enumerate() {
      let is_last = idx + 1 == segments.len();
      if let Some(exports) = self.exports.get(&FileId(module.0)) {
        if let Some(entry) = exports.get(segment) {
          if is_last {
            if let Some(def) = entry.def {
              return Some(def);
            }
          }
        }
      }
      let ns = if is_last {
        final_ns
      } else {
        sem_ts::Namespace::NAMESPACE
      };
      let symbol = self.semantics.resolve_export(*module, segment, ns)?;
      if is_last {
        if let Some(def) = self.pick_decl(symbol, final_ns) {
          return Some(def);
        }
        if final_ns.contains(sem_ts::Namespace::VALUE) {
          if let sem_ts::SymbolOrigin::Import { from, imported } =
            &self.semantics.symbols().symbol(symbol).origin
          {
            if imported == "*" {
              if let sem_ts::ModuleRef::File(dep_file) = from {
                return self.module_namespace_defs.get(&FileId(dep_file.0)).copied();
              }
            }
          }
        }
        return None;
      }
      *module = self.import_origin_file(symbol)?;
    }
    None
  }

  fn resolve_export_symbol_in_module_ref(
    &self,
    module: &sem_ts::ModuleRef,
    name: &str,
    ns: sem_ts::Namespace,
  ) -> Option<sem_ts::SymbolId> {
    match module {
      sem_ts::ModuleRef::File(file) => self.semantics.resolve_export(*file, name, ns),
      sem_ts::ModuleRef::Ambient(specifier) => self
        .semantics
        .exports_of_ambient_module(specifier)?
        .get(name)?
        .symbol_for(ns, self.semantics.symbols()),
      sem_ts::ModuleRef::Unresolved(_) => None,
    }
  }

  fn resolve_export_path_in_module_ref(
    &self,
    mut module: sem_ts::ModuleRef,
    segments: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    if segments.is_empty() {
      return None;
    }
    for (idx, segment) in segments.iter().enumerate() {
      let is_last = idx + 1 == segments.len();
      let ns = if is_last {
        final_ns
      } else {
        sem_ts::Namespace::NAMESPACE
      };
      let symbol = self.resolve_export_symbol_in_module_ref(&module, segment, ns)?;
      if is_last {
        return self.pick_decl(symbol, final_ns);
      }
      module = match &self.semantics.symbols().symbol(symbol).origin {
        sem_ts::SymbolOrigin::Import { from, .. } => from.clone(),
        _ => return None,
      };
    }
    None
  }

  fn pick_decl(&self, symbol: sem_ts::SymbolId, ns: sem_ts::Namespace) -> Option<DefId> {
    let symbols = self.semantics.symbols();
    // Prefer a deterministic "canonical" declaration when a symbol has multiple
    // merged declarations (common in the upstream `lib.*.d.ts` set, e.g.
    // `interface Promise<T> {}` is augmented in several files).
    //
    // We intentionally do *not* use the semantic decl ordering as a tie-breaker
    // because it may depend on hash-map iteration order. Picking the lowest
    // `DefId` stabilizes resolution across callers and ensures that references
    // to merged globals (Promise, SymbolConstructor, ...) share the same
    // referenced definition identity.
    let mut best: Option<(u8, DefId)> = None;
    for decl_id in self.semantics.symbol_decls(symbol, ns).iter() {
      let decl = symbols.decl(*decl_id);
      let def = decl.def_id;
      let Some(kind) = self.def_kinds.get(&def) else {
        continue;
      };
      if !Self::matches_namespace(kind, ns) {
        continue;
      }
      let pri = self.def_priority(def, ns);
      best = match best {
        Some((best_pri, best_def)) if (best_pri, best_def.0) <= (pri, def.0) => {
          Some((best_pri, best_def))
        }
        _ => Some((pri, def)),
      };
    }
    best.map(|(_, def)| def)
  }

  fn def_priority(&self, def: DefId, ns: sem_ts::Namespace) -> u8 {
    let Some(kind) = self.def_kinds.get(&def) else {
      return u8::MAX;
    };
    if !Self::matches_namespace(kind, ns) {
      return u8::MAX;
    }
      if ns.contains(sem_ts::Namespace::VALUE) {
        return match kind {
          DefKind::Function(_) | DefKind::Class(_) | DefKind::Enum(_) => 0,
          DefKind::Var(var) if var.body != MISSING_BODY => 1,
          DefKind::Namespace(_) | DefKind::Module(_) => 2,
          DefKind::Import(_) | DefKind::ImportAlias(_) => 3,
          DefKind::Var(_) => 4,
          DefKind::VarDeclarator(_) => 5,
        DefKind::Interface(_) | DefKind::TypeAlias(_) => 5,
      };
    }
    if ns.contains(sem_ts::Namespace::TYPE) {
      return match kind {
        DefKind::Interface(_) => 0,
        DefKind::TypeAlias(_) => 1,
        DefKind::Class(_) => 2,
        DefKind::Enum(_) => 3,
        DefKind::Import(_) | DefKind::ImportAlias(_) => 4,
        DefKind::VarDeclarator(_) => 5,
        _ => 5,
      };
    }
    if ns.contains(sem_ts::Namespace::NAMESPACE) {
      return match kind {
        DefKind::Namespace(_) | DefKind::Module(_) => 0,
        DefKind::Import(_) | DefKind::ImportAlias(_) => 1,
        DefKind::VarDeclarator(_) => 2,
        _ => 2,
      };
    }
    u8::MAX
  }

  fn import_origin_file(&self, symbol: sem_ts::SymbolId) -> Option<sem_ts::FileId> {
    match &self.semantics.symbols().symbol(symbol).origin {
      sem_ts::SymbolOrigin::Import { from, .. } => match from {
        sem_ts::ModuleRef::File(file) => Some(*file),
        _ => None,
      },
      _ => None,
    }
  }
}

impl TypeResolver for ProgramTypeResolver {
  fn resolve_type_name(&self, path: &[String]) -> Option<DefId> {
    match path {
      [] => None,
      [name] => self.resolve_symbol_in_module(name, sem_ts::Namespace::TYPE),
      _ => self
        .resolve_namespace_import_path(path, sem_ts::Namespace::TYPE)
        .or_else(|| self.resolve_namespace_member_path(path, sem_ts::Namespace::TYPE)),
    }
  }

  fn resolve_typeof(&self, path: &[String]) -> Option<DefId> {
    match path {
      [] => None,
      [name] => self.resolve_symbol_in_module(name, sem_ts::Namespace::VALUE),
      _ => self
        .resolve_namespace_import_path(path, sem_ts::Namespace::VALUE)
        .or_else(|| self.resolve_namespace_member_path(path, sem_ts::Namespace::VALUE)),
    }
  }

  fn resolve_import_type(&self, module: &str, qualifier: Option<&[String]>) -> Option<DefId> {
    let Some(from_key) = self.registry.lookup_key(self.current_file) else {
      return None;
    };
    let target_key = self.host.resolve(&from_key, module)?;
    let target_file = self.registry.lookup_id(&target_key)?;
    let mut module = sem_ts::FileId(target_file.0);
    let Some(path) = qualifier else {
      return None;
    };
    if path.is_empty() {
      return None;
    }
    self.resolve_export_path(path, &mut module, sem_ts::Namespace::TYPE)
  }

  fn resolve_import_typeof(&self, module: &str, qualifier: Option<&[String]>) -> Option<DefId> {
    let Some(from_key) = self.registry.lookup_key(self.current_file) else {
      return None;
    };
    let target_key = self.host.resolve(&from_key, module)?;
    let target_file = self.registry.lookup_id(&target_key)?;
    let mut module = sem_ts::FileId(target_file.0);
    let Some(path) = qualifier else {
      return self.module_namespace_defs.get(&target_file).copied();
    };
    if path.is_empty() {
      return self.module_namespace_defs.get(&target_file).copied();
    }
    self.resolve_export_path(path, &mut module, sem_ts::Namespace::VALUE)
  }
}

pub(super) fn lookup_interned_property_type(
  store: &tti::TypeStore,
  expander: Option<&dyn tti::RelateTypeExpander>,
  ty: tti::TypeId,
  name: &str,
) -> Option<tti::TypeId> {
  if !store.contains_type_id(ty) {
    return None;
  }
  let ty = store.canon(ty);
  match store.type_kind(ty) {
    tti::TypeKind::Union(members) | tti::TypeKind::Intersection(members) => {
      let mut collected = Vec::new();
      for member in members.iter().copied() {
        if let Some(prop) = lookup_interned_property_type(store, expander, member, name) {
          collected.push(prop);
        }
      }
      if collected.is_empty() {
        None
      } else {
        Some(store.union(collected))
      }
    }
    tti::TypeKind::Ref { def, args } => expander
      .and_then(|exp| exp.expand_ref(store, def, &args))
      .and_then(|expanded| lookup_interned_property_type(store, expander, expanded, name)),
    tti::TypeKind::Object(obj_id) => {
      let shape = store.shape(store.object(obj_id).shape);
      for prop in shape.properties.iter() {
        let matches = match prop.key {
          PropKey::String(name_id) => store.name(name_id) == name,
          PropKey::Number(num) => num.to_string() == name,
          _ => false,
        };
        if matches {
          return Some(prop.data.ty);
        }
      }
      let probe_key = if name.parse::<f64>().is_ok() {
        PropKey::Number(0)
      } else {
        PropKey::String(store.intern_name(String::new()))
      };
      for indexer in shape.indexers.iter() {
        if crate::type_queries::indexer_accepts_key(&probe_key, indexer.key_type, store) {
          return Some(indexer.value_type);
        }
      }
      None
    }
    tti::TypeKind::Array { ty, .. } => {
      if name == "length" {
        Some(store.primitive_ids().number)
      } else {
        Some(ty)
      }
    }
    _ => None,
  }
}

#[derive(Clone)]
pub(super) struct DeclTypeResolver {
  file: FileId,
  defs: Arc<HashMap<(FileId, String), DefId>>,
  qualified_def_members: Arc<HashMap<(DefId, String, sem_ts::Namespace), DefId>>,
  by_name: HashMap<String, DefId>,
}

impl DeclTypeResolver {
  pub(super) fn new(
    file: FileId,
    defs: Arc<HashMap<(FileId, String), DefId>>,
    qualified_def_members: Arc<HashMap<(DefId, String, sem_ts::Namespace), DefId>>,
  ) -> Self {
    let mut by_name = HashMap::new();
    let mut ordered: Vec<(FileId, String, DefId)> = defs
      .iter()
      .map(|((file, name), def)| (*file, name.clone(), *def))
      .collect();
    ordered.sort_by(|a, b| (a.1.as_str(), a.0 .0, a.2 .0).cmp(&(b.1.as_str(), b.0 .0, b.2 .0)));
    for (_file, name, def) in ordered.into_iter() {
      by_name.entry(name).or_insert(def);
    }
    DeclTypeResolver {
      file,
      defs,
      qualified_def_members,
      by_name,
    }
  }

  fn resolve_name(&self, name: &str) -> Option<DefId> {
    self
      .defs
      .get(&(self.file, name.to_string()))
      .copied()
      .or_else(|| self.by_name.get(name).copied())
  }

  fn resolve_qualified(&self, path: &[String], final_ns: sem_ts::Namespace) -> Option<DefId> {
    let (first, rest) = path.split_first()?;
    let mut current = self.resolve_name(first)?;
    for (idx, segment) in rest.iter().enumerate() {
      let is_last = idx + 1 == rest.len();
      let ns = if is_last {
        final_ns
      } else {
        sem_ts::Namespace::NAMESPACE
      };
      current = *self
        .qualified_def_members
        .get(&(current, segment.clone(), ns))?;
    }
    Some(current)
  }
}

impl TypeResolver for DeclTypeResolver {
  fn resolve_type_name(&self, path: &[String]) -> Option<tti::DefId> {
    if path.len() < 2 {
      path.last().and_then(|name| self.resolve_name(name))
    } else {
      self.resolve_qualified(path, sem_ts::Namespace::TYPE)
    }
  }

  fn resolve_typeof(&self, path: &[String]) -> Option<tti::DefId> {
    if path.len() < 2 {
      self.resolve_type_name(path)
    } else {
      self.resolve_qualified(path, sem_ts::Namespace::VALUE)
    }
  }
}
