use std::collections::{BTreeMap, HashMap};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use ::semantic_js::ts::{self as sem_ts, locals};
use diagnostics::{FileId, TextRange};
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;

use crate::symbols::{semantic_js, SymbolOccurrence};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalSymbolInfo {
  pub file: FileId,
  pub name: String,
  pub span: Option<TextRange>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolIndex {
  pub occurrences: Arc<[SymbolOccurrence]>,
  pub locals: Arc<BTreeMap<semantic_js::SymbolId, LocalSymbolInfo>>,
}

impl SymbolIndex {
  pub fn empty() -> Self {
    SymbolIndex {
      occurrences: Arc::from([]),
      locals: Arc::new(BTreeMap::new()),
    }
  }
}

/// Deterministic symbol occurrences and synthetic local symbol metadata for a
/// single file.
pub(crate) fn symbol_index_for_file(
  file: FileId,
  mut ast: Node<TopLevel>,
  semantics: Option<&sem_ts::TsProgramSemantics>,
) -> SymbolIndex {
  let locals = locals::bind_ts_locals(&mut ast, file);

  let mut occurrences = Vec::new();
  let mut locals_info: BTreeMap<semantic_js::SymbolId, LocalSymbolInfo> = BTreeMap::new();
  let mut cache: HashMap<(sem_ts::SymbolId, sem_ts::Namespace), semantic_js::SymbolId> =
    HashMap::new();

  for (local_id, data) in locals.symbols.iter() {
    if let Some(span) = data.span {
      let symbol = map_local_symbol(
        file,
        *local_id,
        &locals,
        pick_namespace(data.namespaces, sem_ts::Namespace::VALUE),
        semantics,
        &mut cache,
        &mut locals_info,
      );
      occurrences.push(SymbolOccurrence {
        range: span,
        symbol,
      });
    }
  }

  for (range, local_symbol) in locals.expr_resolutions() {
    let symbol = map_local_symbol(
      file,
      *local_symbol,
      &locals,
      sem_ts::Namespace::VALUE,
      semantics,
      &mut cache,
      &mut locals_info,
    );
    occurrences.push(SymbolOccurrence {
      range: *range,
      symbol,
    });
  }

  for (range, local_symbol) in locals.type_resolutions() {
    let symbol = map_local_symbol(
      file,
      *local_symbol,
      &locals,
      sem_ts::Namespace::TYPE,
      semantics,
      &mut cache,
      &mut locals_info,
    );
    occurrences.push(SymbolOccurrence {
      range: *range,
      symbol,
    });
  }

  occurrences.sort_by_key(|occ| (occ.range.start, occ.range.end, occ.symbol.0));
  occurrences.dedup_by(|a, b| a.range == b.range && a.symbol == b.symbol);

  SymbolIndex {
    occurrences: Arc::from(occurrences),
    locals: Arc::new(locals_info),
  }
}

fn map_local_symbol(
  file: FileId,
  local_symbol: sem_ts::SymbolId,
  locals: &locals::TsLocalSemantics,
  ns_hint: sem_ts::Namespace,
  semantics: Option<&sem_ts::TsProgramSemantics>,
  cache: &mut HashMap<(sem_ts::SymbolId, sem_ts::Namespace), semantic_js::SymbolId>,
  locals_info: &mut BTreeMap<semantic_js::SymbolId, LocalSymbolInfo>,
) -> semantic_js::SymbolId {
  if let Some(symbol) = cache.get(&(local_symbol, ns_hint)) {
    return *symbol;
  }

  let data = locals.symbol(local_symbol);
  let name = locals
    .names
    .get(&data.name)
    .cloned()
    .unwrap_or_else(String::new);
  let ns = pick_namespace(data.namespaces, ns_hint);

  let mapped = semantics.and_then(|sem| {
    if data.decl_scope == locals.root_scope() {
      map_semantic_symbol(sem, file, &name, ns)
    } else {
      None
    }
  });

  let public_symbol = mapped
    .map(Into::into)
    .unwrap_or_else(|| synthetic_symbol_id(file, local_symbol, data, ns));

  if mapped.is_none() && !name.is_empty() {
    locals_info.entry(public_symbol).or_insert(LocalSymbolInfo {
      file,
      name,
      span: data.span,
    });
  }

  cache.insert((local_symbol, ns), public_symbol);
  public_symbol
}

fn map_semantic_symbol(
  semantics: &sem_ts::TsProgramSemantics,
  file: FileId,
  name: &str,
  ns: sem_ts::Namespace,
) -> Option<sem_ts::SymbolId> {
  let symbol = semantics.resolve_in_module(sem_ts::FileId(file.0), name, ns)?;
  let sem_symbol = semantics.symbols().symbol(symbol);
  match &sem_symbol.origin {
    sem_ts::SymbolOrigin::Import {
      from: sem_ts::ModuleRef::File(from),
      imported,
    } => semantics
      .resolve_export(*from, imported, ns)
      .or(Some(symbol)),
    _ => Some(symbol),
  }
}

fn pick_namespace(available: sem_ts::Namespace, hint: sem_ts::Namespace) -> sem_ts::Namespace {
  if available.contains(hint) {
    return hint;
  }
  for candidate in [
    sem_ts::Namespace::VALUE,
    sem_ts::Namespace::TYPE,
    sem_ts::Namespace::NAMESPACE,
  ] {
    if available.contains(candidate) {
      return candidate;
    }
  }
  hint
}

/// Deterministic synthetic symbol identifier for locals that are not represented
/// in the global TS semantics. The hash incorporates file, scope, span, and
/// namespace to keep shadowed bindings distinct while remaining stable across
/// runs. The high bit is set to avoid clashing with `semantic-js` program IDs.
fn synthetic_symbol_id(
  file: FileId,
  local_id: sem_ts::SymbolId,
  data: &locals::SymbolData,
  ns: sem_ts::Namespace,
) -> semantic_js::SymbolId {
  const LOCAL_DOMAIN: u64 = 0x7473_6c6f_6361_6c; // "ts_local"
  let span = data.span.unwrap_or_else(|| TextRange::new(0, 0));
  let hash = stable_hash_u32(&(
    LOCAL_DOMAIN,
    file.0,
    local_id.raw(),
    data.decl_scope.raw(),
    span.start,
    span.end,
    ns.bits(),
  ));
  // Set the high bit to avoid colliding with stable IDs from semantics.
  semantic_js::SymbolId(u64::from(hash) | (1u64 << 63))
}

fn stable_hash_u32<T: Hash>(value: &T) -> u32 {
  struct StableHasher(u64);

  impl StableHasher {
    const OFFSET: u64 = 0xcbf29ce484222325;
    const PRIME: u64 = 0x100000001b3;

    fn new() -> Self {
      StableHasher(Self::OFFSET)
    }
  }

  impl Hasher for StableHasher {
    fn finish(&self) -> u64 {
      self.0
    }

    fn write(&mut self, bytes: &[u8]) {
      for b in bytes {
        self.0 ^= *b as u64;
        self.0 = self.0.wrapping_mul(Self::PRIME);
      }
    }
  }

  let mut hasher = StableHasher::new();
  value.hash(&mut hasher);
  let hash = hasher.finish();
  (hash ^ (hash >> 32)) as u32
}
