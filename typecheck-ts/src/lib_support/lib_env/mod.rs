mod prepared;

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use types_ts_interned::TypeOptions;

use crate::FileId;

pub(crate) use prepared::{prepare_lib, PreparedLib};

use super::{CompilerOptions, LibFile, LibSet};

/// Loaded libraries for a particular set of options.
#[derive(Clone, Debug)]
pub struct LoadedLibs {
  pub lib_set: LibSet,
  libs: Arc<Vec<PreparedLib>>,
}

impl LoadedLibs {
  pub fn empty() -> Self {
    LoadedLibs {
      lib_set: LibSet::empty(),
      libs: Arc::new(Vec::new()),
    }
  }

  pub(crate) fn libs(&self) -> &[PreparedLib] {
    &self.libs
  }
}

#[derive(Default)]
struct LibManagerCounters {
  hits: AtomicUsize,
  misses: AtomicUsize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LibManagerStats {
  pub cache_hits: usize,
  pub cache_misses: usize,
}

/// Simple manager that caches bundled libs for a given option set and tracks loads.
#[derive(Default)]
pub struct LibManager {
  cache: Mutex<HashMap<LibCacheKey, Arc<LoadedLibs>>>,
  stats: LibManagerCounters,
}

impl LibManager {
  pub fn new() -> Self {
    LibManager {
      cache: Mutex::new(HashMap::new()),
      stats: LibManagerCounters::default(),
    }
  }

  /// How many times bundled libs were recomputed (useful for invalidation tests).
  pub fn load_count(&self) -> usize {
    self.stats.misses.load(Ordering::SeqCst)
  }

  /// Return libs appropriate for the provided compiler options. If the options change,
  /// cached results are invalidated and libs are reloaded.
  pub fn bundled_libs(&self, options: &CompilerOptions) -> LoadedLibs {
    let key = LibCacheKey::new(options);
    if let Some(entry) = self.cache.lock().unwrap().get(&key).cloned() {
      self.record_hit();
      return entry.as_ref().clone();
    }

    let prepared = Arc::new(prepare_bundled_libs(&key));
    let mut cache = self.cache.lock().unwrap();
    let entry = cache.entry(key).or_insert_with(|| {
      self.record_miss();
      prepared.clone()
    });
    if !Arc::ptr_eq(entry, &prepared) {
      self.record_hit();
    }
    entry.as_ref().clone()
  }

  pub fn stats(&self) -> LibManagerStats {
    LibManagerStats {
      cache_hits: self.stats.hits.load(Ordering::SeqCst),
      cache_misses: self.stats.misses.load(Ordering::SeqCst),
    }
  }

  fn record_hit(&self) {
    self.stats.hits.fetch_add(1, Ordering::SeqCst);
  }

  fn record_miss(&self) {
    self.stats.misses.fetch_add(1, Ordering::SeqCst);
  }
}

/// Subset of compiler options that affect type semantics for libraries.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct TypeOptionsKey {
  strict_null_checks: bool,
  strict_function_types: bool,
  exact_optional_property_types: bool,
  no_unchecked_indexed_access: bool,
}

impl From<TypeOptions> for TypeOptionsKey {
  fn from(options: TypeOptions) -> Self {
    TypeOptionsKey {
      strict_null_checks: options.strict_null_checks,
      strict_function_types: options.strict_function_types,
      exact_optional_property_types: options.exact_optional_property_types,
      no_unchecked_indexed_access: options.no_unchecked_indexed_access,
    }
  }
}

impl From<&CompilerOptions> for TypeOptionsKey {
  fn from(options: &CompilerOptions) -> Self {
    TypeOptionsKey::from(TypeOptions::from(options))
  }
}

/// Cache key combining the selected libs with type-affecting options.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct LibCacheKey {
  lib_set: LibSet,
  type_options: TypeOptionsKey,
}

impl LibCacheKey {
  fn new(options: &CompilerOptions) -> Self {
    LibCacheKey {
      lib_set: LibSet::for_options(options),
      type_options: TypeOptionsKey::from(options),
    }
  }
}

fn prepare_bundled_libs(key: &LibCacheKey) -> LoadedLibs {
  let files = load_bundled(&key.lib_set);
  let libs: Vec<_> = files.into_iter().map(prepare_lib).collect();
  LoadedLibs {
    lib_set: key.lib_set.clone(),
    libs: Arc::new(libs),
  }
}

fn load_bundled(lib_set: &LibSet) -> Vec<LibFile> {
  #[cfg(feature = "bundled-libs")]
  {
    bundled::load_bundled(lib_set)
  }

  #[cfg(not(feature = "bundled-libs"))]
  {
    let _ = lib_set;
    Vec::new()
  }
}

fn bundled_file_id_for(index: usize) -> FileId {
  FileId(1_000_000 + index as u32)
}

#[cfg(feature = "bundled-libs")]
mod bundled {
  use std::sync::Arc;

  use super::super::FileKind;
  use super::super::LibFile;
  use super::super::LibName;
  use super::super::LibSet;
  use super::bundled_file_id_for;

  pub fn load_bundled(lib_set: &LibSet) -> Vec<LibFile> {
    lib_set
      .libs()
      .iter()
      .enumerate()
      .map(|(idx, name)| LibFile {
        id: bundled_file_id_for(idx),
        name: Arc::from(name.as_str()),
        kind: FileKind::Dts,
        text: Arc::from(text_for(name)),
      })
      .collect()
  }

  fn text_for(name: &LibName) -> &'static str {
    match name {
      LibName::Es5 => include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/fixtures/libs/lib.es5.d.ts"
      )),
      LibName::Es2015 => include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/fixtures/libs/lib.es2015.d.ts"
      )),
      LibName::Es2016 => include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/fixtures/libs/lib.es2016.d.ts"
      )),
      LibName::Es2017 => include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/fixtures/libs/lib.es2017.d.ts"
      )),
      LibName::Es2018 => include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/fixtures/libs/lib.es2018.d.ts"
      )),
      LibName::Es2019 => include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/fixtures/libs/lib.es2019.d.ts"
      )),
      LibName::Es2020 => include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/fixtures/libs/lib.es2020.d.ts"
      )),
      LibName::Es2021 => include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/fixtures/libs/lib.es2021.d.ts"
      )),
      LibName::Es2022 => include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/fixtures/libs/lib.es2022.d.ts"
      )),
      LibName::EsNext => include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/fixtures/libs/lib.esnext.d.ts"
      )),
      LibName::Dom => include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/fixtures/libs/lib.dom.d.ts"
      )),
    }
  }
}
