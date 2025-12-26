use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use super::CompilerOptions;
use super::LibFile;
use super::LibSet;

/// Loaded libraries for a particular set of options.
#[derive(Clone, Debug)]
pub struct LoadedLibs {
  pub lib_set: LibSet,
  pub files: Vec<LibFile>,
}

impl LoadedLibs {
  pub fn empty() -> Self {
    LoadedLibs {
      lib_set: LibSet::empty(),
      files: Vec::new(),
    }
  }
}

/// Simple manager that caches bundled libs for a given option set and tracks loads.
#[derive(Default)]
pub struct LibManager {
  cache: Mutex<Option<(CompilerOptions, LoadedLibs)>>,
  load_count: AtomicUsize,
}

impl LibManager {
  pub fn new() -> Self {
    LibManager {
      cache: Mutex::new(None),
      load_count: AtomicUsize::new(0),
    }
  }

  /// How many times bundled libs were recomputed (useful for invalidation tests).
  pub fn load_count(&self) -> usize {
    self.load_count.load(Ordering::SeqCst)
  }

  /// Return libs appropriate for the provided compiler options. If the options change,
  /// cached results are invalidated and libs are reloaded.
  pub fn bundled_libs(&self, options: &CompilerOptions) -> LoadedLibs {
    let mut cache = self.cache.lock().unwrap();
    if let Some((ref cached_opts, ref libs)) = *cache {
      if cached_opts == options {
        return libs.clone();
      }
    }

    let lib_set = LibSet::for_options(options);
    let files = load_bundled(&lib_set);
    let result = LoadedLibs {
      lib_set: lib_set.clone(),
      files,
    };
    *cache = Some((options.clone(), result.clone()));
    self.load_count.fetch_add(1, Ordering::SeqCst);
    result
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

#[cfg(feature = "bundled-libs")]
mod bundled {
  use std::sync::Arc;

  use super::super::FileKind;
  use super::super::LibFile;
  use super::super::LibName;
  use super::super::LibSet;
  use crate::FileKey;

  pub fn load_bundled(lib_set: &LibSet) -> Vec<LibFile> {
    lib_set
      .libs()
      .iter()
      .map(|name| LibFile {
        key: FileKey::new(format!("lib:{}", name.option_name())),
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
