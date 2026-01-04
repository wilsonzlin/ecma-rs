use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use diagnostics::{Diagnostic, FileId, Span, TextRange};

use super::{CompilerOptions, FileKind, LibFile, LibSet};
use crate::codes;

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
#[derive(Debug, Default)]
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

pub fn bundled_lib_file(name: super::LibName) -> Option<LibFile> {
  #[cfg(feature = "bundled-libs")]
  {
    bundled::lib_file(name)
  }

  #[cfg(not(feature = "bundled-libs"))]
  {
    let _ = name;
    None
  }
}

#[cfg(feature = "bundled-libs")]
mod bundled {
  use std::sync::Arc;

  use include_dir::{include_dir, Dir};

  use super::super::FileKind;
  use super::super::LibFile;
  use super::super::LibName;
  use super::super::LibSet;
  use crate::FileKey;

  static LIB_DIR: Dir<'_> = include_dir!("$CARGO_MANIFEST_DIR/fixtures/libs");

  pub fn load_bundled(lib_set: &LibSet) -> Vec<LibFile> {
    lib_set
      .libs()
      .iter()
      .cloned()
      .filter_map(lib_file)
      .collect()
  }

  pub(super) fn lib_file(name: LibName) -> Option<LibFile> {
    let filename = name.file_name();
    let text = text_for(filename.as_str())?;
    let key = FileKey::new(format!("lib:{filename}"));
    Some(LibFile {
      key,
      name: Arc::from(filename),
      kind: FileKind::Dts,
      text: Arc::from(text),
    })
  }

  fn text_for(filename: &str) -> Option<&'static str> {
    LIB_DIR.get_file(filename).and_then(|file| file.contents_utf8())
  }
}

/// Result of validating a set of libraries.
#[derive(Clone, Debug)]
pub struct LibValidationResult {
  /// Libraries that passed validation, paired with their allocated [`FileId`].
  pub libs: Vec<(LibFile, FileId)>,
  /// Diagnostics produced while validating the libraries.
  pub diagnostics: Vec<Diagnostic>,
}

impl LibValidationResult {
  /// Empty validation result used when no libs are available.
  pub fn empty() -> Self {
    LibValidationResult {
      libs: Vec::new(),
      diagnostics: Vec::new(),
    }
  }
}

/// Merge host-provided libs with bundled libs selected from [`CompilerOptions`].
pub fn collect_libs(
  options: &CompilerOptions,
  mut host_libs: Vec<LibFile>,
  lib_manager: &LibManager,
) -> Vec<LibFile> {
  let bundled = lib_manager.bundled_libs(options);
  host_libs.extend(bundled.files);
  host_libs
}

/// Filter out non-`.d.ts` libraries, emitting diagnostics for any ignored entries
/// and for the absence of any valid libs.
pub fn validate_libs(
  mut libs: Vec<LibFile>,
  mut file_id_for: impl FnMut(&LibFile) -> FileId,
) -> LibValidationResult {
  if libs.is_empty() {
    return LibValidationResult {
      libs: Vec::new(),
      diagnostics: vec![codes::NO_LIBS_LOADED.error(
        "No library files were loaded. Provide libs via the host or enable the bundled-libs feature / disable no_default_lib.",
        Span::new(FileId(u32::MAX), TextRange::new(0, 0)),
      )],
    };
  }

  libs.sort_by(|a, b| (a.name.as_ref(), a.key.as_str()).cmp(&(b.name.as_ref(), b.key.as_str())));

  let mut diagnostics = Vec::new();
  let mut filtered = Vec::new();
  for lib in libs {
    let file_id = file_id_for(&lib);
    let is_dts = lib.kind == FileKind::Dts || lib.name.ends_with(".d.ts");
    if !is_dts {
      diagnostics.push(codes::NON_DTS_LIB.warning(
        format!(
          "Library '{}' is not a .d.ts file; it will be ignored for global declarations.",
          lib.name
        ),
        Span::new(file_id, TextRange::new(0, 0)),
      ));
      continue;
    }
    filtered.push((lib, file_id));
  }

  if filtered.is_empty() {
    diagnostics.push(codes::NO_LIBS_LOADED.error(
      "No library files were loaded. Provide libs via the host or enable the bundled-libs feature / disable no_default_lib.",
      Span::new(FileId(u32::MAX), TextRange::new(0, 0)),
    ));
  }

  LibValidationResult {
    libs: filtered,
    diagnostics,
  }
}
