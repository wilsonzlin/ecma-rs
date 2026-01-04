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
    Some(bundled::lib_file(name))
  }

  #[cfg(not(feature = "bundled-libs"))]
  {
    let _ = name;
    None
  }
}

pub fn bundled_lib_file_by_option_name(name: &str) -> Option<LibFile> {
  #[cfg(feature = "bundled-libs")]
  {
    bundled::lib_file_by_option_name(name)
  }

  #[cfg(not(feature = "bundled-libs"))]
  {
    let _ = name;
    None
  }
}

#[cfg(feature = "bundled-libs")]
mod bundled {
  use std::collections::{BTreeSet, VecDeque};
  use std::sync::Arc;

  use super::super::{FileKind, LibFile, LibName, LibSet};
  use crate::FileKey;

  pub(super) fn lib_file(name: LibName) -> LibFile {
    lib_file_by_option_name(name.as_str())
      .unwrap_or_else(|| panic!("missing bundled TypeScript lib '{}'", name.as_str()))
  }

  pub(super) fn lib_file_by_option_name(option_name: &str) -> Option<LibFile> {
    let option_name = option_name.trim();
    if option_name.is_empty() {
      return None;
    }
    let filename = format!("lib.{}.d.ts", option_name.to_ascii_lowercase());
    lib_file_by_filename(&filename)
  }

  fn lib_file_by_filename(filename: &str) -> Option<LibFile> {
    bundled_lib_text(filename).map(|text| LibFile {
      key: FileKey::new(format!("lib:{filename}")),
      name: Arc::from(filename),
      kind: FileKind::Dts,
      text: Arc::from(text),
    })
  }

  pub fn load_bundled(lib_set: &LibSet) -> Vec<LibFile> {
    let mut required: BTreeSet<String> = BTreeSet::new();
    let mut queue: VecDeque<String> = VecDeque::new();

    for name in lib_set.libs() {
      let file = name.file_name();
      if required.insert(file.clone()) {
        queue.push_back(file);
      }
    }

    while let Some(file) = queue.pop_front() {
      let text = bundled_lib_text_or_panic(&file);
      for dep in referenced_libs(text).into_iter() {
        if required.insert(dep.clone()) {
          queue.push_back(dep);
        }
      }
    }

    required
      .into_iter()
      .map(|filename| {
        lib_file_by_filename(&filename)
          .unwrap_or_else(|| panic!("missing bundled TypeScript lib '{filename}'"))
      })
      .collect()
  }

  mod generated {
    include!(concat!(env!("OUT_DIR"), "/typescript_libs_generated.rs"));
  }

  // Ensure the build-script generated `TYPESCRIPT_VERSION` constant is treated as used
  // so it does not trigger `dead_code` warnings in downstream builds.
  const _: &str = generated::TYPESCRIPT_VERSION;

  fn bundled_lib_text(filename: &str) -> Option<&'static str> {
    match generated::LIBS.binary_search_by(|(name, _)| name.cmp(&filename)) {
      Ok(idx) => Some(generated::LIBS[idx].1),
      Err(_) => None,
    }
  }

  fn bundled_lib_text_or_panic(filename: &str) -> &'static str {
    bundled_lib_text(filename).unwrap_or_else(|| panic!("missing bundled TypeScript lib '{filename}'"))
  }

  fn referenced_libs(text: &str) -> Vec<String> {
    fn attr_value<'a>(line: &'a str, needle: &str) -> Option<&'a str> {
      let mut offset = 0;
      while let Some(found) = line[offset..].find(needle) {
        let start = offset + found;
        // Avoid matching `no-default-lib="true"` as `lib="true"` by requiring
        // the attribute name be preceded by whitespace.
        if start == 0 || line.as_bytes()[start - 1].is_ascii_whitespace() {
          let value_start = start + needle.len();
          let rest = &line[value_start..];
          let end = rest.find('"')?;
          return Some(&rest[..end]);
        }
        offset = start + needle.len();
      }
      None
    }

    let mut out = Vec::new();
    let mut in_directives = false;
    for line in text.lines() {
      let line = line.trim();
      if line.is_empty() {
        continue;
      }
      if !line.starts_with("///") {
        if in_directives {
          break;
        }
        continue;
      }
      in_directives = true;

      if let Some(lib_name) = attr_value(line, "lib=\"") {
        out.push(format!("lib.{lib_name}.d.ts"));
      }

      if let Some(path) = attr_value(line, "path=\"") {
        let filename = path.rsplit('/').next().unwrap_or(path);
        if filename.starts_with("lib.") && filename.ends_with(".d.ts") {
          out.push(filename.to_string());
        }
      }
    }
    out
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
