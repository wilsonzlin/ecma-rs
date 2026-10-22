//! Helpers for selecting and loading TypeScript lib declaration files.
//!
//! This module exposes lib selection and loading utilities used by the main
//! checker. Bundled libs are chosen based on [`CompilerOptions`] and can be
//! cached via [`LibManager`].

mod compiler_options;
pub mod lib_env;

pub use compiler_options::{
  CacheMode, CacheOptions, CompilerOptions, JsxMode, LibName, LibSet, ModuleKind, ScriptTarget,
};
pub use lib_env::{LibManager, LoadedLibs};
pub use types_ts_interned::TypeOptions;

use std::sync::Arc;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::FileKey;

/// Kinds of supported files.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FileKind {
  Js,
  Ts,
  Tsx,
  Jsx,
  Dts,
}

/// Infer a [`FileKind`] from a virtual path (extension-based).
///
/// Paths may be TypeScript-style (`/a.ts`, `dir/file.tsx`) or plain names
/// (`entry.js`). Module-suffixed extensions (`.mts`/`.cts`/`.mjs`/`.cjs`) map
/// to the closest supported kind.
pub fn infer_file_kind(path: &str) -> FileKind {
  let ends_with = |suffix: &str| {
    path.len() >= suffix.len()
      && path.as_bytes()[path.len() - suffix.len()..].eq_ignore_ascii_case(suffix.as_bytes())
  };

  if ends_with(".d.ts") || ends_with(".d.mts") || ends_with(".d.cts") {
    return FileKind::Dts;
  }
  if ends_with(".tsx") {
    return FileKind::Tsx;
  }
  if ends_with(".ts") {
    return FileKind::Ts;
  }
  if ends_with(".jsx") {
    return FileKind::Jsx;
  }
  if ends_with(".js") {
    return FileKind::Js;
  }
  if ends_with(".mts") || ends_with(".cts") {
    return FileKind::Ts;
  }
  if ends_with(".mjs") || ends_with(".cjs") {
    return FileKind::Js;
  }

  FileKind::Ts
}

/// A library file that can be loaded before user source files.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibFile {
  pub key: FileKey,
  pub name: Arc<str>,
  pub kind: FileKind,
  pub text: Arc<str>,
}
