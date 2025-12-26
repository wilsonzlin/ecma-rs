//! Helpers for selecting and loading TypeScript lib declaration files.
//!
//! This module exposes lib selection and loading utilities used by the main
//! checker. Bundled libs are chosen based on [`CompilerOptions`] and can be
//! cached via [`LibManager`].

mod compiler_options;
pub mod lib_env;

pub use compiler_options::{CompilerOptions, JsxMode, LibName, LibSet, ModuleKind, ScriptTarget};
pub use lib_env::{LibManager, LoadedLibs};
pub use types_ts_interned::TypeOptions;

use std::sync::Arc;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::FileId;

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

/// A library file that can be loaded before user source files.
#[derive(Clone, Debug)]
pub struct LibFile {
  pub id: FileId,
  pub name: Arc<str>,
  pub kind: FileKind,
  pub text: Arc<str>,
}
