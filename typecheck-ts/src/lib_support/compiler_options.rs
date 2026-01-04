use serde::{Deserialize, Serialize};
use std::{fmt, sync::Arc};

use types_ts_interned::CacheConfig;

/// Target language level.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ScriptTarget {
  Es3,
  Es5,
  Es2015,
  Es2016,
  Es2017,
  Es2018,
  Es2019,
  Es2020,
  Es2021,
  Es2022,
  EsNext,
}

/// JSX transform mode.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum JsxMode {
  Preserve,
  React,
  ReactJsx,
  ReactJsxdev,
}

/// Module system to emit/parse.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ModuleKind {
  None,
  CommonJs,
  Es2015,
  Es2020,
  Es2022,
  EsNext,
  Umd,
  Amd,
  System,
  Node16,
  NodeNext,
}

impl ModuleKind {
  pub fn option_name(&self) -> &'static str {
    match self {
      ModuleKind::None => "None",
      ModuleKind::CommonJs => "CommonJS",
      ModuleKind::Es2015 => "ES2015",
      ModuleKind::Es2020 => "ES2020",
      ModuleKind::Es2022 => "ES2022",
      ModuleKind::EsNext => "ESNext",
      ModuleKind::Umd => "UMD",
      ModuleKind::Amd => "AMD",
      ModuleKind::System => "System",
      ModuleKind::Node16 => "Node16",
      ModuleKind::NodeNext => "NodeNext",
    }
  }
}

impl Default for ScriptTarget {
  fn default() -> Self {
    ScriptTarget::Es2015
  }
}

/// Compiler configuration that materially affects lib selection and typing.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CompilerOptions {
  pub target: ScriptTarget,
  pub module: Option<ModuleKind>,
  /// If true, do not automatically include default libs.
  pub no_default_lib: bool,
  /// Explicit lib overrides (when non-empty this replaces the default target-derived set).
  pub libs: Vec<LibName>,
  /// Whether to skip checking bundled and host-provided libs.
  pub skip_lib_check: bool,
  /// Whether to suppress emit; the checker never emits today, but we keep the flag for parity.
  pub no_emit: bool,
  /// Whether to suppress emit on error; unused for now but tracked for fidelity.
  pub no_emit_on_error: bool,
  /// Whether to produce declaration outputs; unused in the checker but surfaced for completeness.
  pub declaration: bool,
  /// Module resolution strategy as provided by the host (raw, lower-cased string).
  pub module_resolution: Option<String>,
  /// Explicitly included `@types` packages.
  pub types: Vec<String>,
  pub strict_null_checks: bool,
  pub no_implicit_any: bool,
  pub strict_function_types: bool,
  pub exact_optional_property_types: bool,
  pub no_unchecked_indexed_access: bool,
  /// Whether class fields follow ECMAScript `define` semantics (`Object.defineProperty`)
  /// or legacy assignment semantics.
  ///
  /// The checker uses this option when diagnosing `this.x` reads inside class
  /// field initializers:
  /// - When targeting native class fields (ES2022/ESNext) and `useDefineForClassFields`
  ///   is enabled, reading a constructor parameter property (e.g.
  ///   `constructor(public x: number)`) from a field initializer reports `TS2729`.
  /// - When `useDefineForClassFields` is disabled (assignment semantics),
  ///   `TS2729` is suppressed if the property exists on a base class, matching
  ///   `tsc`'s behavior.
  pub use_define_for_class_fields: bool,
  pub jsx: Option<JsxMode>,
  /// Cache sizing and sharing strategy for the checker.
  pub cache: CacheOptions,
}

impl Default for CompilerOptions {
  fn default() -> Self {
    CompilerOptions {
      target: ScriptTarget::default(),
      module: None,
      no_default_lib: false,
      libs: Vec::new(),
      skip_lib_check: true,
      no_emit: true,
      no_emit_on_error: false,
      declaration: false,
      module_resolution: None,
      types: Vec::new(),
      strict_null_checks: true,
      no_implicit_any: false,
      strict_function_types: true,
      exact_optional_property_types: false,
      no_unchecked_indexed_access: false,
      use_define_for_class_fields: true,
      jsx: None,
      cache: CacheOptions::default(),
    }
  }
}

/// Strategy for sharing caches across bodies/files.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CacheMode {
  /// Reuse the same caches across bodies for maximal hit rates.
  Shared,
  /// Create fresh caches for each body and drop them afterwards.
  PerBody,
}

/// Cache sizing controls exposed through the host.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CacheOptions {
  pub max_relation_cache_entries: usize,
  pub max_eval_cache_entries: usize,
  pub max_instantiation_cache_entries: usize,
  pub max_body_cache_entries: usize,
  pub max_def_cache_entries: usize,
  pub cache_shards: usize,
  pub mode: CacheMode,
}

impl CacheOptions {
  pub fn relation_config(&self) -> CacheConfig {
    CacheConfig {
      max_entries: self.max_relation_cache_entries,
      shard_count: self.cache_shards,
    }
  }

  pub fn eval_config(&self) -> CacheConfig {
    CacheConfig {
      max_entries: self.max_eval_cache_entries,
      shard_count: self.cache_shards,
    }
  }

  pub fn instantiation_config(&self) -> CacheConfig {
    CacheConfig {
      max_entries: self.max_instantiation_cache_entries,
      shard_count: self.cache_shards,
    }
  }

  pub fn body_config(&self) -> CacheConfig {
    CacheConfig {
      max_entries: self.max_body_cache_entries,
      shard_count: self.cache_shards,
    }
  }

  pub fn def_config(&self) -> CacheConfig {
    CacheConfig {
      max_entries: self.max_def_cache_entries,
      shard_count: self.cache_shards,
    }
  }
}

impl Default for CacheOptions {
  fn default() -> Self {
    Self {
      max_relation_cache_entries: CacheConfig::default().max_entries,
      max_eval_cache_entries: CacheConfig::default().max_entries,
      max_instantiation_cache_entries: CacheConfig::default().max_entries / 2,
      max_body_cache_entries: CacheConfig::default().max_entries,
      max_def_cache_entries: CacheConfig::default().max_entries,
      cache_shards: CacheConfig::default().shard_count,
      mode: CacheMode::Shared,
    }
  }
}

/// Named libraries that can be loaded.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct LibName(Arc<str>);

impl LibName {
  /// Parse a TypeScript lib name from the `--lib` / `compilerOptions.lib` model.
  ///
  /// Accepts the canonical names (e.g. `es2020`, `dom.iterable`), common case
  /// variants (e.g. `ES2020`), and the filename form (e.g. `lib.es2020.d.ts`).
  ///
  /// Returns `None` when the string cannot represent a TS lib name.
  pub fn parse(raw: &str) -> Option<Self> {
    canonicalize_lib_name(raw).map(|name| LibName(Arc::from(name)))
  }

  /// Parse a lib name from TypeScript-style option strings (e.g. `dom`, `es2020`,
  /// `esnext.disposable`). This is a small compatibility shim used by features
  /// like `/// <reference lib="..." />`.
  pub fn from_option_name(raw: &str) -> Option<Self> {
    LibName::parse(raw)
  }

  /// Canonical lib name used by TypeScript (lower-cased, no `lib.` / `.d.ts`).
  pub fn as_str(&self) -> &str {
    &self.0
  }

  /// Filename used by the TypeScript lib bundle (`lib.<name>.d.ts`).
  pub fn file_name(&self) -> String {
    format!("lib.{}.d.ts", self.as_str())
  }
}

impl fmt::Display for LibName {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str(self.as_str())
  }
}

fn canonicalize_lib_name(raw: &str) -> Option<String> {
  let trimmed = raw.trim();
  if trimmed.is_empty() {
    return None;
  }

  // TypeScript treats lib names case-insensitively.
  let mut normalized = trimmed.to_ascii_lowercase();

  // Permit passing file names/paths (`lib.es2020.d.ts` or `.../lib.es2020.d.ts`).
  if let Some((_, tail)) = normalized.rsplit_once(['/', '\\']) {
    normalized = tail.to_string();
  }

  normalized = normalized.trim_start_matches("lib.").to_string();
  normalized = normalized
    .trim_end_matches(".d.ts")
    .trim_end_matches(".ts")
    .to_string();

  // `--lib es6` is an alias for `es2015`.
  if normalized == "es6" {
    normalized = "es2015".to_string();
  }

  if normalized.is_empty() {
    return None;
  }

  // TypeScript lib names are dot-separated ASCII identifiers.
  if !normalized
    .chars()
    .all(|ch| ch.is_ascii_lowercase() || ch.is_ascii_digit() || ch == '.')
  {
    return None;
  }

  Some(normalized)
}

/// Ordered set of libs to load.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LibSet {
  libs: Vec<LibName>,
}

impl LibSet {
  pub fn empty() -> Self {
    LibSet { libs: Vec::new() }
  }

  /// Compute the default lib set for a given compiler configuration.
  pub fn for_options(options: &CompilerOptions) -> Self {
    if !options.libs.is_empty() {
      return LibSet::from(options.libs.clone());
    }

    if options.no_default_lib {
      return LibSet::empty();
    }

    let mut libs = vec![es_lib_for_target(options.target), lib_name("dom")];
    if matches!(options.target, ScriptTarget::EsNext) {
      libs.push(lib_name("esnext.disposable"));
    }
    LibSet::from(libs)
  }

  pub fn libs(&self) -> &[LibName] {
    &self.libs
  }
}

impl fmt::Display for LibSet {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let names: Vec<_> = self.libs.iter().map(|l| l.as_str()).collect();
    write!(f, "{}", names.join(", "))
  }
}

impl From<Vec<LibName>> for LibSet {
  fn from(libs: Vec<LibName>) -> Self {
    let mut libs = libs;
    libs.sort();
    libs.dedup();
    LibSet { libs }
  }
}

fn es_lib_for_target(target: ScriptTarget) -> LibName {
  match target {
    ScriptTarget::Es3 | ScriptTarget::Es5 => lib_name("es5"),
    ScriptTarget::Es2015 => lib_name("es2015"),
    ScriptTarget::Es2016 => lib_name("es2016"),
    ScriptTarget::Es2017 => lib_name("es2017"),
    ScriptTarget::Es2018 => lib_name("es2018"),
    ScriptTarget::Es2019 => lib_name("es2019"),
    ScriptTarget::Es2020 => lib_name("es2020"),
    ScriptTarget::Es2021 => lib_name("es2021"),
    ScriptTarget::Es2022 => lib_name("es2022"),
    ScriptTarget::EsNext => lib_name("esnext"),
  }
}

fn lib_name(name: &'static str) -> LibName {
  LibName(Arc::from(name))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn canonicalizes_lib_names() {
    let cases = [
      ("es2020", "es2020"),
      ("ES2020", "es2020"),
      ("lib.es2020.d.ts", "es2020"),
      ("lib.es2020.ts", "es2020"),
      ("dom.iterable", "dom.iterable"),
      ("LIB.DOM.ITERABLE.D.TS", "dom.iterable"),
      ("esnext.disposable", "esnext.disposable"),
      ("lib.esnext.disposable.d.ts", "esnext.disposable"),
      ("es6", "es2015"),
      ("lib.es6.d.ts", "es2015"),
      ("path/to/lib.es2020.d.ts", "es2020"),
      ("path\\to\\lib.es2020.d.ts", "es2020"),
    ];

    for (raw, expected) in cases {
      let parsed = LibName::parse(raw).unwrap_or_else(|| panic!("expected parse for {raw}"));
      assert_eq!(parsed.as_str(), expected);
    }

    assert!(LibName::parse("").is_none());
    assert!(LibName::parse("lib.").is_none());
    assert!(LibName::parse("es2020+dom").is_none());
  }

  #[test]
  fn computes_default_libs_from_target() {
    let mut options = CompilerOptions::default();
    options.target = ScriptTarget::Es2020;
    let libs = LibSet::for_options(&options);
    assert_eq!(
      libs.libs(),
      &[lib_name("dom"), lib_name("es2020")],
      "default libs should include target ES lib plus dom"
    );

    let mut options = CompilerOptions::default();
    options.target = ScriptTarget::Es3;
    let libs = LibSet::for_options(&options);
    assert_eq!(libs.libs(), &[lib_name("dom"), lib_name("es5")]);

    let mut options = CompilerOptions::default();
    options.target = ScriptTarget::EsNext;
    let libs = LibSet::for_options(&options);
    assert_eq!(
      libs.libs(),
      &[
        lib_name("dom"),
        lib_name("esnext"),
        lib_name("esnext.disposable")
      ],
      "esnext defaults should include esnext.disposable for using/await using support"
    );

    let mut options = CompilerOptions::default();
    options.no_default_lib = true;
    let libs = LibSet::for_options(&options);
    assert!(libs.libs().is_empty());

    let mut options = CompilerOptions::default();
    options.no_default_lib = true;
    options.libs = vec![LibName::parse("es2015.promise").unwrap()];
    let libs = LibSet::for_options(&options);
    assert_eq!(libs.libs(), &[LibName::parse("es2015.promise").unwrap()]);
  }
}

impl From<&CompilerOptions> for types_ts_interned::TypeOptions {
  fn from(options: &CompilerOptions) -> Self {
    types_ts_interned::TypeOptions {
      strict_null_checks: options.strict_null_checks,
      strict_function_types: options.strict_function_types,
      exact_optional_property_types: options.exact_optional_property_types,
      no_unchecked_indexed_access: options.no_unchecked_indexed_access,
    }
  }
}
