use serde::{Deserialize, Serialize};
use std::fmt;

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
  /// Whether DOM libs should be included in addition to the ES lib set.
  pub include_dom: bool,
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
      include_dom: true,
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
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LibName {
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
  Dom,
}

impl LibName {
  pub fn as_str(&self) -> &'static str {
    match self {
      LibName::Es5 => "lib.es5.d.ts",
      LibName::Es2015 => "lib.es2015.d.ts",
      LibName::Es2016 => "lib.es2016.d.ts",
      LibName::Es2017 => "lib.es2017.d.ts",
      LibName::Es2018 => "lib.es2018.d.ts",
      LibName::Es2019 => "lib.es2019.d.ts",
      LibName::Es2020 => "lib.es2020.d.ts",
      LibName::Es2021 => "lib.es2021.d.ts",
      LibName::Es2022 => "lib.es2022.d.ts",
      LibName::EsNext => "lib.esnext.d.ts",
      LibName::Dom => "lib.dom.d.ts",
    }
  }

  pub fn option_name(&self) -> &'static str {
    match self {
      LibName::Es5 => "es5",
      LibName::Es2015 => "es2015",
      LibName::Es2016 => "es2016",
      LibName::Es2017 => "es2017",
      LibName::Es2018 => "es2018",
      LibName::Es2019 => "es2019",
      LibName::Es2020 => "es2020",
      LibName::Es2021 => "es2021",
      LibName::Es2022 => "es2022",
      LibName::EsNext => "esnext",
      LibName::Dom => "dom",
    }
  }
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
    if options.no_default_lib {
      return LibSet::from(options.libs.clone());
    }

    if !options.libs.is_empty() {
      return LibSet::from(options.libs.clone());
    }

    let mut libs = vec![es_lib_for_target(options.target)];
    if options.include_dom && !libs.contains(&LibName::Dom) {
      libs.push(LibName::Dom);
    }
    LibSet { libs }
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
    LibSet { libs }
  }
}

fn es_lib_for_target(target: ScriptTarget) -> LibName {
  match target {
    ScriptTarget::Es3 | ScriptTarget::Es5 => LibName::Es5,
    ScriptTarget::Es2015 => LibName::Es2015,
    ScriptTarget::Es2016 => LibName::Es2016,
    ScriptTarget::Es2017 => LibName::Es2017,
    ScriptTarget::Es2018 => LibName::Es2018,
    ScriptTarget::Es2019 => LibName::Es2019,
    ScriptTarget::Es2020 => LibName::Es2020,
    ScriptTarget::Es2021 => LibName::Es2021,
    ScriptTarget::Es2022 => LibName::Es2022,
    ScriptTarget::EsNext => LibName::EsNext,
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
