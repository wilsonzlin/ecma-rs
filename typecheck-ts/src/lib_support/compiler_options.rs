use std::fmt;

/// Target language level.
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum JsxMode {
  Preserve,
  React,
  ReactJsx,
  ReactJsxdev,
}

impl Default for ScriptTarget {
  fn default() -> Self {
    ScriptTarget::Es2015
  }
}

/// Compiler configuration that materially affects lib selection and typing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompilerOptions {
  pub target: ScriptTarget,
  /// Whether DOM libs should be included in addition to the ES lib set.
  pub include_dom: bool,
  /// If true, do not automatically include default libs.
  pub no_default_lib: bool,
  /// Explicit lib overrides (when non-empty this replaces the default target-derived set).
  pub libs: Vec<LibName>,
  pub strict_null_checks: bool,
  pub no_implicit_any: bool,
  pub strict_function_types: bool,
  pub exact_optional_property_types: bool,
  pub no_unchecked_indexed_access: bool,
  pub use_define_for_class_fields: bool,
  pub jsx: Option<JsxMode>,
}

impl Default for CompilerOptions {
  fn default() -> Self {
    CompilerOptions {
      target: ScriptTarget::default(),
      include_dom: false,
      no_default_lib: false,
      libs: Vec::new(),
      strict_null_checks: true,
      no_implicit_any: false,
      strict_function_types: true,
      exact_optional_property_types: false,
      no_unchecked_indexed_access: false,
      use_define_for_class_fields: true,
      jsx: None,
    }
  }
}

/// Named libraries that can be loaded.
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
}

/// Ordered set of libs to load.
#[derive(Clone, Debug, PartialEq, Eq)]
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
