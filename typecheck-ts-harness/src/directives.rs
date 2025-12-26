use crate::tsc::apply_default_tsc_options;
use serde::Deserialize;
use serde::Serialize;
use serde_json::{Map, Value};
use typecheck_ts::lib_support::{CompilerOptions, JsxMode, LibName, ModuleKind, ScriptTarget};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DirectiveSource {
  Line,
  Block,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HarnessDirective {
  /// Canonical, lower-cased directive name (e.g. `filename`, `module`, `target`).
  pub name: String,
  /// Raw value after the colon, trimmed; `None` if omitted or empty.
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub value: Option<String>,
  /// Whether the directive came from a line or block comment.
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub source: Option<DirectiveSource>,
  /// 1-based line number within the original harness file.
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub line: Option<usize>,
}

/// Parse a harness directive from a single line of text.
///
/// Recognizes both line comments (`// @name: value`) and block comments
/// (`/* @name: value */`). Leading whitespace is ignored. The directive name is
/// lower-cased; the value is trimmed and returned as-is (or `None` if missing).
pub fn parse_directive(raw_line: &str, line_number: usize) -> Option<HarnessDirective> {
  parse_line_comment(raw_line, line_number).or_else(|| parse_block_comment(raw_line, line_number))
}

fn parse_line_comment(raw_line: &str, line_number: usize) -> Option<HarnessDirective> {
  let trimmed = raw_line.trim_start();
  if !trimmed.starts_with("//") {
    return None;
  }

  let content = trimmed.trim_start_matches('/').trim_start();
  parse_directive_content(content, DirectiveSource::Line, line_number)
}

fn parse_block_comment(raw_line: &str, line_number: usize) -> Option<HarnessDirective> {
  let trimmed = raw_line.trim_start();
  if !trimmed.starts_with("/*") {
    return None;
  }

  let mut content = trimmed.trim_start_matches("/*").trim_start();
  if let Some(stripped) = content.strip_suffix("*/") {
    content = stripped.trim_end();
  }

  parse_directive_content(content, DirectiveSource::Block, line_number)
}

fn parse_directive_content(
  content: &str,
  source: DirectiveSource,
  line_number: usize,
) -> Option<HarnessDirective> {
  let content = content.trim_start();
  if !content.starts_with('@') {
    return None;
  }

  // Require the `@name: value` shape to avoid accidentally treating other @tags
  // (like `@ts-ignore`) as harness directives.
  let colon_index = content.find(':')?;
  let (raw_name, raw_value) = content.split_at(colon_index);

  let name = raw_name.trim_start_matches('@').trim();
  if name.is_empty() {
    return None;
  }
  if !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
    return None;
  }

  let value = raw_value.trim_start_matches(':').trim();
  let value = if value.is_empty() {
    None
  } else {
    Some(value.to_string())
  };

  Some(HarnessDirective {
    name: name.to_ascii_lowercase(),
    value,
    source: Some(source),
    line: Some(line_number),
  })
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub struct HarnessOptions {
  #[serde(skip_serializing_if = "Option::is_none")]
  pub target: Option<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub module: Option<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub jsx: Option<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub strict: Option<bool>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub no_implicit_any: Option<bool>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub strict_null_checks: Option<bool>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub strict_function_types: Option<bool>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub exact_optional_property_types: Option<bool>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub no_unchecked_indexed_access: Option<bool>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub no_lib: Option<bool>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub lib: Vec<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub skip_lib_check: Option<bool>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub no_emit: Option<bool>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub use_define_for_class_fields: Option<bool>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub no_emit_on_error: Option<bool>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub declaration: Option<bool>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub module_resolution: Option<String>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub types: Vec<String>,
}

impl HarnessOptions {
  pub fn from_directives(directives: &[HarnessDirective]) -> HarnessOptions {
    let mut options = HarnessOptions::default();
    for directive in directives {
      let value = directive.value.as_deref();
      match directive.name.as_str() {
        "target" => options.target = value.map(str::to_string),
        "module" => options.module = value.map(str::to_string),
        "jsx" => options.jsx = value.map(str::to_string),
        "strict" => options.strict = parse_bool(value),
        "strictfunctiontypes" => options.strict_function_types = parse_bool(value),
        "noimplicitany" => options.no_implicit_any = parse_bool(value),
        "strictnullchecks" => options.strict_null_checks = parse_bool(value),
        "exactoptionalpropertytypes" => options.exact_optional_property_types = parse_bool(value),
        "nouncheckedindexedaccess" => options.no_unchecked_indexed_access = parse_bool(value),
        "nolib" => options.no_lib = parse_bool(value),
        "lib" => options.lib = parse_list(value),
        "skiplibcheck" => options.skip_lib_check = parse_bool(value),
        "noemit" => options.no_emit = parse_bool(value),
        "usedefineforclassfields" => options.use_define_for_class_fields = parse_bool(value),
        "noemitonerror" => options.no_emit_on_error = parse_bool(value),
        "declaration" => options.declaration = parse_bool(value),
        "moduleresolution" => {
          options.module_resolution = value.map(|v| v.trim().to_ascii_lowercase())
        }
        "types" => options.types = parse_list(value),
        _ => {}
      }
    }

    options
  }

  /// Convert parsed harness options to `typecheck-ts` compiler options.
  pub fn to_compiler_options(&self) -> CompilerOptions {
    let mut opts = CompilerOptions::default();

    if let Some(target) = self
      .target
      .as_deref()
      .and_then(|raw| parse_script_target(raw))
    {
      opts.target = target;
    }

    if let Some(module) = self
      .module
      .as_deref()
      .and_then(|raw| parse_module_kind(raw))
    {
      opts.module = Some(module);
    }

    if let Some(strict) = self.strict {
      opts.strict_null_checks = strict;
      opts.no_implicit_any = strict;
      opts.strict_function_types = strict;
    }
    if let Some(value) = self.no_implicit_any {
      opts.no_implicit_any = value;
    }
    if let Some(value) = self.strict_null_checks {
      opts.strict_null_checks = value;
    }
    if let Some(value) = self.strict_function_types {
      opts.strict_function_types = value;
    }
    if let Some(value) = self.exact_optional_property_types {
      opts.exact_optional_property_types = value;
    }
    if let Some(value) = self.no_unchecked_indexed_access {
      opts.no_unchecked_indexed_access = value;
    }
    if let Some(value) = self.use_define_for_class_fields {
      opts.use_define_for_class_fields = value;
    }
    if let Some(value) = self.skip_lib_check {
      opts.skip_lib_check = value;
    }
    if let Some(value) = self.no_emit {
      opts.no_emit = value;
    }
    if let Some(value) = self.no_emit_on_error {
      opts.no_emit_on_error = value;
    }
    if let Some(value) = self.declaration {
      opts.declaration = value;
    }
    if let Some(value) = self.module_resolution.as_ref() {
      opts.module_resolution = Some(value.clone());
    }
    if !self.types.is_empty() {
      opts.types = self.types.clone();
    }

    if let Some(mode) = self.jsx.as_deref().and_then(parse_jsx_mode) {
      opts.jsx = Some(mode);
    }

    let mut libs = Vec::new();
    for lib in &self.lib {
      if let Some(parsed) = parse_lib_name(lib) {
        libs.push(parsed);
      }
    }
    let no_lib = self.no_lib.unwrap_or(false);
    if !libs.is_empty() {
      opts.include_dom = libs.iter().any(|l| matches!(l, LibName::Dom));
      opts.libs = libs.clone();
      opts.no_default_lib = true;
    } else {
      opts.include_dom = !no_lib;
      opts.no_default_lib |= no_lib;
    }

    opts
  }

  /// Serialize options for the Node-based `tsc` wrapper.
  pub fn to_env_json(&self) -> Option<String> {
    let map = self.to_tsc_options_map();
    if map.is_empty() {
      None
    } else {
      serde_json::to_string(&map).ok()
    }
  }

  pub(crate) fn to_tsc_options_map(&self) -> Map<String, Value> {
    let mut map = Map::new();
    apply_default_tsc_options(&mut map);

    let compiler = self.to_compiler_options();
    map.insert(
      "target".to_string(),
      Value::String(script_target_str(compiler.target).to_string()),
    );
    map.insert(
      "noImplicitAny".to_string(),
      Value::Bool(compiler.no_implicit_any),
    );
    map.insert(
      "strictNullChecks".to_string(),
      Value::Bool(compiler.strict_null_checks),
    );
    map.insert(
      "strictFunctionTypes".to_string(),
      Value::Bool(compiler.strict_function_types),
    );
    map.insert(
      "exactOptionalPropertyTypes".to_string(),
      Value::Bool(compiler.exact_optional_property_types),
    );
    map.insert(
      "noUncheckedIndexedAccess".to_string(),
      Value::Bool(compiler.no_unchecked_indexed_access),
    );
    map.insert(
      "useDefineForClassFields".to_string(),
      Value::Bool(compiler.use_define_for_class_fields),
    );
    if let Some(value) = self.no_lib {
      map.insert("noLib".to_string(), Value::Bool(value));
    }

    if let Some(strict) = self.strict {
      map.insert("strict".to_string(), Value::Bool(strict));
    }

    if let Some(module) = compiler.module {
      map.insert(
        "module".to_string(),
        Value::String(module.option_name().to_string()),
      );
    } else if let Some(module) = &self.module {
      map.insert("module".to_string(), Value::String(module.clone()));
    }
    if let Some(mode) = compiler.jsx {
      map.insert(
        "jsx".to_string(),
        Value::String(jsx_mode_str(mode).to_string()),
      );
    } else if let Some(raw) = &self.jsx {
      map.insert("jsx".to_string(), Value::String(raw.clone()));
    }

    if !self.lib.is_empty() {
      let libs: Vec<String> = if compiler.libs.is_empty() {
        self.lib.clone()
      } else {
        compiler
          .libs
          .iter()
          .map(|lib| lib.option_name().to_string())
          .collect()
      };
      map.insert(
        "lib".to_string(),
        Value::Array(libs.into_iter().map(Value::String).collect()),
      );
    }
    if let Some(value) = self.skip_lib_check {
      map.insert("skipLibCheck".to_string(), Value::Bool(value));
    }
    if let Some(value) = self.no_emit {
      map.insert("noEmit".to_string(), Value::Bool(value));
    }
    if let Some(value) = self.no_emit_on_error {
      map.insert("noEmitOnError".to_string(), Value::Bool(value));
    }
    if let Some(value) = self.declaration {
      map.insert("declaration".to_string(), Value::Bool(value));
    }
    if let Some(value) = self.module_resolution.as_ref() {
      map.insert("moduleResolution".to_string(), Value::String(value.clone()));
    }
    if !self.types.is_empty() {
      map.insert(
        "types".to_string(),
        Value::Array(self.types.iter().cloned().map(Value::String).collect()),
      );
    }

    map
  }
}

fn parse_bool(raw: Option<&str>) -> Option<bool> {
  match raw.map(|s| s.trim().to_ascii_lowercase()) {
    None => Some(true),
    Some(value) if value.is_empty() => Some(true),
    Some(value) if matches!(value.as_str(), "true" | "1" | "yes" | "on") => Some(true),
    Some(value) if matches!(value.as_str(), "false" | "0" | "no" | "off") => Some(false),
    _ => None,
  }
}

fn parse_list(raw: Option<&str>) -> Vec<String> {
  let Some(raw) = raw else {
    return Vec::new();
  };

  raw
    .split(|c| c == ',' || c == ' ' || c == '\t')
    .map(str::trim)
    .filter(|s| !s.is_empty())
    .map(|s| s.to_string())
    .collect()
}

fn parse_script_target(raw: &str) -> Option<ScriptTarget> {
  match raw.trim().to_ascii_lowercase().as_str() {
    "es3" => Some(ScriptTarget::Es3),
    "es5" => Some(ScriptTarget::Es5),
    "es2015" => Some(ScriptTarget::Es2015),
    "es2016" => Some(ScriptTarget::Es2016),
    "es2017" => Some(ScriptTarget::Es2017),
    "es2018" => Some(ScriptTarget::Es2018),
    "es2019" => Some(ScriptTarget::Es2019),
    "es2020" => Some(ScriptTarget::Es2020),
    "es2021" => Some(ScriptTarget::Es2021),
    "es2022" => Some(ScriptTarget::Es2022),
    "esnext" => Some(ScriptTarget::EsNext),
    _ => None,
  }
}

fn script_target_str(target: ScriptTarget) -> &'static str {
  match target {
    ScriptTarget::Es3 => "ES3",
    ScriptTarget::Es5 => "ES5",
    ScriptTarget::Es2015 => "ES2015",
    ScriptTarget::Es2016 => "ES2016",
    ScriptTarget::Es2017 => "ES2017",
    ScriptTarget::Es2018 => "ES2018",
    ScriptTarget::Es2019 => "ES2019",
    ScriptTarget::Es2020 => "ES2020",
    ScriptTarget::Es2021 => "ES2021",
    ScriptTarget::Es2022 => "ES2022",
    ScriptTarget::EsNext => "ESNext",
  }
}

fn parse_jsx_mode(raw: &str) -> Option<JsxMode> {
  match raw.trim().to_ascii_lowercase().as_str() {
    "preserve" => Some(JsxMode::Preserve),
    "react" => Some(JsxMode::React),
    "react-jsx" => Some(JsxMode::ReactJsx),
    "react-jsxdev" => Some(JsxMode::ReactJsxdev),
    _ => None,
  }
}

fn jsx_mode_str(mode: JsxMode) -> &'static str {
  match mode {
    JsxMode::Preserve => "preserve",
    JsxMode::React => "react",
    JsxMode::ReactJsx => "react-jsx",
    JsxMode::ReactJsxdev => "react-jsxdev",
  }
}

fn parse_module_kind(raw: &str) -> Option<ModuleKind> {
  match raw.trim().to_ascii_lowercase().as_str() {
    "none" => Some(ModuleKind::None),
    "commonjs" => Some(ModuleKind::CommonJs),
    "amd" => Some(ModuleKind::Amd),
    "system" => Some(ModuleKind::System),
    "umd" => Some(ModuleKind::Umd),
    "es6" | "es2015" => Some(ModuleKind::Es2015),
    "es2020" => Some(ModuleKind::Es2020),
    "es2022" => Some(ModuleKind::Es2022),
    "esnext" => Some(ModuleKind::EsNext),
    "node16" => Some(ModuleKind::Node16),
    "nodenext" => Some(ModuleKind::NodeNext),
    _ => None,
  }
}

fn parse_lib_name(raw: &str) -> Option<LibName> {
  match raw.trim().to_ascii_lowercase().as_str() {
    "es5" => Some(LibName::Es5),
    "es2015" => Some(LibName::Es2015),
    "es2016" => Some(LibName::Es2016),
    "es2017" => Some(LibName::Es2017),
    "es2018" => Some(LibName::Es2018),
    "es2019" => Some(LibName::Es2019),
    "es2020" => Some(LibName::Es2020),
    "es2021" => Some(LibName::Es2021),
    "es2022" => Some(LibName::Es2022),
    "esnext" => Some(LibName::EsNext),
    "dom" => Some(LibName::Dom),
    _ => None,
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn dir(name: &str, value: Option<&str>) -> HarnessDirective {
    HarnessDirective {
      name: name.to_string(),
      value: value.map(|v| v.to_string()),
      source: Some(DirectiveSource::Line),
      line: None,
    }
  }

  #[test]
  fn parses_line_comment_directive() {
    let directive = parse_directive("  //   @target: ES2022   ", 1).expect("directive");
    assert_eq!(directive.name, "target");
    assert_eq!(directive.value.as_deref(), Some("ES2022"));
    assert_eq!(directive.source, Some(DirectiveSource::Line));
    assert_eq!(directive.line, Some(1));
  }

  #[test]
  fn parses_block_comment_directive() {
    let directive = parse_directive("/* @module: CommonJS */", 4).expect("directive");
    assert_eq!(directive.name, "module");
    assert_eq!(directive.value.as_deref(), Some("CommonJS"));
    assert_eq!(directive.source, Some(DirectiveSource::Block));
    assert_eq!(directive.line, Some(4));
  }

  #[test]
  fn ignores_non_directives() {
    assert!(parse_directive("const x = 1; // not a directive", 1).is_none());
    assert!(parse_directive("// @ts-ignore: next line", 2).is_none());
    assert!(parse_directive("/* missing colon @foo */", 3).is_none());
  }

  #[test]
  fn builds_options_from_directives() {
    let directives = vec![
      dir("target", Some("ES5")),
      dir("strict", Some("false")),
      dir("strict", Some("true")),
      dir("lib", Some("dom,es2015")),
      dir("skiplibcheck", None),
    ];

    let options = HarnessOptions::from_directives(&directives);
    assert_eq!(options.target.as_deref(), Some("ES5"));
    assert_eq!(options.strict, Some(true));
    assert_eq!(options.lib, vec!["dom", "es2015"]);
    assert_eq!(options.skip_lib_check, Some(true));
  }

  #[test]
  fn duplicate_directives_last_one_wins() {
    let directives = vec![dir("module", Some("commonjs")), dir("module", Some("amd"))];
    let options = HarnessOptions::from_directives(&directives);
    assert_eq!(options.module.as_deref(), Some("amd"));
  }

  #[test]
  fn maps_directives_to_tsc_and_compiler_options() {
    let directives = vec![
      dir("target", Some("ES5")),
      dir("jsx", Some("react-jsx")),
      dir("strict", Some("true")),
      dir("noimplicitany", Some("false")),
      dir("module", Some("nodenext")),
      dir("lib", Some("dom es2015")),
    ];

    let options = HarnessOptions::from_directives(&directives);
    let tsc = options.to_tsc_options_map();

    assert_eq!(tsc.get("target"), Some(&Value::String("ES5".to_string())));
    assert_eq!(
      tsc.get("jsx"),
      Some(&Value::String("react-jsx".to_string()))
    );
    assert_eq!(tsc.get("strict"), Some(&Value::Bool(true)));
    assert_eq!(tsc.get("noImplicitAny"), Some(&Value::Bool(false)));
    assert_eq!(tsc.get("strictNullChecks"), Some(&Value::Bool(true)));
    assert_eq!(
      tsc.get("module"),
      Some(&Value::String("NodeNext".to_string()))
    );
    assert_eq!(
      tsc
        .get("lib")
        .and_then(|v| v.as_array())
        .map(|arr| arr.iter().filter_map(|v| v.as_str()).collect::<Vec<_>>()),
      Some(vec!["dom", "es2015"])
    );

    let compiler = options.to_compiler_options();
    assert_eq!(compiler.target, ScriptTarget::Es5);
    assert_eq!(compiler.jsx, Some(JsxMode::ReactJsx));
    assert_eq!(compiler.module, Some(ModuleKind::NodeNext));
    assert!(compiler.strict_function_types);
    assert!(!compiler.no_implicit_any);
    assert!(compiler.strict_null_checks);
    assert!(compiler.no_default_lib);
    assert_eq!(compiler.libs, vec![LibName::Dom, LibName::Es2015]);
  }

  #[test]
  fn normalizes_no_unchecked_indexed_access_name() {
    let directive =
      parse_directive("// @noUncheckedIndexedAccess: true", 1).expect("directive should parse");
    assert_eq!(directive.name, "nouncheckedindexedaccess");
  }

  #[test]
  fn maps_additional_directives_including_no_lib() {
    let directives = vec![
      dir("nolib", None),
      dir("lib", Some("es2020")),
      dir("types", Some("foo bar")),
      dir("declaration", None),
      dir("moduleresolution", Some("Node16")),
      dir("usedefineforclassfields", Some("false")),
    ];

    let options = HarnessOptions::from_directives(&directives);
    let tsc = options.to_tsc_options_map();
    let compiler = options.to_compiler_options();

    assert_eq!(compiler.libs, vec![LibName::Es2020]);
    assert!(compiler.no_default_lib);
    assert!(!compiler.include_dom);
    assert_eq!(compiler.types, vec!["foo".to_string(), "bar".to_string()]);
    assert_eq!(
      compiler.module_resolution.as_deref(),
      Some("node16"),
      "moduleResolution should be normalized"
    );
    assert!(!compiler.use_define_for_class_fields);
    assert_eq!(tsc.get("noLib"), Some(&Value::Bool(true)));
    assert_eq!(
      tsc
        .get("types")
        .and_then(|v| v.as_array())
        .map(|arr| arr.iter().filter_map(|v| v.as_str()).collect::<Vec<_>>()),
      Some(vec!["foo", "bar"])
    );
  }

  #[test]
  fn builds_default_tsc_options() {
    let options = HarnessOptions::default();
    let tsc = options.to_tsc_options_map();
    assert_eq!(tsc.get("noEmit"), Some(&Value::Bool(true)));
    assert_eq!(tsc.get("skipLibCheck"), Some(&Value::Bool(true)));
    assert_eq!(tsc.get("pretty"), Some(&Value::Bool(false)));
    assert_eq!(
      tsc.get("target"),
      Some(&Value::String("ES2015".to_string()))
    );
  }

  #[test]
  fn compiler_options_apply_strict_overrides() {
    let mut opts = HarnessOptions::default();
    opts.strict = Some(true);
    opts.strict_null_checks = Some(false);
    let compiler = opts.to_compiler_options();
    assert!(compiler.strict_function_types);
    assert!(compiler.no_implicit_any);
    assert!(!compiler.strict_null_checks);
  }
}
