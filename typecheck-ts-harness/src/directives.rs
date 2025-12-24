use serde::Deserialize;
use serde::Serialize;

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
        "noimplicitany" => options.no_implicit_any = parse_bool(value),
        "strictnullchecks" => options.strict_null_checks = parse_bool(value),
        "lib" => options.lib = parse_list(value),
        "skiplibcheck" => options.skip_lib_check = parse_bool(value),
        "noemit" => options.no_emit = parse_bool(value),
        "usedefineforclassfields" => options.use_define_for_class_fields = parse_bool(value),
        "noemitonerror" => options.no_emit_on_error = parse_bool(value),
        "declaration" => options.declaration = parse_bool(value),
        "moduleresolution" => options.module_resolution = value.map(str::to_string),
        "types" => options.types = parse_list(value),
        _ => {}
      }
    }

    options
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
}
