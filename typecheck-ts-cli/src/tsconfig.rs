use globset::{Glob, GlobSet, GlobSetBuilder};
use serde::Deserialize;
use std::collections::{BTreeMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use typecheck_ts::lib_support::{CompilerOptions, JsxMode, LibName, ScriptTarget};
use walkdir::WalkDir;

#[derive(Debug, Clone)]
pub struct ProjectConfig {
  pub tsconfig_path: PathBuf,
  pub root_dir: PathBuf,
  pub compiler_options: CompilerOptions,
  pub base_url: Option<PathBuf>,
  pub paths: BTreeMap<String, Vec<String>>,
  pub root_files: Vec<PathBuf>,
}

#[derive(Debug, Clone, Default, Deserialize)]
#[serde(rename_all = "camelCase")]
struct RawTsConfig {
  #[serde(default)]
  extends: Option<String>,
  #[serde(default)]
  compiler_options: RawCompilerOptions,
  #[serde(default)]
  files: Option<Vec<String>>,
  #[serde(default)]
  include: Option<Vec<String>>,
  #[serde(default)]
  exclude: Option<Vec<String>>,
}

#[derive(Debug, Clone, Default, Deserialize)]
#[serde(rename_all = "camelCase")]
struct RawCompilerOptions {
  #[serde(default)]
  target: Option<String>,
  #[serde(default)]
  lib: Option<Vec<String>>,
  #[serde(default)]
  strict_null_checks: Option<bool>,
  #[serde(default)]
  strict_function_types: Option<bool>,
  #[serde(default)]
  exact_optional_property_types: Option<bool>,
  #[serde(default)]
  no_unchecked_indexed_access: Option<bool>,
  #[serde(default)]
  no_lib: Option<bool>,
  #[serde(default)]
  no_default_lib: Option<bool>,
  #[serde(default)]
  jsx: Option<String>,
  #[serde(default)]
  base_url: Option<String>,
  #[serde(default)]
  paths: Option<BTreeMap<String, Vec<String>>>,
}

pub fn load_project_config(project: &Path) -> Result<ProjectConfig, String> {
  let tsconfig_path = resolve_tsconfig_path(project)?;
  let root_dir = tsconfig_path
    .parent()
    .ok_or_else(|| format!("invalid tsconfig path {}", tsconfig_path.display()))?
    .to_path_buf();
  let mut visited = HashSet::new();
  let raw = load_raw_config(&tsconfig_path, &mut visited)?;

  let mut compiler_options = compiler_options_from_raw(&raw.compiler_options)?;
  let mut base_url = raw
    .compiler_options
    .base_url
    .as_deref()
    .map(|raw| resolve_path_relative_to(&root_dir, Path::new(raw)));
  let paths = raw.compiler_options.paths.clone().unwrap_or_default();
  if base_url.is_none() && !paths.is_empty() {
    base_url = Some(root_dir.clone());
  }

  let root_files = discover_root_files(&root_dir, &raw)?;

  // Convenience: include DOM when explicitly listed via `lib`.
  if compiler_options.libs.contains(&LibName::Dom) {
    compiler_options.include_dom = true;
  }

  Ok(ProjectConfig {
    tsconfig_path,
    root_dir,
    compiler_options,
    base_url,
    paths,
    root_files,
  })
}

fn resolve_tsconfig_path(project: &Path) -> Result<PathBuf, String> {
  let candidate = if project.is_dir() {
    project.join("tsconfig.json")
  } else {
    project.to_path_buf()
  };
  let absolute = if candidate.is_absolute() {
    candidate
  } else {
    std::env::current_dir()
      .map_err(|err| format!("failed to resolve current directory: {err}"))?
      .join(candidate)
  };
  absolute
    .canonicalize()
    .map_err(|err| format!("failed to read tsconfig {}: {err}", absolute.display()))
}

fn load_raw_config(path: &Path, visited: &mut HashSet<PathBuf>) -> Result<RawTsConfig, String> {
  let canonical = path
    .canonicalize()
    .map_err(|err| format!("failed to read tsconfig {}: {err}", path.display()))?;
  if !visited.insert(canonical.clone()) {
    return Err(format!(
      "cycle detected while resolving tsconfig extends: {}",
      canonical.display()
    ));
  }

  let text = fs::read_to_string(&canonical)
    .map_err(|err| format!("failed to read {}: {err}", canonical.display()))?;
  let mut current: RawTsConfig = json5::from_str(&text)
    .map_err(|err| format!("failed to parse {}: {err}", canonical.display()))?;

  let Some(extends) = current.extends.take() else {
    return Ok(current);
  };

  let config_dir = canonical
    .parent()
    .ok_or_else(|| format!("invalid tsconfig path {}", canonical.display()))?;
  let extends_path = resolve_extends_path(config_dir, &extends)?;
  let base = load_raw_config(&extends_path, visited)?;
  Ok(merge_raw_configs(base, current))
}

fn resolve_extends_path(config_dir: &Path, extends: &str) -> Result<PathBuf, String> {
  if extends.starts_with('.') || Path::new(extends).is_absolute() {
    return resolve_extends_file(&resolve_path_relative_to(config_dir, Path::new(extends)));
  }

  for ancestor in config_dir.ancestors() {
    let base = ancestor.join("node_modules").join(extends);
    if let Ok(resolved) = resolve_extends_file(&base) {
      return Ok(resolved);
    }
  }

  Err(format!(
    "failed to resolve tsconfig extends '{extends}' from {}",
    config_dir.display()
  ))
}

fn resolve_extends_file(candidate: &Path) -> Result<PathBuf, String> {
  let mut attempts = Vec::new();
  attempts.push(candidate.to_path_buf());
  if candidate.extension().is_none() {
    attempts.push(candidate.with_extension("json"));
  }
  if candidate.is_dir() {
    attempts.push(candidate.join("tsconfig.json"));
  }

  for attempt in attempts {
    if attempt.is_file() {
      return attempt.canonicalize().map_err(|err| {
        format!(
          "failed to read extended tsconfig {}: {err}",
          attempt.display()
        )
      });
    }
  }

  Err(format!(
    "extended tsconfig {} does not exist",
    candidate.display()
  ))
}

fn merge_raw_configs(base: RawTsConfig, overlay: RawTsConfig) -> RawTsConfig {
  RawTsConfig {
    extends: None,
    compiler_options: merge_raw_compiler_options(base.compiler_options, overlay.compiler_options),
    files: overlay.files.or(base.files),
    include: overlay.include.or(base.include),
    exclude: overlay.exclude.or(base.exclude),
  }
}

fn merge_raw_compiler_options(
  base: RawCompilerOptions,
  overlay: RawCompilerOptions,
) -> RawCompilerOptions {
  RawCompilerOptions {
    target: overlay.target.or(base.target),
    lib: overlay.lib.or(base.lib),
    strict_null_checks: overlay.strict_null_checks.or(base.strict_null_checks),
    strict_function_types: overlay.strict_function_types.or(base.strict_function_types),
    exact_optional_property_types: overlay
      .exact_optional_property_types
      .or(base.exact_optional_property_types),
    no_unchecked_indexed_access: overlay
      .no_unchecked_indexed_access
      .or(base.no_unchecked_indexed_access),
    no_lib: overlay.no_lib.or(base.no_lib),
    no_default_lib: overlay.no_default_lib.or(base.no_default_lib),
    jsx: overlay.jsx.or(base.jsx),
    base_url: overlay.base_url.or(base.base_url),
    paths: overlay.paths.or(base.paths),
  }
}

fn compiler_options_from_raw(raw: &RawCompilerOptions) -> Result<CompilerOptions, String> {
  let mut options = CompilerOptions::default();

  if let Some(raw) = raw.target.as_deref() {
    options.target =
      parse_script_target(raw).ok_or_else(|| format!("unknown compilerOptions.target '{raw}'"))?;
  }

  if let Some(libs) = raw.lib.as_ref() {
    let mut parsed = Vec::new();
    for raw in libs {
      if let Some(lib) = parse_lib_name(raw) {
        parsed.push(lib);
      }
    }
    if parsed.is_empty() && !libs.is_empty() {
      return Err("compilerOptions.lib did not include any supported libs".to_string());
    }
    parsed.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    parsed.dedup();
    options.libs = parsed;
  }

  if raw.no_lib.unwrap_or(false) || raw.no_default_lib.unwrap_or(false) {
    options.no_default_lib = true;
    options.libs.clear();
  }

  if let Some(value) = raw.strict_null_checks {
    options.strict_null_checks = value;
  }
  if let Some(value) = raw.strict_function_types {
    options.strict_function_types = value;
  }
  if let Some(value) = raw.exact_optional_property_types {
    options.exact_optional_property_types = value;
  }
  if let Some(value) = raw.no_unchecked_indexed_access {
    options.no_unchecked_indexed_access = value;
  }

  if let Some(raw) = raw.jsx.as_deref() {
    options.jsx = Some(parse_jsx_mode(raw)?);
  }

  Ok(options)
}

fn parse_script_target(raw: &str) -> Option<ScriptTarget> {
  let normalized = raw.trim().to_ascii_lowercase();
  match normalized.as_str() {
    "es3" => Some(ScriptTarget::Es3),
    "es5" => Some(ScriptTarget::Es5),
    "es2015" | "es6" => Some(ScriptTarget::Es2015),
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

fn parse_lib_name(raw: &str) -> Option<LibName> {
  let normalized = raw.trim().to_ascii_lowercase();
  let base = normalized.split('.').next().unwrap_or(&normalized);
  match base {
    "es5" => Some(LibName::Es5),
    "es2015" | "es6" => Some(LibName::Es2015),
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

fn parse_jsx_mode(raw: &str) -> Result<JsxMode, String> {
  let normalized = raw.trim().to_ascii_lowercase();
  match normalized.as_str() {
    "preserve" | "react-native" => Ok(JsxMode::Preserve),
    "react" => Ok(JsxMode::React),
    "react-jsx" => Ok(JsxMode::ReactJsx),
    "react-jsxdev" => Ok(JsxMode::ReactJsxdev),
    other => Err(format!("unknown compilerOptions.jsx '{other}'")),
  }
}

fn discover_root_files(root_dir: &Path, raw: &RawTsConfig) -> Result<Vec<PathBuf>, String> {
  if let Some(files) = raw.files.as_ref() {
    let mut resolved = Vec::new();
    for file in files {
      let path = resolve_path_relative_to(root_dir, Path::new(file));
      resolved.push(
        path
          .canonicalize()
          .map_err(|err| format!("failed to read project file {}: {err}", path.display()))?,
      );
    }
    resolved.sort_by(|a, b| a.display().to_string().cmp(&b.display().to_string()));
    resolved.dedup();
    return Ok(resolved);
  }

  let include = raw
    .include
    .clone()
    .unwrap_or_else(|| vec!["**/*".to_string()]);

  let exclude = match raw.exclude.clone() {
    Some(patterns) => patterns,
    None => vec![
      "node_modules".to_string(),
      "bower_components".to_string(),
      "jspm_packages".to_string(),
    ],
  };

  let include_set = build_globset(&include)?;
  let exclude_set = build_globset(&exclude)?;

  let mut files = Vec::new();
  for entry in WalkDir::new(root_dir)
    .follow_links(false)
    .into_iter()
    .filter_map(|entry| entry.ok())
  {
    if !entry.file_type().is_file() {
      continue;
    }
    if !is_supported_source_file(entry.path()) {
      continue;
    }
    let rel = match entry.path().strip_prefix(root_dir) {
      Ok(rel) => rel,
      Err(_) => continue,
    };
    if !include_set.is_match(rel) {
      continue;
    }
    if exclude_set.is_match(rel) {
      continue;
    }
    files.push(
      entry
        .path()
        .canonicalize()
        .unwrap_or_else(|_| entry.path().to_path_buf()),
    );
  }

  files.sort_by(|a, b| a.display().to_string().cmp(&b.display().to_string()));
  files.dedup();
  Ok(files)
}

fn build_globset(patterns: &[String]) -> Result<GlobSet, String> {
  let mut builder = GlobSetBuilder::new();
  for pat in patterns {
    let normalized = normalize_glob_pattern(pat)?;
    if normalized.is_empty() {
      continue;
    }
    let glob =
      Glob::new(&normalized).map_err(|err| format!("invalid glob pattern '{pat}': {err}"))?;
    builder.add(glob);
  }
  builder
    .build()
    .map_err(|err| format!("failed to build glob matcher: {err}"))
}

fn normalize_glob_pattern(pattern: &str) -> Result<String, String> {
  let trimmed = pattern.trim();
  if trimmed.is_empty() {
    return Ok(trimmed.to_string());
  }
  Ok(expand_directory_pattern(trimmed))
}

fn expand_directory_pattern(pattern: &str) -> String {
  if contains_glob_magic(pattern) {
    return pattern.to_string();
  }

  let trimmed = pattern.trim_end_matches('/');
  if trimmed.is_empty() {
    return "**/*".to_string();
  }
  let file_name = Path::new(trimmed)
    .file_name()
    .and_then(|s| s.to_str())
    .unwrap_or("");
  if file_name.ends_with(".d.ts") {
    return trimmed.to_string();
  }
  match Path::new(trimmed).extension().and_then(|e| e.to_str()) {
    Some("ts" | "tsx" | "js" | "jsx" | "json") => trimmed.to_string(),
    Some(_) => trimmed.to_string(),
    None => format!("{trimmed}/**/*"),
  }
}

fn contains_glob_magic(pattern: &str) -> bool {
  pattern
    .chars()
    .any(|ch| matches!(ch, '*' | '?' | '[' | ']'))
}

fn is_supported_source_file(path: &Path) -> bool {
  let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
  if name.ends_with(".d.ts") {
    return true;
  }
  matches!(
    path.extension().and_then(|e| e.to_str()),
    Some("ts" | "tsx")
  )
}

fn resolve_path_relative_to(base: &Path, path: &Path) -> PathBuf {
  if path.is_absolute() {
    path.to_path_buf()
  } else {
    base.join(path)
  }
}
