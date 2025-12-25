//! Helpers for selecting and loading TypeScript lib declaration files.
//!
//! This module exposes the lib selection and loading utilities used by the real
//! checker. The legacy [`LibCheckProgram`] is a string-scanning helper retained
//! for transitional testing; it is **not** the actual type checker API.

mod compiler_options;
mod host;
pub mod lib_env;

pub use compiler_options::{CompilerOptions, JsxMode, LibName, LibSet, ModuleKind, ScriptTarget};
#[allow(deprecated)]
pub use host::LibCheckHost;
pub use lib_env::{LibManager, LoadedLibs};

use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::sync::Arc;

use crate::{Diagnostic, FileId, Span, TextRange};

/// Kinds of supported files.
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

fn lib_diagnostic(
  code: &'static str,
  message: impl Into<String>,
  file: Option<FileId>,
) -> Diagnostic {
  Diagnostic::error(
    code,
    message,
    Span::new(file.unwrap_or(FileId(u32::MAX)), TextRange::new(0, 0)),
  )
}

/// Deprecated, string-scanning helper that checks root files against loaded libs.
///
/// This is **not** the real `typecheck_ts::Program`. It only loads bundled libs
/// and emits basic diagnostics about missing globals.
#[allow(deprecated)]
#[deprecated(
  note = "LibCheckProgram is a legacy string-scanning helper; it is not the real type checker API."
)]
pub struct LibCheckProgram {
  host: Arc<dyn LibCheckHost>,
  libs: Vec<LibFile>,
  global_env: GlobalEnv,
  lib_diags: Vec<Diagnostic>,
  lib_manager: Arc<LibManager>,
}

#[allow(deprecated)]
impl LibCheckProgram {
  /// Construct a program using the default lib manager.
  pub fn new(host: Arc<dyn LibCheckHost>) -> Self {
    LibCheckProgram::with_lib_manager(host, Arc::new(LibManager::new()))
  }

  /// Construct a program with a provided lib manager (useful for tests to observe invalidation).
  pub fn with_lib_manager(host: Arc<dyn LibCheckHost>, lib_manager: Arc<LibManager>) -> Self {
    let options = host.compiler_options();
    let mut lib_diags = Vec::new();
    let libs = collect_libraries(host.as_ref(), &options, &lib_manager, &mut lib_diags);
    let global_env = build_global_env(&libs, &mut lib_diags);

    LibCheckProgram {
      host,
      libs,
      global_env,
      lib_diags,
      lib_manager,
    }
  }

  /// Perform lib checking across all root files and return diagnostics.
  pub fn check(&self) -> Vec<Diagnostic> {
    let mut diags = self.lib_diags.clone();

    if self.libs.is_empty() {
      diags.push(lib_diagnostic(
        "TC0001",
        "No library files were loaded. Provide libs via the host or enable the bundled-libs feature / disable no_default_lib.",
        None,
      ));
      return diags;
    }

    for file in self.host.root_files() {
      check_file(file, self.host.as_ref(), &self.global_env, &mut diags);
    }

    diags
  }

  /// Expose libs used by this program (mainly for tests).
  pub fn libs(&self) -> &[LibFile] {
    &self.libs
  }

  pub fn lib_manager(&self) -> Arc<LibManager> {
    self.lib_manager.clone()
  }
}

#[allow(deprecated)]
fn collect_libraries(
  host: &dyn LibCheckHost,
  options: &CompilerOptions,
  lib_manager: &LibManager,
  diags: &mut Vec<Diagnostic>,
) -> Vec<LibFile> {
  let mut libs = host.lib_files();
  if !options.no_default_lib {
    let bundled = lib_manager.bundled_libs(options);
    libs.extend(bundled.files);
  }

  for lib in libs.iter() {
    if lib.kind != FileKind::Dts {
      diags.push(lib_diagnostic(
        "TC0004",
        format!(
          "Library '{}' is not a .d.ts file; it will be ignored for global declarations.",
          lib.name
        ),
        Some(lib.id),
      ));
    }
  }

  libs
}

#[derive(Clone, Debug)]
enum GlobalValue {
  Any,
  Object(GlobalObject),
}

#[derive(Clone, Debug, Default)]
struct GlobalObject {
  props: HashMap<String, GlobalValue>,
}

#[derive(Clone, Debug, Default)]
struct GlobalEnv {
  globals: HashMap<String, GlobalValue>,
}

impl GlobalEnv {
  fn has_global(&self, name: &str) -> bool {
    self.globals.contains_key(name)
  }

  fn has_property(&self, obj: &str, prop: &str) -> bool {
    match self.globals.get(obj) {
      Some(GlobalValue::Any) => true,
      Some(GlobalValue::Object(o)) => o.props.contains_key(prop),
      None => false,
    }
  }

  fn set_any(&mut self, name: &str) {
    self
      .globals
      .entry(name.to_string())
      .or_insert(GlobalValue::Any);
  }

  fn merge_object(
    &mut self,
    name: &str,
    props: Vec<String>,
    diags: &mut Vec<Diagnostic>,
    file: FileId,
  ) {
    match self.globals.entry(name.to_string()) {
      Entry::Vacant(v) => {
        let mut obj = GlobalObject::default();
        for prop in props {
          obj.props.entry(prop).or_insert(GlobalValue::Any);
        }
        v.insert(GlobalValue::Object(obj));
      }
      Entry::Occupied(mut entry) => match entry.get_mut() {
        GlobalValue::Object(obj) => {
          for prop in props {
            obj.props.entry(prop).or_insert(GlobalValue::Any);
          }
        }
        GlobalValue::Any => {
          diags.push(lib_diagnostic(
            "TC0003",
            format!("Unsupported global augmentation for '{}'.", name),
            Some(file),
          ));
        }
      },
    }
  }
}

fn build_global_env(libs: &[LibFile], diags: &mut Vec<Diagnostic>) -> GlobalEnv {
  let mut env = GlobalEnv::default();
  for lib in libs {
    add_lib_decls(&mut env, lib, diags);
  }
  env
}

fn add_lib_decls(env: &mut GlobalEnv, lib: &LibFile, diags: &mut Vec<Diagnostic>) {
  if lib.kind != FileKind::Dts {
    return;
  }

  let text = lib.text.as_ref();
  if text.contains("declare global") {
    diags.push(lib_diagnostic(
      "TC0002",
      "Global augmentations are only partially supported; declaration will be treated as-is.",
      Some(lib.id),
    ));
  }

  for segment in text.split("declare") {
    match parse_declare_segment(segment) {
      Some(GlobalDecl::Object { name, props }) => env.merge_object(&name, props, diags, lib.id),
      Some(GlobalDecl::Any { name }) => env.set_any(&name),
      None => {}
    }
  }
}

enum GlobalDecl {
  Any { name: String },
  Object { name: String, props: Vec<String> },
}

fn parse_declare_segment(segment: &str) -> Option<GlobalDecl> {
  let trimmed = segment.trim();
  if trimmed.is_empty() {
    return None;
  }
  if !(trimmed.starts_with("const") || trimmed.starts_with("var") || trimmed.starts_with("let")) {
    return None;
  }
  let after = trimmed
    .trim_start_matches("const")
    .trim_start_matches("var")
    .trim_start_matches("let")
    .trim();

  let mut name = String::new();
  for ch in after.chars() {
    if ch.is_ascii_alphanumeric() || ch == '_' || ch == '$' {
      name.push(ch);
    } else {
      break;
    }
  }
  if name.is_empty() {
    return None;
  }

  if let Some(props) = extract_props(after) {
    return Some(GlobalDecl::Object { name, props });
  }

  Some(GlobalDecl::Any { name })
}

fn extract_props(after: &str) -> Option<Vec<String>> {
  if let (Some(open), Some(close)) = (after.find('{'), after.rfind('}')) {
    if close > open {
      let body = &after[open + 1..close];
      let props: Vec<String> = body
        .split(';')
        .filter_map(|seg| {
          let seg = seg.trim();
          if seg.is_empty() {
            return None;
          }
          let mut name = String::new();
          for ch in seg.chars() {
            if ch.is_ascii_alphanumeric() || ch == '_' || ch == '$' {
              name.push(ch);
            } else {
              break;
            }
          }
          if name.is_empty() {
            None
          } else {
            Some(name)
          }
        })
        .collect();
      return Some(props);
    }
  }
  None
}

#[allow(deprecated)]
fn check_file(file: FileId, host: &dyn LibCheckHost, env: &GlobalEnv, diags: &mut Vec<Diagnostic>) {
  let text = host.file_text(file);

  check_global_use(&text, file, "console", env, diags, Some("log"));
  check_global_use(&text, file, "document", env, diags, None);
  check_global_use(&text, file, "window", env, diags, None);
}

fn check_global_use(
  text: &str,
  file: FileId,
  name: &str,
  env: &GlobalEnv,
  diags: &mut Vec<Diagnostic>,
  property: Option<&str>,
) {
  if !text.contains(name) {
    return;
  }

  if !env.has_global(name) {
    diags.push(lib_diagnostic(
      "TC0005",
      format!(
        "Cannot find name '{}'. Consider adding appropriate libs.",
        name
      ),
      Some(file),
    ));
    return;
  }

  if let Some(prop) = property {
    if text.contains(&format!("{}.", name)) && !env.has_property(name, prop) {
      diags.push(lib_diagnostic(
        "TC0006",
        format!("Property '{}' does not exist on '{}'.", prop, name),
        Some(file),
      ));
    }
  }
}

#[cfg(test)]
#[allow(deprecated)]
mod tests {
  use super::*;

  struct TestHost {
    files: HashMap<FileId, (FileKind, Arc<str>)>,
    libs: Vec<LibFile>,
    root: Vec<FileId>,
    options: CompilerOptions,
  }

  impl TestHost {
    fn new(options: CompilerOptions) -> Self {
      TestHost {
        files: HashMap::new(),
        libs: Vec::new(),
        root: Vec::new(),
        options,
      }
    }

    fn with_file(mut self, id: FileId, kind: FileKind, text: &str) -> Self {
      self.files.insert(id, (kind, Arc::from(text)));
      self.root.push(id);
      self
    }

    fn with_lib(mut self, lib: LibFile) -> Self {
      self.libs.push(lib);
      self
    }
  }

  impl LibCheckHost for TestHost {
    fn root_files(&self) -> Vec<FileId> {
      self.root.clone()
    }

    fn file_text(&self, file: FileId) -> Arc<str> {
      self
        .files
        .get(&file)
        .map(|(_, text)| text.clone())
        .unwrap_or_else(|| Arc::from(""))
    }

    fn file_kind(&self, file: FileId) -> FileKind {
      self
        .files
        .get(&file)
        .map(|(kind, _)| *kind)
        .unwrap_or(FileKind::Ts)
    }

    fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
      None
    }

    fn lib_files(&self) -> Vec<LibFile> {
      self.libs.clone()
    }

    fn compiler_options(&self) -> CompilerOptions {
      self.options.clone()
    }
  }

  fn console_lib(id: FileId, name: &str) -> LibFile {
    LibFile {
      id,
      name: Arc::from(name),
      kind: FileKind::Dts,
      text: Arc::from("declare const console: {\n  log(msg: string): void;\n};\n"),
    }
  }

  #[test]
  fn bundled_lib_allows_console_usage() {
    let host = TestHost::new(CompilerOptions::default()).with_file(
      FileId(0),
      FileKind::Ts,
      "console.log(\"hi\")",
    );
    let program = LibCheckProgram::new(Arc::new(host));
    let diags = program.check();
    assert!(diags.is_empty(), "expected no diagnostics, got {diags:?}");
    assert!(
      !program.libs().is_empty(),
      "bundled libs should be loaded by default"
    );
  }

  #[test]
  fn host_libs_are_used_when_provided() {
    let options = CompilerOptions {
      no_default_lib: true,
      ..Default::default()
    };
    let host = TestHost::new(options)
      .with_lib(console_lib(FileId(99), "host-lib"))
      .with_file(FileId(0), FileKind::Ts, "console.log(\"hi\")");

    let program = LibCheckProgram::new(Arc::new(host));
    let diags = program.check();
    assert!(
      diags.is_empty(),
      "console should be resolved from host libs"
    );
  }

  #[test]
  fn missing_libs_emits_diagnostic() {
    let options = CompilerOptions {
      no_default_lib: true,
      ..Default::default()
    };
    let host = TestHost::new(options).with_file(FileId(0), FileKind::Ts, "console.log('x')");
    let program = LibCheckProgram::new(Arc::new(host));
    let diags = program.check();
    assert_eq!(
      diags.len(),
      1,
      "should emit a single diagnostic when libs are missing"
    );
    assert_eq!(
      diags[0].code, "TC0001",
      "should surface missing lib diagnostic"
    );
  }

  #[test]
  fn target_change_invalidate_lib_selection() {
    let manager = Arc::new(LibManager::new());

    let mut options_es5 = CompilerOptions::default();
    options_es5.target = ScriptTarget::Es5;
    options_es5.include_dom = false;

    let host_a = TestHost::new(options_es5.clone()).with_file(FileId(0), FileKind::Ts, "");
    let program_a = LibCheckProgram::with_lib_manager(Arc::new(host_a), manager.clone());
    program_a.check();
    let count_after_first = manager.load_count();

    let host_b = TestHost::new(options_es5.clone()).with_file(FileId(1), FileKind::Ts, "");
    let program_b = LibCheckProgram::with_lib_manager(Arc::new(host_b), manager.clone());
    program_b.check();
    let count_after_second = manager.load_count();
    assert_eq!(
      count_after_first, count_after_second,
      "libs should be reused for same target"
    );

    let mut options_es2015 = options_es5.clone();
    options_es2015.target = ScriptTarget::Es2015;
    let host_c = TestHost::new(options_es2015).with_file(FileId(2), FileKind::Ts, "");
    let program_c = LibCheckProgram::with_lib_manager(Arc::new(host_c), manager.clone());
    program_c.check();
    let count_after_third = manager.load_count();
    assert!(
      count_after_third > count_after_second,
      "changing target should invalidate cached libs"
    );
  }

  #[test]
  fn host_libs_extend_default_libs() {
    let options = CompilerOptions::default();
    let host = TestHost::new(options)
      .with_lib(console_lib(FileId(100), "host-lib"))
      .with_file(FileId(0), FileKind::Ts, "console.log('hi')");

    let program = LibCheckProgram::new(Arc::new(host));
    let libs = program.libs();
    assert!(
      libs.iter().any(|l| l.name.as_ref() == "host-lib"),
      "host libs should be loaded alongside bundled libs"
    );
    assert!(
      libs.iter().any(|l| l.name.as_ref().contains("lib.es")),
      "bundled libs should still be present by default"
    );
  }

  #[test]
  fn dom_lib_is_optional() {
    let mut options = CompilerOptions::default();
    options.include_dom = false;
    let host = TestHost::new(options.clone()).with_file(FileId(0), FileKind::Ts, "document.title");
    let program = LibCheckProgram::new(Arc::new(host));
    let diags = program.check();
    assert!(
      diags.iter().any(|d| d.code == "TC0005"),
      "should flag missing dom global when include_dom is false"
    );

    options.include_dom = true;
    let host_with_dom = TestHost::new(options).with_file(FileId(1), FileKind::Ts, "document.title");
    let program_with_dom = LibCheckProgram::new(Arc::new(host_with_dom));
    let diags = program_with_dom.check();
    assert!(
      diags.is_empty(),
      "DOM lib should supply document when include_dom is true"
    );
  }

  #[test]
  fn lib_selection_matches_target() {
    let mut options_es5 = CompilerOptions::default();
    options_es5.target = ScriptTarget::Es5;
    let host_es5 = TestHost::new(options_es5).with_file(FileId(0), FileKind::Ts, "");
    let program_es5 = LibCheckProgram::new(Arc::new(host_es5));
    let libs_es5: Vec<_> = program_es5
      .libs()
      .iter()
      .map(|l| l.name.as_ref().to_string())
      .collect();
    assert!(
      libs_es5.iter().any(|n| n.contains("lib.es5.d.ts")),
      "es5 target should include es5 lib"
    );

    let mut options_es2015 = CompilerOptions::default();
    options_es2015.target = ScriptTarget::Es2015;
    let host_es2015 = TestHost::new(options_es2015).with_file(FileId(1), FileKind::Ts, "");
    let program_es2015 = LibCheckProgram::new(Arc::new(host_es2015));
    let libs_es2015: Vec<_> = program_es2015
      .libs()
      .iter()
      .map(|l| l.name.as_ref().to_string())
      .collect();
    assert!(
      libs_es2015.iter().any(|n| n.contains("lib.es2015.d.ts")),
      "es2015 target should include es2015 lib"
    );
  }
}
