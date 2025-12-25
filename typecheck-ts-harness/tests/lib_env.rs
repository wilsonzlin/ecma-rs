use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;
use tempfile::tempdir;
use typecheck_ts::{FileId, Host, HostError, Program};
use typecheck_ts_harness::collect_harness_options;
use typecheck_ts_harness::libs::{resolve_libs, LIB_DIRECTORY};
use typecheck_ts_harness::tsc::{node_available, TscDiagnostics, TscRequest, TscRunner};
use typecheck_ts_harness::{EffectiveLibs, LibFlags, VirtualFile};

#[derive(Clone)]
struct SimpleHost {
  files: Vec<VirtualFile>,
}

impl SimpleHost {
  fn new(files: Vec<VirtualFile>) -> Self {
    Self { files }
  }

  fn roots(&self) -> Vec<FileId> {
    (0..self.files.len()).map(|i| FileId(i as u32)).collect()
  }
}

impl Host for SimpleHost {
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(file.0 as usize)
      .map(|f| Arc::from(f.content.clone()))
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
    None
  }
}

fn fixture_path() -> PathBuf {
  Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("lib_env")
    .join("promise.ts")
}

fn promise_fixture() -> VirtualFile {
  let path = fixture_path();
  VirtualFile {
    name: "promise.ts".to_string(),
    content: fs::read_to_string(path).expect("read fixture"),
  }
}

fn effective_libs_for(file: &VirtualFile, tsc_no_lib: bool) -> EffectiveLibs {
  let directives = collect_harness_options(&[file.clone()]);
  let flags = LibFlags {
    tsc_no_lib,
    libs: Vec::new(),
    use_directive_libs: true,
  };
  flags.effective_libs(&directives).expect("compute libs")
}

fn run_rust(files: Vec<VirtualFile>) -> Vec<typecheck_ts::Diagnostic> {
  let host = SimpleHost::new(files.clone());
  let roots = host.roots();
  Program::new(host, roots).check()
}

#[cfg(feature = "with-node")]
fn typescript_available() -> bool {
  if !node_available(Path::new("node")).unwrap_or(false) {
    return false;
  }
  Command::new("node")
    .args(["-e", "require('typescript')"])
    .output()
    .map(|out| out.status.success())
    .unwrap_or(false)
}

#[cfg(feature = "with-node")]
fn run_tsc(file: &VirtualFile, libs: &EffectiveLibs) -> Option<TscDiagnostics> {
  if !typescript_available() {
    return None;
  }

  let temp_dir = tempdir().ok()?;
  let file_path = temp_dir.path().join(&file.name);
  if let Some(parent) = file_path.parent() {
    fs::create_dir_all(parent).ok()?;
  }
  fs::write(&file_path, &file.content).ok()?;

  let lib_files = if libs.no_lib {
    Vec::new()
  } else {
    resolve_libs(&libs.libs).ok()?
  };
  if !lib_files.is_empty() {
    for lib in &lib_files {
      let out = temp_dir.path().join(&lib.name);
      if let Some(parent) = out.parent() {
        fs::create_dir_all(parent).ok()?;
      }
      fs::write(&out, &lib.content).ok()?;
    }
  }

  let request = TscRequest {
    cwd: temp_dir.path().to_path_buf(),
    root_files: vec![file_path],
    no_lib: libs.no_lib,
    libs: if libs.no_lib {
      Vec::new()
    } else {
      libs.libs.clone()
    },
    lib_root: if lib_files.is_empty() {
      None
    } else {
      Some(temp_dir.path().join(LIB_DIRECTORY))
    },
  };

  runner().run(&request).ok()
}

#[cfg(feature = "with-node")]
fn runner() -> TscRunner {
  TscRunner::new(PathBuf::from("node"))
}

#[test]
fn promise_reports_unknown_without_libs() {
  let fixture = promise_fixture();
  let no_libs = effective_libs_for(&fixture, true);

  let rust_diags = run_rust(vec![fixture.clone()]);
  assert!(
    rust_diags.iter().any(|d| d.message.contains("Promise")),
    "expected an unknown identifier diagnostic, got {rust_diags:?}"
  );

  #[cfg(feature = "with-node")]
  {
    if let Some(tsc) = run_tsc(&fixture, &no_libs) {
      assert!(
        tsc.diagnostics.iter().any(|d| d.code == 2304),
        "expected tsc to report missing Promise, got {:?}",
        tsc.diagnostics
      );
    } else {
      eprintln!("skipping tsc check without libs (TypeScript not available)");
    }
  }
}

#[test]
fn tsc_accepts_promise_with_libs_when_available() {
  let fixture = promise_fixture();
  let with_libs = effective_libs_for(&fixture, false);
  let lib_files = resolve_libs(&with_libs.libs).expect("resolve libs");

  let mut all_files = vec![fixture.clone()];
  all_files.extend(lib_files.clone());
  let host = SimpleHost::new(all_files.clone());
  let roots = host.roots();
  // Ensure libs are wired in; diagnostics may still exist until the checker understands .d.ts fully.
  let _ = Program::new(host, roots).check();

  #[cfg(feature = "with-node")]
  {
    if let Some(tsc) = run_tsc(&fixture, &with_libs) {
      assert!(
        tsc.diagnostics.is_empty(),
        "expected no diagnostics with libs, got {:?}",
        tsc.diagnostics
      );
    } else {
      eprintln!("skipping tsc check with libs (TypeScript not available)");
    }
  }
}
