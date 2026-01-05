use std::fs;
use std::path::{Path, PathBuf};
use typecheck_ts_harness::tsc::{node_available, typescript_available, TscRunner};

pub fn node_path_or_skip(context: &str) -> Option<PathBuf> {
  let node_path = PathBuf::from("node");

  if !node_available(&node_path) {
    eprintln!("skipping {context}: node not available");
    return None;
  }

  if !typescript_available(&node_path) {
    eprintln!(
      "skipping {context}: typescript not available (run `cd typecheck-ts-harness && npm ci`)"
    );
    return None;
  }

  Some(node_path)
}

#[allow(dead_code)]
pub fn runner_or_skip(context: &str) -> Option<TscRunner> {
  let node_path = node_path_or_skip(context)?;

  match TscRunner::new(node_path) {
    Ok(runner) => Some(runner),
    Err(err) => {
      eprintln!("skipping {context}: {err}");
      None
    }
  }
}

#[allow(dead_code)]
pub fn temp_difftsc_suite(fixtures: &[&str]) -> (tempfile::TempDir, PathBuf) {
  let dir = tempfile::tempdir().expect("tempdir");
  let suite = dir.path().join("difftsc");
  fs::create_dir_all(&suite).expect("create difftsc suite directory");

  let source = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("difftsc");

  for fixture in fixtures {
    let src = source.join(fixture);
    let dst = suite.join(fixture);
    copy_recursively(&src, &dst).expect("copy fixture");
  }

  (dir, suite)
}

#[allow(dead_code)]
fn copy_recursively(src: &Path, dst: &Path) -> std::io::Result<()> {
  if src.is_dir() {
    fs::create_dir_all(dst)?;
    for entry in walkdir::WalkDir::new(src) {
      let entry = entry?;
      let path = entry.path();
      let rel = path.strip_prefix(src).unwrap_or(path);
      let target = dst.join(rel);
      if entry.file_type().is_dir() {
        fs::create_dir_all(&target)?;
        continue;
      }

      if let Some(parent) = target.parent() {
        fs::create_dir_all(parent)?;
      }
      fs::copy(path, &target)?;
    }
    return Ok(());
  }

  if let Some(parent) = dst.parent() {
    fs::create_dir_all(parent)?;
  }
  fs::copy(src, dst)?;
  Ok(())
}
