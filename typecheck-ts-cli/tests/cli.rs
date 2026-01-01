use assert_cmd::Command;
use predicates::str::{contains, is_empty};
use serde_json::Value;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use tempfile::NamedTempFile;

fn fixture(name: &str) -> PathBuf {
  Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("tests")
    .join("fixtures")
    .join(name)
}

fn normalized(path: &Path) -> String {
  path
    .canonicalize()
    .unwrap_or_else(|_| path.to_path_buf())
    .display()
    .to_string()
}

#[test]
fn typecheck_succeeds_on_basic_fixture() {
  let path = fixture("basic.ts");
  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .args(["typecheck"])
    .arg(path.as_os_str())
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn type_at_reports_number() {
  let path = fixture("basic.ts");
  let normalized_path = normalized(&path);
  let content = fs::read_to_string(&path).expect("read fixture");
  let offset = content
    .find("a + b")
    .map(|idx| idx as u32)
    .expect("offset for a + b");
  let query = format!("{}:{}", path.display(), offset);

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .args(["typecheck"])
    .arg(path.as_os_str())
    .args(["--type-at", &query])
    .assert()
    .success()
    .get_output()
    .stdout
    .clone();

  let stdout = String::from_utf8(output).unwrap();
  assert!(
    stdout.contains(&format!("type at {}:{}", normalized_path, offset)),
    "missing type-at header in output: {stdout:?}"
  );
  assert!(
    stdout.contains("number"),
    "expected number type in output, got {stdout:?}"
  );
}

#[test]
fn resolves_relative_modules_and_index_files() {
  let path = fixture("resolution/entry.ts");
  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .args(["typecheck"])
    .arg(path.as_os_str())
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn node_modules_resolution_is_opt_in() {
  let path = fixture("node_project/src/main.ts");

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .args(["typecheck"])
    .arg(path.as_os_str())
    .assert()
    .failure()
    .stdout(contains("unresolved module specifier"));

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .args(["typecheck"])
    .arg(path.as_os_str())
    .arg("--node-resolve")
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn json_output_is_stable_and_parseable() {
  let path = fixture("error.ts");
  let run = || {
    Command::cargo_bin("typecheck-ts-cli")
      .unwrap()
      .args(["typecheck"])
      .arg(path.as_os_str())
      .arg("--json")
      .assert()
      .failure()
      .get_output()
      .stdout
      .clone()
  };

  let output1 = String::from_utf8(run()).unwrap();
  let output2 = String::from_utf8(run()).unwrap();
  assert_eq!(
    output1, output2,
    "expected deterministic JSON output across runs"
  );

  let json: Value = serde_json::from_str(&output1).expect("valid JSON output");
  let files = json
    .get("files")
    .and_then(|f| f.as_array())
    .expect("files array");
  assert!(
    !files.is_empty(),
    "expected at least one file name, got {json:?}"
  );
  let diagnostics = json
    .get("diagnostics")
    .and_then(|d| d.as_array())
    .expect("diagnostics array");
  assert!(
    !diagnostics.is_empty(),
    "expected at least one diagnostic, got {json:?}"
  );
  assert!(
    diagnostics.iter().any(|d| d.get("code").is_some()),
    "diagnostics should include codes: {diagnostics:?}"
  );
}

#[test]
fn rejects_invalid_utf8_sources() {
  let mut file = NamedTempFile::new().expect("temp file");
  file
    .write_all(&[0xFF])
    .expect("write invalid utf-8 to temp file");
  let path = file.path().to_path_buf();

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .args(["typecheck"])
    .arg(path.as_os_str())
    .assert()
    .failure()
    .get_output()
    .stdout
    .clone();

  let stdout = String::from_utf8_lossy(&output);
  assert!(
    stdout.contains("UTF-8"),
    "expected UTF-8 error in CLI output, got: {stdout}"
  );
}

#[test]
fn project_mode_discovers_files_and_resolves_paths() {
  let tsconfig = fixture("project_mode/tsconfig.json");
  let index = fixture("project_mode/src/index.ts");
  let answer = fixture("project_mode/src/lib/answer.ts");
  let unused = fixture("project_mode/src/unused.ts");
  let ignored = fixture("project_mode/bower_components/ignored/index.ts");

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .args(["typecheck"])
    .arg("--project")
    .arg(tsconfig.as_os_str())
    .arg("--json")
    .assert()
    .failure()
    .get_output()
    .stdout
    .clone();
  let stdout = String::from_utf8(output).unwrap();

  let json: Value = serde_json::from_str(&stdout).expect("valid JSON output");
  let files: Vec<_> = json
    .get("files")
    .and_then(|f| f.as_array())
    .expect("files array")
    .iter()
    .filter_map(|v| v.as_str())
    .collect();

  assert!(
    files.contains(&normalized(&index).as_str()),
    "expected project mode to include index.ts, got: {files:?}"
  );
  assert!(
    files.contains(&normalized(&answer).as_str()),
    "expected project mode to include answer.ts, got: {files:?}"
  );
  assert!(
    files.contains(&normalized(&unused).as_str()),
    "expected project mode to include unused.ts, got: {files:?}"
  );
  assert!(
    !files.contains(&normalized(&ignored).as_str()),
    "expected default exclude to omit bower_components, got: {files:?}"
  );

  let diagnostics = json
    .get("diagnostics")
    .and_then(|d| d.as_array())
    .expect("diagnostics array");
  assert!(
    diagnostics
      .iter()
      .any(|d| d.get("code").and_then(|c| c.as_str()) == Some("TC0007")),
    "expected type mismatch diagnostic (TC0007), got: {diagnostics:?}"
  );
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.get("code").and_then(|c| c.as_str()) == Some("TC1001")),
    "expected path-mapped module to resolve without TC1001, got: {diagnostics:?}"
  );
}

#[test]
fn project_mode_exports_and_type_at_queries_work() {
  let tsconfig = fixture("project_mode/tsconfig.json");
  let index = fixture("project_mode/src/index.ts");
  let normalized_index = normalized(&index);
  let content = fs::read_to_string(&index).expect("read index.ts");
  let offset = content
    .find("answer * 2")
    .map(|idx| idx as u32)
    .expect("offset for answer * 2");
  let query = format!("{}:{}", index.display(), offset);

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .args(["typecheck"])
    .arg("--project")
    .arg(tsconfig.as_os_str())
    .arg("--json")
    .args(["--type-at", &query])
    .arg("--exports")
    .arg(index.as_os_str())
    .assert()
    .failure()
    .get_output()
    .stdout
    .clone();
  let stdout = String::from_utf8(output).unwrap();
  let json: Value = serde_json::from_str(&stdout).expect("valid JSON output");

  let queries = json
    .get("queries")
    .and_then(|q| q.as_object())
    .expect("queries object");

  let type_at = queries
    .get("type_at")
    .and_then(|v| v.as_object())
    .expect("type_at object");
  assert_eq!(
    type_at.get("file").and_then(|v| v.as_str()),
    Some(normalized_index.as_str())
  );
  assert_eq!(
    type_at.get("offset").and_then(|v| v.as_u64()),
    Some(offset as u64)
  );
  assert!(
    type_at
      .get("type")
      .and_then(|v| v.as_str())
      .unwrap_or("")
      .contains("number"),
    "expected number type-at result, got: {type_at:?}"
  );

  let exports = queries
    .get("exports")
    .and_then(|v| v.as_object())
    .expect("exports object");
  let file_exports = exports
    .get(&normalized_index)
    .and_then(|v| v.as_object())
    .expect("exports for index.ts");
  let doubled = file_exports
    .get("doubled")
    .and_then(|v| v.as_object())
    .expect("doubled export entry");
  assert!(
    doubled.get("symbol").is_some(),
    "expected doubled export to include a symbol: {doubled:?}"
  );
  assert_eq!(doubled.get("type").and_then(|v| v.as_str()), Some("number"));
}
