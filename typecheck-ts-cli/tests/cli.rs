use assert_cmd::Command;
use predicates::str::{contains, is_empty};
use serde_json::Value;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use tempfile::NamedTempFile;
use typecheck_ts::resolve::normalize_path;

fn fixture(name: &str) -> PathBuf {
  Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("tests")
    .join("fixtures")
    .join(name)
}

fn normalized(path: &Path) -> String {
  normalize_path(path)
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
    .stdout(contains("unresolved import"));

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
