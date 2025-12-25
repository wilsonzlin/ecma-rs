use assert_cmd::Command;
use predicates::str::is_empty;
use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};

fn fixture(name: &str) -> PathBuf {
  Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("tests")
    .join("fixtures")
    .join(name)
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
    stdout.contains(&format!("type at {}:{}", path.display(), offset)),
    "missing type-at header in output: {stdout:?}"
  );
  assert!(
    stdout.contains("number"),
    "expected number type in output, got {stdout:?}"
  );
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
