use assert_cmd::Command;
use predicates::str::{contains, is_empty};
use serde_json::Value;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Duration;
use tempfile::{tempdir, NamedTempFile};

const CLI_TIMEOUT: Duration = Duration::from_secs(30);

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

fn write_file(path: &Path, content: &str) {
  if let Some(parent) = path.parent() {
    fs::create_dir_all(parent).expect("create parent directories");
  }
  fs::write(path, content).expect("write fixture file");
}

#[test]
fn typecheck_succeeds_on_basic_fixture() {
  let path = fixture("basic.ts");
  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
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
    .timeout(CLI_TIMEOUT)
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
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg(path.as_os_str())
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn node_modules_resolution_is_opt_in() {
  let tmp = tempdir().expect("temp dir");
  let path = tmp.path().join("src/main.ts");
  write_file(
    &path,
    "import { value } from \"pkg\";\n\nexport const doubled = value * 2;\n",
  );
  write_file(
    &tmp.path().join("node_modules/pkg/index.ts"),
    "export const value: number = 21;\n",
  );

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg(path.as_os_str())
    .assert()
    .failure()
    .stdout(contains("unresolved module specifier"));

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg(path.as_os_str())
    .arg("--node-resolve")
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn resolves_mjs_modules_without_internal_error() {
  let tmp = tempdir().expect("temp dir");
  let entry = tmp.path().join("src/main.ts");
  write_file(
    &entry,
    "import { value } from \"pkg\";\n\nexport const doubled = value * 2;\n",
  );
  write_file(
    &tmp.path().join("node_modules/pkg/index.mjs"),
    "export const value = 21;\n",
  );

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg(entry.as_os_str())
    .arg("--node-resolve")
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn node_resolve_prefers_node_modules_over_cwd_for_package_subpaths() {
  let package_name = "typecheck-ts-cli-subpath-pkg";
  let tmp = tempdir().expect("temp dir");
  let entry = tmp.path().join("src/main.ts");
  write_file(
    &entry,
    &format!(
      "import {{ value }} from \"{package_name}/index.js\";\n\nexport const doubled = value * 2;\n"
    ),
  );
  // File that would be incorrectly resolved if the resolver treated non-relative
  // package subpaths as paths relative to the process CWD.
  write_file(
    &tmp.path().join(format!("{package_name}/index.js")),
    "export const value = 21;\n",
  );
  // The correct resolution target is the node_modules package.
  write_file(
    &tmp
      .path()
      .join(format!("node_modules/{package_name}/index.d.ts")),
    "export const value: number;\n",
  );
  let expected = tmp
    .path()
    .join(format!("node_modules/{package_name}/index.d.ts"));
  let wrong = tmp.path().join(format!("{package_name}/index.js"));

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .current_dir(tmp.path())
    .args(["typecheck"])
    .arg(entry.as_os_str())
    .arg("--node-resolve")
    .arg("--json")
    .assert()
    .success()
    .get_output()
    .stdout
    .clone();

  let json: Value = serde_json::from_slice(&output).expect("valid JSON output");
  let files: Vec<_> = json
    .get("files")
    .and_then(|f| f.as_array())
    .expect("files array")
    .iter()
    .filter_map(|v| v.as_str())
    .collect();

  assert!(
    files.contains(&normalized(&expected).as_str()),
    "expected resolution to prefer node_modules package, got {files:?}"
  );
  assert!(
    !files.contains(&normalized(&wrong).as_str()),
    "did not expect resolver to use cwd-relative file, got {files:?}"
  );
}

#[test]
fn resolves_package_json_types_entry() {
  let tmp = tempdir().expect("temp dir");
  let entry = tmp.path().join("src/main.ts");
  write_file(
    &entry,
    "import { value } from \"pkg\";\n\nexport const doubled = value * 2;\n",
  );
  write_file(
    &tmp.path().join("node_modules/pkg/package.json"),
    r#"{ "name": "pkg", "version": "1.0.0", "types": "./dist/types.d.ts" }"#,
  );
  write_file(
    &tmp.path().join("node_modules/pkg/dist/types.d.ts"),
    "export const value: number;\n",
  );

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg(entry.as_os_str())
    .arg("--node-resolve")
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn resolves_package_json_exports_types() {
  let tmp = tempdir().expect("temp dir");
  let entry = tmp.path().join("src/main.ts");
  write_file(
    &entry,
    "import { value } from \"pkg\";\n\nexport const doubled = value * 2;\n",
  );
  write_file(
    &tmp.path().join("node_modules/pkg/package.json"),
    r#"{ "name": "pkg", "version": "1.0.0", "exports": { ".": { "types": "./dist/types.d.ts" } } }"#,
  );
  write_file(
    &tmp.path().join("node_modules/pkg/dist/types.d.ts"),
    "export const value: number;\n",
  );

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg(entry.as_os_str())
    .arg("--node-resolve")
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn resolves_package_json_exports_types_without_dot_key() {
  let tmp = tempdir().expect("temp dir");
  let entry = tmp.path().join("src/main.ts");
  write_file(
    &entry,
    "import { value } from \"pkg\";\n\nexport const doubled = value * 2;\n",
  );
  write_file(
    &tmp.path().join("node_modules/pkg/package.json"),
    r#"{ "name": "pkg", "version": "1.0.0", "exports": { "types": "./dist/index.d.ts", "default": "./dist/index.js" } }"#,
  );
  write_file(
    &tmp.path().join("node_modules/pkg/dist/index.d.ts"),
    "export const value: number;\n",
  );

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg(entry.as_os_str())
    .arg("--node-resolve")
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn resolves_package_json_typings_entry() {
  let tmp = tempdir().expect("temp dir");
  let entry = tmp.path().join("src/main.ts");
  write_file(
    &entry,
    "import { value } from \"pkg\";\n\nexport const doubled = value * 2;\n",
  );
  write_file(
    &tmp.path().join("node_modules/pkg/package.json"),
    r#"{ "name": "pkg", "version": "1.0.0", "typings": "./index.d.ts" }"#,
  );
  write_file(
    &tmp.path().join("node_modules/pkg/index.d.ts"),
    "export const value: number;\n",
  );

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg(entry.as_os_str())
    .arg("--node-resolve")
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn resolves_node_modules_from_ancestor_directories() {
  let tmp = tempdir().expect("temp dir");
  let entry = tmp.path().join("src/nested/main.ts");
  write_file(
    &entry,
    "import { value } from \"pkg\";\n\nexport const doubled = value * 2;\n",
  );
  write_file(
    &tmp.path().join("node_modules/pkg/index.d.ts"),
    "export const value: number;\n",
  );

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg(entry.as_os_str())
    .arg("--node-resolve")
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn resolves_imports_specifiers_from_package_json() {
  let tmp = tempdir().expect("temp dir");
  write_file(
    &tmp.path().join("package.json"),
    r##"{ "name": "app", "imports": { "#answer": "./src/answer.ts" } }"##,
  );
  write_file(
    &tmp.path().join("src/answer.ts"),
    "export const value: number = 21;\n",
  );
  let entry = tmp.path().join("src/main.ts");
  write_file(
    &entry,
    "import { value } from \"#answer\";\n\nexport const doubled = value * 2;\n",
  );

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg(entry.as_os_str())
    .arg("--node-resolve")
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn resolves_imports_star_patterns_from_package_json() {
  let tmp = tempdir().expect("temp dir");
  write_file(
    &tmp.path().join("package.json"),
    r##"{ "name": "app", "imports": { "#*": "./src/*.ts" } }"##,
  );
  write_file(
    &tmp.path().join("src/answer.ts"),
    "export const value: number = 21;\n",
  );
  let entry = tmp.path().join("src/main.ts");
  write_file(
    &entry,
    "import { value } from \"#answer\";\n\nexport const doubled = value * 2;\n",
  );

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg(entry.as_os_str())
    .arg("--node-resolve")
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn resolves_exports_subpath_patterns_with_types_condition() {
  let tmp = tempdir().expect("temp dir");
  let entry = tmp.path().join("src/main.ts");
  write_file(
    &entry,
    "import { value } from \"pkg/answer\";\n\nexport const doubled = value * 2;\n",
  );
  write_file(
    &tmp.path().join("node_modules/pkg/package.json"),
    r#"{ "name": "pkg", "version": "1.0.0", "exports": { "./*": { "types": "./dist/*.d.ts" } } }"#,
  );
  write_file(
    &tmp.path().join("node_modules/pkg/dist/answer.d.ts"),
    "export const value: number;\n",
  );

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg(entry.as_os_str())
    .arg("--node-resolve")
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn resolves_at_types_fallback_packages() {
  let tmp = tempdir().expect("temp dir");
  let entry = tmp.path().join("src/main.ts");
  write_file(
    &entry,
    "import { value } from \"pkg\";\n\nexport const doubled = value * 2;\n",
  );
  write_file(
    &tmp.path().join("node_modules/@types/pkg/index.d.ts"),
    "export const value: number;\n",
  );

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg(entry.as_os_str())
    .arg("--node-resolve")
    .assert()
    .success()
    .stdout(is_empty());
}

#[test]
fn tsconfig_paths_patterns_prefer_most_specific_match() {
  let tmp = tempdir().expect("temp dir");
  write_file(
    &tmp.path().join("tsconfig.json"),
    r#"{ "compilerOptions": { "baseUrl": ".", "paths": { "@lib/*": ["src/lib/*"], "@lib/special/*": ["src/special/*"] } }, "files": ["src/index.ts"] }"#,
  );
  write_file(
    &tmp.path().join("src/index.ts"),
    "import { value } from \"@lib/special/answer\";\n\nexport const doubled = value * 2;\n",
  );
  write_file(
    &tmp.path().join("src/special/answer.ts"),
    "export const value: number = 21;\n",
  );
  // This file matches the less-specific mapping. If we pick it, type checking should fail.
  write_file(
    &tmp.path().join("src/lib/special/answer.ts"),
    "export const value: string = \"oops\";\n",
  );

  Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg("--project")
    .arg(tmp.path().join("tsconfig.json").as_os_str())
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
      .timeout(CLI_TIMEOUT)
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
    .timeout(CLI_TIMEOUT)
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
fn timeout_secs_cancels_typecheck() {
  let path = fixture("basic.ts");

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg("--timeout-secs")
    .arg("0")
    .arg("--json")
    .arg(path.as_os_str())
    .assert()
    .failure()
    .get_output()
    .stdout
    .clone();

  let json: Value = serde_json::from_slice(&output).expect("valid JSON output");
  let diagnostics = json
    .get("diagnostics")
    .and_then(|d| d.as_array())
    .expect("diagnostics array");
  assert!(
    diagnostics.iter().any(|d| {
      d.get("code")
        .and_then(|c| c.as_str())
        .is_some_and(|code| code == "CANCEL0001")
    }),
    "expected cancellation diagnostic in output, got {json:?}"
  );
}

#[test]
fn project_mode_discovers_files_and_resolves_paths() {
  let tsconfig = fixture("project_mode/basic/tsconfig.json");
  let index = fixture("project_mode/basic/src/index.ts");
  let answer = fixture("project_mode/basic/src/lib/answer.ts");
  let unused = fixture("project_mode/basic/src/unused.ts");
  let ignored = fixture("project_mode/basic/bower_components/ignored/index.ts");

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
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
  let tsconfig = fixture("project_mode/basic/tsconfig.json");
  let index = fixture("project_mode/basic/src/index.ts");
  let normalized_index = normalized(&index);
  let content = fs::read_to_string(&index).expect("read index.ts");
  let offset = content
    .find("answer * 2")
    .map(|idx| idx as u32)
    .expect("offset for answer * 2");
  let query = format!("{}:{}", index.display(), offset);

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
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

#[test]
fn project_mode_honors_include_exclude_patterns() {
  let project_dir = fixture("project_mode/file_discovery");
  let included_a = fixture("project_mode/file_discovery/src/included_a.ts");
  let included_b = fixture("project_mode/file_discovery/src/included_b.ts");
  let only = fixture("project_mode/file_discovery/src/only.ts");
  let extra = fixture("project_mode/file_discovery/src/extra.ts");
  let excluded = fixture("project_mode/file_discovery/src/excluded.ts");
  let outside = fixture("project_mode/file_discovery/other/outside.ts");

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg("--project")
    .arg(project_dir.as_os_str())
    .arg("--json")
    .assert()
    .success()
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

  assert!(files.contains(&normalized(&included_a).as_str()));
  assert!(files.contains(&normalized(&included_b).as_str()));
  assert!(files.contains(&normalized(&only).as_str()));
  assert!(files.contains(&normalized(&extra).as_str()));
  assert!(
    !files.contains(&normalized(&excluded).as_str()),
    "expected excluded.ts to be excluded, got {files:?}"
  );
  assert!(
    !files.contains(&normalized(&outside).as_str()),
    "expected outside.ts to be excluded by include pattern, got {files:?}"
  );
}

#[test]
fn project_mode_honors_files_list_over_include() {
  let tsconfig = fixture("project_mode/file_discovery/tsconfig.files.json");
  let only = fixture("project_mode/file_discovery/src/only.ts");
  let extra = fixture("project_mode/file_discovery/src/extra.ts");

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg("--project")
    .arg(tsconfig.as_os_str())
    .arg("--json")
    .assert()
    .success()
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

  assert!(files.contains(&normalized(&only).as_str()));
  assert!(
    !files.contains(&normalized(&extra).as_str()),
    "expected extra.ts to be omitted when using files list, got {files:?}"
  );
}

#[test]
fn project_mode_merges_compiler_options_from_extends() {
  let inherit = fixture("project_mode/extends_merge/tsconfig.inherit.json");
  let override_config = fixture("project_mode/extends_merge/tsconfig.override.json");

  let inherit_out = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg("--project")
    .arg(inherit.as_os_str())
    .arg("--json")
    .assert()
    .failure()
    .get_output()
    .stdout
    .clone();
  let inherit_json: Value =
    serde_json::from_slice(&inherit_out).expect("valid JSON output for inherit config");
  let inherit_diags = inherit_json
    .get("diagnostics")
    .and_then(|d| d.as_array())
    .expect("diagnostics array");
  assert!(
    inherit_diags
      .iter()
      .any(|d| d.get("code").and_then(|c| c.as_str()) == Some("TC3000")),
    "expected noImplicitAny error from strict base config, got {inherit_diags:?}"
  );
  assert!(
    inherit_diags
      .iter()
      .any(|d| d.get("code").and_then(|c| c.as_str()) == Some("TC0007")),
    "expected strictNullChecks assignment error from strict base config, got {inherit_diags:?}"
  );

  let override_out = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg("--project")
    .arg(override_config.as_os_str())
    .arg("--json")
    .assert()
    .success()
    .get_output()
    .stdout
    .clone();
  let override_json: Value =
    serde_json::from_slice(&override_out).expect("valid JSON output for override config");
  let override_diags = override_json
    .get("diagnostics")
    .and_then(|d| d.as_array())
    .expect("diagnostics array");
  assert!(
    override_diags.is_empty(),
    "expected overrides to suppress strict diagnostics, got {override_diags:?}"
  );
}

#[test]
fn project_mode_uses_module_resolution_from_tsconfig() {
  let tsconfig = fixture("project_mode/module_resolution/tsconfig.json");

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg("--project")
    .arg(tsconfig.as_os_str())
    .arg("--json")
    .assert()
    .success()
    .get_output()
    .stdout
    .clone();

  let json: Value = serde_json::from_slice(&output).expect("valid JSON output");
  let diagnostics = json
    .get("diagnostics")
    .and_then(|d| d.as_array())
    .expect("diagnostics array");
  assert!(
    diagnostics.is_empty(),
    "expected moduleResolution Node16 to enable node_modules resolution, got {diagnostics:?}"
  );
}

#[test]
fn project_mode_resolves_types_and_type_roots() {
  let tsconfig = fixture("project_mode/types/tsconfig.json");
  let foo = fixture("project_mode/types/node_modules/@types/foo/index.d.ts");
  let bar = fixture("project_mode/types/node_modules/@types/bar/index.d.ts");

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg("--project")
    .arg(tsconfig.as_os_str())
    .arg("--json")
    .assert()
    .failure()
    .get_output()
    .stdout
    .clone();

  let json: Value = serde_json::from_slice(&output).expect("valid JSON output");
  let files: Vec<_> = json
    .get("files")
    .and_then(|f| f.as_array())
    .expect("files array")
    .iter()
    .filter_map(|v| v.as_str())
    .collect();
  assert!(files.contains(&normalized(&foo).as_str()));
  assert!(
    !files.contains(&normalized(&bar).as_str()),
    "expected 'types' list to exclude bar, got {files:?}"
  );

  let diagnostics = json
    .get("diagnostics")
    .and_then(|d| d.as_array())
    .expect("diagnostics array");
  assert!(
    diagnostics.iter().any(|d| {
      d.get("code").and_then(|c| c.as_str()) == Some("TC0005")
        && d
          .get("message")
          .and_then(|m| m.as_str())
          .is_some_and(|m| m.contains("BarGlobal"))
    }),
    "expected missing BarGlobal due to types filtering, got {diagnostics:?}"
  );
  assert!(
    !diagnostics.iter().any(|d| {
      d.get("message")
        .and_then(|m| m.as_str())
        .is_some_and(|m| m.contains("FooGlobal"))
    }),
    "did not expect FooGlobal errors, got {diagnostics:?}"
  );
}

#[test]
fn project_mode_accepts_full_ts_lib_names() {
  let tsconfig = fixture("project_mode/lib_names/tsconfig.json");
  let main = fixture("project_mode/lib_names/src/main.ts");

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg("--project")
    .arg(tsconfig.as_os_str())
    .arg("--json")
    .assert()
    .success()
    .get_output()
    .stdout
    .clone();

  let json: Value = serde_json::from_slice(&output).expect("valid JSON output");
  let files: Vec<_> = json
    .get("files")
    .and_then(|f| f.as_array())
    .expect("files array")
    .iter()
    .filter_map(|v| v.as_str())
    .collect();
  assert!(
    files.contains(&normalized(&main).as_str()),
    "expected program to include main.ts, got {files:?}"
  );
}

#[test]
fn project_mode_resolves_scoped_types_packages() {
  let tsconfig = fixture("project_mode/types_scoped/tsconfig.json");
  let main = fixture("project_mode/types_scoped/src/main.ts");
  let dts = fixture("project_mode/types_scoped/node_modules/@types/scope__pkg/index.d.ts");

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg("--project")
    .arg(tsconfig.as_os_str())
    .arg("--json")
    .assert()
    .success()
    .get_output()
    .stdout
    .clone();

  let json: Value = serde_json::from_slice(&output).expect("valid JSON output");
  let files: Vec<_> = json
    .get("files")
    .and_then(|f| f.as_array())
    .expect("files array")
    .iter()
    .filter_map(|v| v.as_str())
    .collect();

  assert!(files.contains(&normalized(&main).as_str()));
  assert!(
    files.contains(&normalized(&dts).as_str()),
    "expected scoped @types package to be loaded, got {files:?}"
  );

  let diagnostics = json
    .get("diagnostics")
    .and_then(|d| d.as_array())
    .expect("diagnostics array");
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics when scoped types package is resolved, got {diagnostics:?}"
  );
}

#[test]
fn project_mode_applies_jsx_import_source_types() {
  let tsconfig = fixture("project_mode/jsx_import_source/tsconfig.json");
  let main = fixture("project_mode/jsx_import_source/src/main.tsx");
  let dts = fixture("project_mode/jsx_import_source/node_modules/@types/foo/index.d.ts");

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg("--project")
    .arg(tsconfig.as_os_str())
    .arg("--json")
    .assert()
    .success()
    .get_output()
    .stdout
    .clone();

  let json: Value = serde_json::from_slice(&output).expect("valid JSON output");
  let files: Vec<_> = json
    .get("files")
    .and_then(|f| f.as_array())
    .expect("files array")
    .iter()
    .filter_map(|v| v.as_str())
    .collect();

  assert!(files.contains(&normalized(&main).as_str()));
  assert!(
    files.contains(&normalized(&dts).as_str()),
    "expected jsxImportSource package to be loaded as a type library, got {files:?}"
  );

  let diagnostics = json
    .get("diagnostics")
    .and_then(|d| d.as_array())
    .expect("diagnostics array");
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.get("code").and_then(|c| c.as_str()) == Some("TC3003")),
    "did not expect missing JSX namespace diagnostics, got {diagnostics:?}"
  );
}

#[test]
fn project_mode_discovers_mts_files() {
  let tsconfig = fixture("project_mode/mts_files/tsconfig.json");
  let main = fixture("project_mode/mts_files/src/main.mts");

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg("--project")
    .arg(tsconfig.as_os_str())
    .arg("--json")
    .assert()
    .success()
    .get_output()
    .stdout
    .clone();

  let json: Value = serde_json::from_slice(&output).expect("valid JSON output");
  let files: Vec<_> = json
    .get("files")
    .and_then(|f| f.as_array())
    .expect("files array")
    .iter()
    .filter_map(|v| v.as_str())
    .collect();

  assert!(
    files.contains(&normalized(&main).as_str()),
    "expected project mode to include main.mts, got {files:?}"
  );
}

#[test]
fn project_mode_resolves_paths_relative_to_extended_config() {
  let tsconfig = fixture("project_mode/extends_basedir/tsconfig.json");

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg("--project")
    .arg(tsconfig.as_os_str())
    .arg("--json")
    .assert()
    .success()
    .get_output()
    .stdout
    .clone();

  let json: Value = serde_json::from_slice(&output).expect("valid JSON output");
  let diagnostics = json
    .get("diagnostics")
    .and_then(|d| d.as_array())
    .expect("diagnostics array");
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.get("code").and_then(|c| c.as_str()) == Some("TC1001")),
    "expected @lib/ paths from extended config to resolve, got {diagnostics:?}"
  );
}

#[test]
fn project_mode_uses_include_from_extended_config() {
  let tsconfig = fixture("project_mode/extends_include/tsconfig.json");
  let main = fixture("project_mode/extends_include/src/main.ts");

  let output = Command::cargo_bin("typecheck-ts-cli")
    .unwrap()
    .timeout(CLI_TIMEOUT)
    .args(["typecheck"])
    .arg("--project")
    .arg(tsconfig.as_os_str())
    .arg("--json")
    .assert()
    .success()
    .get_output()
    .stdout
    .clone();

  let json: Value = serde_json::from_slice(&output).expect("valid JSON output");
  let files: Vec<_> = json
    .get("files")
    .and_then(|f| f.as_array())
    .expect("files array")
    .iter()
    .filter_map(|v| v.as_str())
    .collect();
  assert!(
    files.contains(&normalized(&main).as_str()),
    "expected include from extended config to include main.ts, got {files:?}"
  );
}
