use assert_cmd::Command;
use std::time::Duration;

fn minify_js_cli() -> Command {
  assert_cmd::cargo::cargo_bin_cmd!("minify-js-cli")
}

#[test]
fn rejects_invalid_utf8_input() {
  let assert = minify_js_cli()
    .timeout(Duration::from_secs(5))
    .arg("--mode")
    .arg("global")
    .write_stdin(vec![0xFF])
    .assert()
    .failure()
    .code(1);

  let stderr = String::from_utf8_lossy(&assert.get_output().stderr);
  assert!(
    stderr.contains("UTF-8"),
    "stderr should mention UTF-8 error, got: {stderr}"
  );
}

#[test]
fn dialect_js_rejects_typescript_syntax() {
  let source = r#"
    let y = 1;
    let x = <number>y;
    console.log(x);
  "#;

  minify_js_cli()
    .timeout(Duration::from_secs(5))
    .arg("--mode")
    .arg("global")
    .write_stdin(source)
    .assert()
    .success()
    .code(0);

  minify_js_cli()
    .timeout(Duration::from_secs(5))
    .arg("--mode")
    .arg("global")
    .arg("--dialect")
    .arg("js")
    .write_stdin(source)
    .assert()
    .failure()
    .code(1);
}

#[test]
fn lowering_class_fields_changes_output() {
  let source = r#"
    class C {
      foo: number = 1;
    }
    new C();
  "#;

  let base = minify_js_cli()
    .timeout(Duration::from_secs(5))
    .arg("--mode")
    .arg("global")
    .write_stdin(source)
    .assert()
    .success()
    .code(0);
  let base_out = String::from_utf8_lossy(&base.get_output().stdout).into_owned();
  assert!(
    base_out.contains("foo=1"),
    "expected output to preserve class field when lowering is disabled, got: {base_out}"
  );

  let lowered = minify_js_cli()
    .timeout(Duration::from_secs(5))
    .arg("--mode")
    .arg("global")
    .arg("--ts-lower-class-fields")
    .write_stdin(source)
    .assert()
    .success()
    .code(0);
  let lowered_out = String::from_utf8_lossy(&lowered.get_output().stdout).into_owned();
  assert_ne!(
    base_out, lowered_out,
    "expected output to differ when lowering class fields"
  );
  assert!(
    lowered_out.contains("defineProperty"),
    "expected lowered output to contain Object.defineProperty call, got: {lowered_out}"
  );
}

#[test]
fn preserve_const_enums_changes_output() {
  let source = r#"eval("x");const enum E{A=1}export const x=E.A;"#;

  let inlined = minify_js_cli()
    .timeout(Duration::from_secs(5))
    .arg("--mode")
    .arg("module")
    .write_stdin(source)
    .assert()
    .success()
    .code(0);
  let inlined_out = String::from_utf8_lossy(&inlined.get_output().stdout).into_owned();
  assert!(
    inlined_out.contains("export const x=1"),
    "expected const enum member access to be inlined by default, got: {inlined_out}"
  );
  assert!(
    !inlined_out.contains("var E"),
    "expected const enum declaration to be erased by default, got: {inlined_out}"
  );

  let preserved = minify_js_cli()
    .timeout(Duration::from_secs(5))
    .arg("--mode")
    .arg("module")
    .arg("--preserve-const-enums")
    .write_stdin(source)
    .assert()
    .success()
    .code(0);
  let preserved_out = String::from_utf8_lossy(&preserved.get_output().stdout).into_owned();
  assert!(
    preserved_out.contains("var E"),
    "expected preserve mode to emit runtime enum scaffolding, got: {preserved_out}"
  );
  assert!(
    preserved_out.contains("export const x=E.A"),
    "expected preserve mode to keep enum member access, got: {preserved_out}"
  );

  // Legacy flag (kept as an alias) should behave the same.
  let legacy = minify_js_cli()
    .timeout(Duration::from_secs(5))
    .arg("--mode")
    .arg("module")
    .arg("--ts-preserve-const-enums")
    .write_stdin(source)
    .assert()
    .success()
    .code(0);
  assert_eq!(
    String::from_utf8_lossy(&legacy.get_output().stdout),
    preserved_out
  );
}

