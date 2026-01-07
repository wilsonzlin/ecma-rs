use assert_cmd::Command;
use std::time::Duration;

fn minify_js_cli() -> Command {
  assert_cmd::cargo::cargo_bin_cmd!("minify-js-cli")
}

#[test]
fn human_mode_writes_output_to_stdout() {
  let assert = minify_js_cli()
    .timeout(Duration::from_secs(5))
    .arg("--mode")
    .arg("global")
    .write_stdin("let x = 1;")
    .assert()
    .success()
    .code(0);

  assert_eq!(
    String::from_utf8_lossy(&assert.get_output().stdout),
    "let x=1;"
  );
  assert!(
    assert.get_output().stderr.is_empty(),
    "expected stderr to be empty, got: {}",
    String::from_utf8_lossy(&assert.get_output().stderr)
  );
}

#[test]
fn human_mode_writes_diagnostics_to_stderr() {
  let assert = minify_js_cli()
    .timeout(Duration::from_secs(5))
    .arg("--mode")
    .arg("global")
    .write_stdin("function {")
    .assert()
    .failure()
    .code(1);

  assert!(
    assert.get_output().stdout.is_empty(),
    "expected stdout to be empty, got: {}",
    String::from_utf8_lossy(&assert.get_output().stdout)
  );
  assert!(
    !assert.get_output().stderr.is_empty(),
    "expected stderr to contain diagnostics"
  );
}
