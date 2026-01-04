use assert_cmd::Command;
use std::time::Duration;

fn parse_js_cli() -> Command {
  assert_cmd::cargo::cargo_bin_cmd!("parse-js-cli")
}

#[test]
fn timeout_flag_cancels_parsing() {
  let assert = parse_js_cli()
    .timeout(Duration::from_secs(5))
    .arg("--timeout-secs")
    .arg("0")
    .write_stdin("const x = 1;")
    .assert()
    .failure()
    .code(1);

  let stderr = String::from_utf8_lossy(&assert.get_output().stderr);
  assert!(
    stderr.contains("PS0016"),
    "expected cancellation diagnostic code in stderr, got: {stderr}"
  );
  assert!(
    stderr.contains("timed out after 0 seconds"),
    "expected timeout note in stderr, got: {stderr}"
  );
}
