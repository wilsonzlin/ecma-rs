use assert_cmd::Command;
use std::time::Duration;

fn parse_js_cli() -> Command {
  assert_cmd::cargo::cargo_bin_cmd!("parse-js-cli")
}

#[test]
fn rejects_invalid_utf8() {
  let assert = parse_js_cli()
    .timeout(Duration::from_secs(5))
    .write_stdin(vec![0xFF])
    .assert()
    .failure()
    .code(1);

  let stderr = String::from_utf8_lossy(&assert.get_output().stderr);
  assert!(
    stderr.contains("UTF-8"),
    "stderr should mention UTF-8, got: {stderr}"
  );
}
