use assert_cmd::Command;
use std::time::Duration;

fn parse_js_cli() -> Command {
  assert_cmd::cargo::cargo_bin_cmd!("parse-js-cli")
}

#[test]
fn prints_diagnostic_on_parse_error() {
  let mut cmd = parse_js_cli();
  cmd.timeout(Duration::from_secs(5));
  let assert = cmd.write_stdin("function {").assert().failure().code(1);
  let stderr = String::from_utf8_lossy(&assert.get_output().stderr);

  assert!(stderr.contains("error[PS"));
  assert!(stderr.contains("<stdin>:1:"));
  assert!(stderr.contains('^'));
}
