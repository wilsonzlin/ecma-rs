use assert_cmd::Command;

#[test]
fn prints_diagnostic_on_parse_error() {
  #[allow(deprecated)]
  let mut cmd = Command::cargo_bin("parse-js-cli").expect("binary");
  let assert = cmd.write_stdin("function {").assert().failure().code(1);
  let stderr = String::from_utf8_lossy(&assert.get_output().stderr);

  assert!(stderr.contains("error[PS"));
  assert!(stderr.contains("<stdin>:1:"));
  assert!(stderr.contains('^'));
}
