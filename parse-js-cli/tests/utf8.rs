use assert_cmd::Command;

#[test]
fn rejects_invalid_utf8() {
  #[allow(deprecated)]
  let assert = Command::cargo_bin("parse-js-cli")
    .expect("binary")
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
