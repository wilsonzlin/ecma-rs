use std::path::PathBuf;
use std::process::Command;

#[test]
fn public_source_apis_use_utf8() {
  let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .parent()
    .expect("workspace root")
    .to_path_buf();
  let script = repo_root.join("scripts/check_utf8_apis.sh");
  let output = Command::new("bash")
    .arg(&script)
    .output()
    .expect("failed to run UTF-8 API guard script");
  if !output.status.success() {
    panic!(
      "UTF-8 API guard failed: {}\nstdout:\n{}\nstderr:\n{}",
      output.status,
      String::from_utf8_lossy(&output.stdout),
      String::from_utf8_lossy(&output.stderr)
    );
  }
}
