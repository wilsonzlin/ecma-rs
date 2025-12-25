use std::path::Path;
use std::process::Command;

#[test]
fn public_api_source_text_is_utf8() {
  let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
    .parent()
    .expect("workspace root");
  let script = repo_root.join("scripts").join("check_utf8_apis.sh");

  assert!(
    script.is_file(),
    "UTF-8 API guard script is missing at {}",
    script.display()
  );

  let output = Command::new(&script)
    .output()
    .unwrap_or_else(|err| panic!("failed to run {}: {err}", script.display()));

  assert!(
    output.status.success(),
    "UTF-8 API check failed.\nstdout:\n{}\nstderr:\n{}",
    String::from_utf8_lossy(&output.stdout),
    String::from_utf8_lossy(&output.stderr)
  );
}
