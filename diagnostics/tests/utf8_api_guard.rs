use std::path::PathBuf;
use std::process::Command;

#[test]
fn public_source_apis_use_utf8() {
  // Guard against new public APIs that take raw byte slices or Vec<u8> for
  // source text. Fuzz entry points are allowed; see
  // `scripts/check_utf8_apis.sh` for the exact pattern this enforces.
  let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
  let repo_root = manifest_dir.parent().expect("workspace root").to_path_buf();
  let script = repo_root.join("scripts").join("check_utf8_apis.sh");

  let output = Command::new(&script)
    .current_dir(&repo_root)
    .output()
    .expect("run check_utf8_apis.sh");
  if !output.status.success() {
    panic!(
      "UTF-8 API guard failed ({}):\nstdout:\n{}\nstderr:\n{}",
      output.status,
      String::from_utf8_lossy(&output.stdout),
      String::from_utf8_lossy(&output.stderr)
    );
  }
}
