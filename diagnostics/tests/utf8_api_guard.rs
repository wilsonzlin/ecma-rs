use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

fn reap_child_with_timeout(
  child: &mut std::process::Child,
  timeout: Duration,
) -> std::io::Result<Option<std::process::ExitStatus>> {
  let deadline = Instant::now() + timeout;
  loop {
    match child.try_wait()? {
      Some(status) => return Ok(Some(status)),
      None => {
        if Instant::now() >= deadline {
          return Ok(None);
        }
        std::thread::sleep(Duration::from_millis(10));
      }
    }
  }
}

fn output_with_timeout(mut command: Command, timeout: Duration) -> std::io::Result<Option<Output>> {
  command.stdin(Stdio::null());
  command.stdout(Stdio::piped());
  command.stderr(Stdio::piped());

  let mut child = command.spawn()?;
  let mut stdout = child.stdout.take().expect("child stdout");
  let mut stderr = child.stderr.take().expect("child stderr");
  let deadline = Instant::now() + timeout;
  loop {
    match child.try_wait()? {
      Some(status) => {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let _ = stdout.read_to_end(&mut out);
        let _ = stderr.read_to_end(&mut err);
        return Ok(Some(Output {
          status,
          stdout: out,
          stderr: err,
        }));
      }
      None => {
        if Instant::now() >= deadline {
          let _ = child.kill();
          let _ = reap_child_with_timeout(&mut child, Duration::from_millis(200));
          return Ok(None);
        }
        std::thread::sleep(Duration::from_millis(10));
      }
    }
  }
}

#[test]
fn public_source_apis_use_utf8() {
  // Guard against new public APIs that take raw byte slices or Vec<u8> for
  // source text. Fuzz entry points are allowed; see
  // `scripts/check_utf8_apis.sh` for the exact pattern this enforces.
  let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
  let repo_root = manifest_dir.parent().expect("workspace root").to_path_buf();
  let script = repo_root.join("scripts").join("check_utf8_apis.sh");

  let mut command = Command::new(&script);
  command.current_dir(&repo_root);
  let output = output_with_timeout(command, Duration::from_secs(10))
    .expect("run check_utf8_apis.sh")
    .expect("check_utf8_apis.sh timed out");
  if !output.status.success() {
    panic!(
      "UTF-8 API guard failed ({}):\nstdout:\n{}\nstderr:\n{}",
      output.status,
      String::from_utf8_lossy(&output.stdout),
      String::from_utf8_lossy(&output.stderr)
    );
  }
}
