use std::io::Read;
use std::io::Write;
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

fn wait_with_output_timeout(
  mut child: std::process::Child,
  timeout: Duration,
) -> std::io::Result<Option<Output>> {
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

fn binary_path() -> String {
  let names = ["minify-js", "minify-js-cli"];
  for name in names {
    for key in [
      format!("CARGO_BIN_EXE_{name}"),
      format!("CARGO_BIN_EXE_{}", name.replace('-', "_")),
    ] {
      if let Ok(path) = std::env::var(&key) {
        return path;
      }
    }
  }

  let target_dir = std::env::var("CARGO_TARGET_DIR")
    .map(PathBuf::from)
    .unwrap_or_else(|_| {
      PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("target")
    });
  for name in names {
    let candidate = target_dir.join("debug").join(name);
    if candidate.exists() {
      return candidate.display().to_string();
    }
  }

  let available: Vec<(String, String)> = std::env::vars()
    .filter(|(k, _)| k.contains("CARGO_BIN_EXE"))
    .collect();
  panic!(
    "binary path not set; available CARGO_BIN_EXE vars: {:?}",
    available
  );
}

#[test]
fn rejects_invalid_utf8_input() {
  // Locate the built binary (either via Cargo-provided vars or the default target path).
  let bin = binary_path();

  let mut child = Command::new(bin)
    .arg("--mode")
    .arg("global")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .expect("spawn minify-js");

  {
    let mut stdin = child.stdin.take().expect("child stdin");
    stdin.write_all(&[0xFF]).expect("write invalid utf-8");
  }

  let output = wait_with_output_timeout(child, Duration::from_secs(5))
    .expect("wait for output")
    .expect("minify-js timed out");
  assert!(!output.status.success(), "expected non-zero exit status");
  let stderr = String::from_utf8_lossy(&output.stderr);
  assert!(
    stderr.contains("UTF-8"),
    "stderr should mention UTF-8 error, got: {}",
    stderr
  );
}
