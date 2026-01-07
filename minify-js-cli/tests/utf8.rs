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

fn run_minify(args: &[&str], input: &[u8]) -> Output {
  let bin = binary_path();
  let mut child = Command::new(bin)
    .args(args)
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .expect("spawn minify-js");

  {
    let mut stdin = child.stdin.take().expect("child stdin");
    stdin.write_all(input).expect("write stdin");
  }

  wait_with_output_timeout(child, Duration::from_secs(5))
    .expect("wait for output")
    .expect("minify-js timed out")
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

#[test]
fn dialect_js_rejects_typescript_syntax() {
  let source = br#"
    let y = 1;
    let x = <number>y;
    console.log(x);
  "#;

  let output = run_minify(&["--mode", "global"], source);
  assert!(
    output.status.success(),
    "expected minify-js to succeed in default dialect, got status: {:?}, stderr: {}",
    output.status,
    String::from_utf8_lossy(&output.stderr)
  );

  let output = run_minify(&["--mode", "global", "--dialect", "js"], source);
  assert!(
    !output.status.success(),
    "expected minify-js to reject TS angle-bracket assertions in JS dialect"
  );
}

#[test]
fn lowering_class_fields_changes_output() {
  let source = br#"
    class C {
      foo: number = 1;
    }
    new C();
  "#;

  let base = run_minify(&["--mode", "global"], source);
  assert!(
    base.status.success(),
    "expected minify-js to succeed, got status: {:?}, stderr: {}",
    base.status,
    String::from_utf8_lossy(&base.stderr)
  );
  let base_out = String::from_utf8_lossy(&base.stdout);
  assert!(
    base_out.contains("foo=1"),
    "expected output to preserve class field when lowering is disabled, got: {}",
    base_out
  );

  let lowered = run_minify(&["--mode", "global", "--ts-lower-class-fields"], source);
  assert!(
    lowered.status.success(),
    "expected minify-js to succeed with --ts-lower-class-fields, got status: {:?}, stderr: {}",
    lowered.status,
    String::from_utf8_lossy(&lowered.stderr)
  );
  let lowered_out = String::from_utf8_lossy(&lowered.stdout);
  assert_ne!(
    base_out, lowered_out,
    "expected output to differ when lowering class fields"
  );
  assert!(
    lowered_out.contains("defineProperty"),
    "expected lowered output to contain Object.defineProperty call, got: {}",
    lowered_out
  );
}

#[test]
fn preserve_const_enums_changes_output() {
  let source = br#"eval("x");const enum E{A=1}export const x=E.A;"#;

  let inlined = run_minify(&["--mode", "module"], source);
  assert!(
    inlined.status.success(),
    "expected minify-js to succeed, got status: {:?}, stderr: {}",
    inlined.status,
    String::from_utf8_lossy(&inlined.stderr)
  );
  let inlined_out = String::from_utf8_lossy(&inlined.stdout);
  assert!(
    inlined_out.contains("export const x=1"),
    "expected const enum member access to be inlined by default, got: {}",
    inlined_out
  );
  assert!(
    !inlined_out.contains("var E"),
    "expected const enum declaration to be erased by default, got: {}",
    inlined_out
  );

  let preserved = run_minify(&["--mode", "module", "--preserve-const-enums"], source);
  assert!(
    preserved.status.success(),
    "expected minify-js to succeed with --preserve-const-enums, got status: {:?}, stderr: {}",
    preserved.status,
    String::from_utf8_lossy(&preserved.stderr)
  );
  let preserved_out = String::from_utf8_lossy(&preserved.stdout);
  assert!(
    preserved_out.contains("var E"),
    "expected preserve mode to emit runtime enum scaffolding, got: {}",
    preserved_out
  );
  assert!(
    preserved_out.contains("export const x=E.A"),
    "expected preserve mode to keep enum member access, got: {}",
    preserved_out
  );

  // Legacy flag (kept as an alias) should behave the same.
  let legacy = run_minify(&["--mode", "module", "--ts-preserve-const-enums"], source);
  assert!(
    legacy.status.success(),
    "expected minify-js to succeed with --ts-preserve-const-enums, got status: {:?}, stderr: {}",
    legacy.status,
    String::from_utf8_lossy(&legacy.stderr)
  );
  assert_eq!(String::from_utf8_lossy(&legacy.stdout), preserved_out);
}
