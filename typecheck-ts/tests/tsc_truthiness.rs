use std::fs;
use std::io::Read;
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

#[derive(Debug)]
enum CommandOutcome {
  SpawnFailed,
  TimedOut,
  Output(Output),
}

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

fn output_with_timeout(mut command: Command, timeout: Duration) -> CommandOutcome {
  command.stdin(Stdio::null());
  command.stdout(Stdio::piped());
  command.stderr(Stdio::piped());
  let mut child = match command.spawn() {
    Ok(child) => child,
    Err(_) => return CommandOutcome::SpawnFailed,
  };

  let mut stdout = child.stdout.take().unwrap();
  let mut stderr = child.stderr.take().unwrap();
  let deadline = Instant::now() + timeout;

  loop {
    match child.try_wait() {
      Ok(Some(status)) => {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let _ = stdout.read_to_end(&mut out);
        let _ = stderr.read_to_end(&mut err);
        return CommandOutcome::Output(Output {
          status,
          stdout: out,
          stderr: err,
        });
      }
      Ok(None) => {
        if Instant::now() >= deadline {
          let _ = child.kill();
          let _ = reap_child_with_timeout(&mut child, Duration::from_millis(200));
          return CommandOutcome::TimedOut;
        }
        std::thread::sleep(Duration::from_millis(10));
      }
      Err(_) => return CommandOutcome::SpawnFailed,
    }
  }
}

#[test]
fn tsc_truthiness_baseline() {
  let mut version_cmd = Command::new("tsc");
  version_cmd.arg("--version");
  let version = output_with_timeout(version_cmd, Duration::from_secs(5));
  let version = match version {
    CommandOutcome::Output(output) => output,
    CommandOutcome::SpawnFailed => {
      eprintln!("skipping truthiness baseline: tsc not available");
      return;
    }
    CommandOutcome::TimedOut => {
      eprintln!("skipping truthiness baseline: tsc --version timed out");
      return;
    }
  };
  if !version.status.success() {
    eprintln!("skipping truthiness baseline: tsc not available");
    return;
  };

  let ts = r#"
function stringNull(x: string | null) {
  if (x) {
    const ok: string = x;
  } else {
    // @ts-expect-error string is still possible here
    const onlyNull: null = x;
  }
}

function primitiveMaybes(x: string | undefined, y: number | null, z: bigint | null) {
  if (x) {
    const ok: string = x;
  } else {
    // @ts-expect-error string is still possible here
    const onlyUndefined: undefined = x;
  }

  if (y) {
    const ok: number = y;
  } else {
    // @ts-expect-error number is still possible here
    const onlyNull: null = y;
  }

  if (z) {
    const ok: bigint = z;
  } else {
    // @ts-expect-error bigint is still possible here
    const onlyNull: null = z;
  }
}

function genericTruthiness<T>(value: T) {
  if (value) {
    const ok: T = value;
  } else {
    // @ts-expect-error T still flows to the falsy branch
    const impossible: never = value;
  }
}

function falsyLiterals(x: "" | "a", y: 0 | 1, z: 0n | 1n) {
  if (x) {
    const onlyA: "a" = x;
  } else {
    const empty: "" = x;
  }

  if (y) {
    const one: 1 = y;
  } else {
    const zero: 0 = y;
  }

  if (z) {
    const one: 1n = z;
  } else {
    const zero: 0n = z;
  }
}
  "#;

  let mut path = std::env::temp_dir();
  let unique = SystemTime::now()
    .duration_since(UNIX_EPOCH)
    .unwrap_or_default()
    .as_nanos();
  path.push(format!("ts_truthiness_{unique}.ts"));
  fs::write(&path, ts).expect("write temp ts file");

  let mut tsc_cmd = Command::new("tsc");
  tsc_cmd
    .args(["--pretty", "false", "--strict", "--noEmit"])
    .arg(&path);
  let output = output_with_timeout(tsc_cmd, Duration::from_secs(30));

  let _ = fs::remove_file(&path);

  let output = match output {
    CommandOutcome::Output(output) => output,
    CommandOutcome::SpawnFailed => {
      eprintln!("skipping truthiness baseline: tsc not available");
      return;
    }
    CommandOutcome::TimedOut => {
      eprintln!("skipping truthiness baseline: tsc invocation timed out");
      return;
    }
  };

  assert!(
    output.status.success(),
    "tsc truthiness baseline failed: {}\nstdout:\n{}\nstderr:\n{}",
    output.status,
    String::from_utf8_lossy(&output.stdout),
    String::from_utf8_lossy(&output.stderr)
  );
}
