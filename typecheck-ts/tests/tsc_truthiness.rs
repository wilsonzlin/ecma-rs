use std::fs;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn tsc_truthiness_baseline() {
  let version = Command::new("tsc").arg("--version").output();
  let Ok(version) = version else {
    eprintln!("skipping truthiness baseline: tsc not available");
    return;
  };
  if !version.status.success() {
    eprintln!("skipping truthiness baseline: tsc unusable");
    return;
  }

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

  let output = Command::new("tsc")
    .args(["--pretty", "false", "--strict", "--noEmit"])
    .arg(&path)
    .output()
    .expect("run tsc");

  let _ = fs::remove_file(&path);

  assert!(
    output.status.success(),
    "tsc truthiness baseline failed: {}\nstdout:\n{}\nstderr:\n{}",
    output.status,
    String::from_utf8_lossy(&output.stdout),
    String::from_utf8_lossy(&output.stderr)
  );
}
