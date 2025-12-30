#[cfg(not(feature = "with-node"))]
use anyhow::anyhow;
#[cfg(feature = "with-node")]
use anyhow::bail;
#[cfg(feature = "with-node")]
use anyhow::Context;
use serde::Deserialize;
use serde::Serialize;
use serde_json::Map;
use serde_json::Value;
use std::collections::HashMap;
#[cfg(feature = "with-node")]
use std::io::BufRead;
#[cfg(feature = "with-node")]
use std::io::BufReader;
#[cfg(feature = "with-node")]
use std::io::BufWriter;
#[cfg(feature = "with-node")]
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TscRequest {
  pub root_names: Vec<String>,
  pub files: HashMap<String, String>,
  #[serde(default)]
  pub options: Map<String, Value>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub type_queries: Vec<TypeQuery>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct TypeQuery {
  pub file: String,
  pub offset: u32,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub line: Option<u32>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub column: Option<u32>,
}

pub const TSC_BASELINE_SCHEMA_VERSION: u32 = 2;
/// Merge default tsc options used by the harness with a provided options map.
pub fn apply_default_tsc_options(options: &mut Map<String, Value>) {
  options
    .entry("noEmit".to_string())
    .or_insert(Value::Bool(true));
  options
    .entry("skipLibCheck".to_string())
    .or_insert(Value::Bool(true));
  options
    .entry("pretty".to_string())
    .or_insert(Value::Bool(false));
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TscDiagnostics {
  #[serde(default, alias = "schemaVersion")]
  pub schema_version: Option<u32>,
  #[serde(default)]
  pub metadata: TscMetadata,
  pub diagnostics: Vec<TscDiagnostic>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub crash: Option<TscCrash>,
  #[serde(default, alias = "typeFacts", skip_serializing_if = "Option::is_none")]
  pub type_facts: Option<TypeFacts>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct TscMetadata {
  #[serde(default, alias = "typescriptVersion")]
  pub typescript_version: Option<String>,
  #[serde(default)]
  pub options: Map<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TscCrash {
  pub message: String,
  pub stack: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TscDiagnostic {
  pub code: u32,
  pub file: Option<String>,
  pub start: u32,
  pub end: u32,
  pub category: Option<String>,
  #[serde(default)]
  pub message: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct TypeFacts {
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub exports: Vec<ExportTypeFact>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub markers: Vec<TypeAtFact>,
}

impl TypeFacts {
  pub fn is_empty(&self) -> bool {
    self.exports.is_empty() && self.markers.is_empty()
  }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExportTypeFact {
  pub file: String,
  pub name: String,
  #[serde(rename = "type")]
  pub type_str: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeAtFact {
  pub file: String,
  pub offset: u32,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub line: Option<u32>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub column: Option<u32>,
  #[serde(rename = "type")]
  pub type_str: String,
}

#[cfg(feature = "with-node")]
#[derive(Debug)]
struct RunnerProcess {
  child: std::process::Child,
  stdin: BufWriter<std::process::ChildStdin>,
  stdout: BufReader<std::process::ChildStdout>,
}

#[cfg(feature = "with-node")]
#[derive(Debug)]
pub struct TscRunner {
  node_path: PathBuf,
  process: Option<RunnerProcess>,
}

#[cfg(feature = "with-node")]
impl TscRunner {
  pub fn new(node_path: PathBuf) -> anyhow::Result<Self> {
    let mut runner = Self {
      node_path,
      process: None,
    };
    runner.spawn()?;
    Ok(runner)
  }

  pub fn check(&mut self, request: TscRequest) -> anyhow::Result<TscDiagnostics> {
    self.ensure_running()?;

    let mut attempts = 0;
    loop {
      attempts += 1;
      match self.send(&request) {
        Ok(mut diags) => {
          if diags.metadata.options.is_empty() {
            diags.metadata.options = request.options.clone();
          }
          return Ok(diags);
        }
        Err(err) => {
          if attempts >= 2 {
            return Err(err);
          }
          self.spawn()?;
        }
      }
    }
  }

  fn ensure_running(&mut self) -> anyhow::Result<()> {
    if let Some(process) = self.process.as_mut() {
      if process.child.try_wait()?.is_none() {
        return Ok(());
      }
    }

    self.spawn()
  }

  fn spawn(&mut self) -> anyhow::Result<()> {
    if let Some(mut existing) = self.process.take() {
      if existing.child.try_wait().ok().flatten().is_none() {
        let _ = existing.child.kill();
      }
      let _ = existing.child.wait();
    }

    let runner_path = Path::new(env!("CARGO_MANIFEST_DIR"))
      .join("scripts")
      .join("tsc_runner.js");
    if !runner_path.exists() {
      bail!("missing tsc runner at {}", runner_path.display());
    }

    let mut child = std::process::Command::new(&self.node_path);
    child.arg(&runner_path);
    child.stdin(std::process::Stdio::piped());
    child.stdout(std::process::Stdio::piped());
    child.stderr(std::process::Stdio::inherit());

    let mut spawned = child
      .spawn()
      .with_context(|| format!("spawn node at {}", self.node_path.display()))?;
    let stdin = spawned
      .stdin
      .take()
      .context("failed to open stdin for tsc runner")?;
    let stdout = spawned
      .stdout
      .take()
      .context("failed to open stdout for tsc runner")?;

    self.process = Some(RunnerProcess {
      child: spawned,
      stdin: BufWriter::new(stdin),
      stdout: BufReader::new(stdout),
    });
    Ok(())
  }

  fn send(&mut self, request: &TscRequest) -> anyhow::Result<TscDiagnostics> {
    let runner = self
      .process
      .as_mut()
      .context("tsc runner process missing")?;

    let line = serde_json::to_string(request)?;
    runner.stdin.write_all(line.as_bytes())?;
    runner.stdin.write_all(b"\n")?;
    runner.stdin.flush()?;

    let mut response = String::new();
    let bytes = runner.stdout.read_line(&mut response)?;
    if bytes == 0 {
      bail!("tsc runner exited unexpectedly");
    }

    let parsed: TscDiagnostics =
      serde_json::from_str(response.trim_end()).context("parse tsc runner response")?;
    let mut parsed = parsed;
    if parsed.schema_version.is_none() {
      parsed.schema_version = Some(TSC_BASELINE_SCHEMA_VERSION);
    }
    if let Some(crash) = parsed.crash.clone() {
      let mut message = crash.message;
      if let Some(stack) = crash.stack {
        message.push_str("\n");
        message.push_str(&stack);
      }
      bail!("tsc runner crashed: {message}");
    }

    Ok(parsed)
  }
}

#[cfg(feature = "with-node")]
impl Drop for TscRunner {
  fn drop(&mut self) {
    if let Some(mut process) = self.process.take() {
      if process.child.try_wait().ok().flatten().is_none() {
        let _ = process.child.kill();
      }
      let _ = process.child.wait();
    }
  }
}

#[cfg(feature = "with-node")]
pub fn node_available(node_path: &Path) -> bool {
  let output = std::process::Command::new(node_path)
    .arg("--version")
    .output();
  matches!(output, Ok(out) if out.status.success())
}

#[cfg(feature = "with-node")]
pub fn typescript_available(node_path: &Path) -> bool {
  let probe = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("scripts")
    .join("typescript_probe.js");
  if !probe.exists() {
    return false;
  }
  let output = std::process::Command::new(node_path).arg(probe).output();
  matches!(output, Ok(out) if out.status.success())
}

#[cfg(not(feature = "with-node"))]
#[derive(Debug, Default, Clone)]
pub struct TscRunner;

#[cfg(not(feature = "with-node"))]
impl TscRunner {
  pub fn new(_node_path: PathBuf) -> anyhow::Result<Self> {
    Ok(Self)
  }

  pub fn check(&mut self, _request: TscRequest) -> anyhow::Result<TscDiagnostics> {
    Err(anyhow!(
      "tsc runner skipped: built without `with-node` feature"
    ))
  }
}

#[cfg(not(feature = "with-node"))]
pub fn node_available(_node_path: &Path) -> bool {
  false
}

#[cfg(not(feature = "with-node"))]
pub fn typescript_available(_node_path: &Path) -> bool {
  false
}
