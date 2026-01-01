use crate::diagnostic_norm::normalize_type_string;
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
use std::sync::atomic::AtomicU64;
#[cfg(feature = "with-node")]
use std::sync::atomic::Ordering;
#[cfg(feature = "with-node")]
use std::sync::{Arc, Mutex};
#[cfg(feature = "with-node")]
use std::time::{Duration, Instant};

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TscRequest {
  pub root_names: Vec<String>,
  pub files: HashMap<String, String>,
  #[serde(default)]
  pub options: Map<String, Value>,
  /// When set, the runner will skip collecting type facts (exports/markers) and
  /// only return diagnostics. This avoids expensive `checker.typeToString` work
  /// for large conformance suites that only diff diagnostics.
  #[serde(default, skip_serializing_if = "crate::serde_helpers::is_false")]
  pub diagnostics_only: bool,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub type_queries: Vec<TypeQuery>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct TypeQuery {
  pub file: String,
  /// UTF-8 byte offset into `file` where the query should be resolved.
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

impl TscDiagnostics {
  pub(crate) fn canonicalize_for_baseline(&mut self) {
    self.schema_version = Some(TSC_BASELINE_SCHEMA_VERSION);
    self.diagnostics.sort_by(|a, b| {
      (a.file.as_deref().unwrap_or(""), a.start, a.end, a.code).cmp(&(
        b.file.as_deref().unwrap_or(""),
        b.start,
        b.end,
        b.code,
      ))
    });

    if let Some(type_facts) = self.type_facts.as_mut() {
      for export in &mut type_facts.exports {
        export.type_str = normalize_type_string(&export.type_str);
      }
      for marker in &mut type_facts.markers {
        marker.type_str = normalize_type_string(&marker.type_str);
      }
      type_facts
        .exports
        .sort_by(|a, b| (&a.file, &a.name, &a.type_str).cmp(&(&b.file, &b.name, &b.type_str)));
      type_facts
        .markers
        .sort_by(|a, b| (&a.file, a.offset, &a.type_str).cmp(&(&b.file, b.offset, &b.type_str)));
    }
  }
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
  /// UTF-8 byte offset into `file`.
  pub start: u32,
  /// UTF-8 byte offset into `file`.
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
  /// UTF-8 byte offset into `file` where the type was queried.
  pub offset: u32,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub line: Option<u32>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub column: Option<u32>,
  #[serde(rename = "type")]
  pub type_str: String,
}

#[cfg(feature = "with-node")]
#[derive(Clone, Debug)]
pub(crate) struct TscKillSwitch {
  state: Arc<Mutex<KillState>>,
}

#[cfg(feature = "with-node")]
#[derive(Debug)]
struct KillState {
  child: Option<std::process::Child>,
  active_request_id: u64,
}

#[cfg(feature = "with-node")]
impl TscKillSwitch {
  pub(crate) fn new() -> Self {
    Self {
      state: Arc::new(Mutex::new(KillState {
        child: None,
        active_request_id: 0,
      })),
    }
  }

  pub(crate) fn kill(&self) {
    let mut guard = self.state.lock().unwrap();
    if let Some(child) = guard.child.as_mut() {
      let _ = child.kill();
    }
  }

  pub(crate) fn kill_request(&self, request_id: u64) {
    let mut guard = self.state.lock().unwrap();
    if guard.active_request_id != request_id {
      return;
    }
    if let Some(child) = guard.child.as_mut() {
      let _ = child.kill();
    }
  }

  fn activate_request(&self, request_id: u64) -> ActiveRequestGuard {
    {
      let mut guard = self.state.lock().unwrap();
      guard.active_request_id = request_id;
    }
    ActiveRequestGuard {
      state: Arc::clone(&self.state),
      request_id,
    }
  }
}

#[cfg(feature = "with-node")]
struct ActiveRequestGuard {
  state: Arc<Mutex<KillState>>,
  request_id: u64,
}

#[cfg(feature = "with-node")]
impl Drop for ActiveRequestGuard {
  fn drop(&mut self) {
    let mut guard = self.state.lock().unwrap();
    if guard.active_request_id == self.request_id {
      guard.active_request_id = 0;
    }
  }
}

#[cfg(feature = "with-node")]
fn is_cancelled(cancel: &AtomicU64, request_id: u64) -> bool {
  let value = cancel.load(Ordering::Relaxed);
  value == request_id || value == u64::MAX
}

#[cfg(not(feature = "with-node"))]
#[derive(Clone, Debug, Default)]
pub(crate) struct TscKillSwitch;

#[cfg(not(feature = "with-node"))]
impl TscKillSwitch {
  pub(crate) fn new() -> Self {
    Self
  }

  pub(crate) fn kill(&self) {}

  pub(crate) fn kill_request(&self, _request_id: u64) {}
}

#[cfg(feature = "with-node")]
#[derive(Debug)]
struct RunnerProcess {
  stdin: BufWriter<std::process::ChildStdin>,
  stdout: BufReader<std::process::ChildStdout>,
}

#[cfg(feature = "with-node")]
#[derive(Debug)]
pub struct TscRunner {
  node_path: PathBuf,
  kill_switch: TscKillSwitch,
  process: Option<RunnerProcess>,
}

#[cfg(feature = "with-node")]
impl TscRunner {
  pub fn new(node_path: PathBuf) -> anyhow::Result<Self> {
    Self::with_kill_switch(node_path, TscKillSwitch::new())
  }

  pub(crate) fn with_kill_switch(
    node_path: PathBuf,
    kill_switch: TscKillSwitch,
  ) -> anyhow::Result<Self> {
    let mut runner = Self {
      node_path,
      kill_switch,
      process: None,
    };
    runner.spawn()?;
    Ok(runner)
  }

  pub fn check(&mut self, request: TscRequest) -> anyhow::Result<TscDiagnostics> {
    self.ensure_running()?;

    let cancel = AtomicU64::new(0);
    self.check_inner(request, &cancel, 1)
  }

  pub(crate) fn check_cancellable(
    &mut self,
    request: TscRequest,
    cancel: &AtomicU64,
    request_id: u64,
  ) -> anyhow::Result<TscDiagnostics> {
    if is_cancelled(cancel, request_id) {
      bail!("tsc request cancelled");
    }

    let _active = self.kill_switch.activate_request(request_id);
    self.ensure_running()?;
    self.check_inner(request, cancel, request_id)
  }

  fn check_inner(
    &mut self,
    request: TscRequest,
    cancel: &AtomicU64,
    request_id: u64,
  ) -> anyhow::Result<TscDiagnostics> {
    let mut attempts = 0;
    loop {
      if is_cancelled(cancel, request_id) {
        bail!("tsc request cancelled");
      }
      attempts += 1;
      match self.send(&request) {
        Ok(mut diags) => {
          if diags.metadata.options.is_empty() {
            diags.metadata.options = request.options.clone();
          }
          return Ok(diags);
        }
        Err(err) => {
          if is_cancelled(cancel, request_id) || attempts >= 2 {
            return Err(err);
          }
          self.spawn()?;
        }
      }
    }
  }

  fn ensure_running(&mut self) -> anyhow::Result<()> {
    if self.process.is_some() {
      let mut child_guard = self.kill_switch.state.lock().unwrap();
      if let Some(child) = child_guard.child.as_mut() {
        if child.try_wait()?.is_none() {
          return Ok(());
        }
      }
    }

    self.spawn()
  }

  fn spawn(&mut self) -> anyhow::Result<()> {
    let _ = self.process.take();
    // Do not hold the kill switch mutex while waiting/spawning; timeouts call
    // `TscKillSwitch::kill()` from other threads and must never block on slow
    // process management.
    let existing_child = {
      let mut child_guard = self.kill_switch.state.lock().unwrap();
      child_guard.child.take()
    };
    if let Some(mut child) = existing_child {
      if child.try_wait().ok().flatten().is_none() {
        let _ = child.kill();
      }
      let _ = child.wait();
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

    {
      let mut child_guard = self.kill_switch.state.lock().unwrap();
      child_guard.child = Some(spawned);
    }
    self.process = Some(RunnerProcess {
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
    let _ = self.process.take();
    let child = {
      let mut child_guard = self.kill_switch.state.lock().unwrap();
      child_guard.child.take()
    };
    if let Some(mut child) = child {
      if child.try_wait().ok().flatten().is_none() {
        let _ = child.kill();
      }
      let _ = child.wait();
    }
  }
}

#[cfg(feature = "with-node")]
fn command_succeeds_with_timeout(mut command: std::process::Command, timeout: Duration) -> bool {
  command.stdin(std::process::Stdio::null());
  command.stdout(std::process::Stdio::null());
  command.stderr(std::process::Stdio::null());
  let mut child = match command.spawn() {
    Ok(child) => child,
    Err(_) => return false,
  };

  let deadline = Instant::now() + timeout;
  loop {
    match child.try_wait() {
      Ok(Some(status)) => return status.success(),
      Ok(None) => {
        if Instant::now() >= deadline {
          let _ = child.kill();
          let _ = child.wait();
          return false;
        }
        std::thread::sleep(Duration::from_millis(10));
      }
      Err(_) => return false,
    }
  }
}

#[cfg(feature = "with-node")]
pub fn node_available(node_path: &Path) -> bool {
  let mut command = std::process::Command::new(node_path);
  command.arg("--version");
  command_succeeds_with_timeout(command, Duration::from_secs(2))
}

#[cfg(feature = "with-node")]
pub fn typescript_available(node_path: &Path) -> bool {
  let probe = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("scripts")
    .join("typescript_probe.js");
  if !probe.exists() {
    return false;
  }
  let mut command = std::process::Command::new(node_path);
  command.arg(probe);
  command_succeeds_with_timeout(command, Duration::from_secs(2))
}

#[cfg(not(feature = "with-node"))]
#[derive(Debug, Default, Clone)]
pub struct TscRunner;

#[cfg(not(feature = "with-node"))]
impl TscRunner {
  pub fn new(_node_path: PathBuf) -> anyhow::Result<Self> {
    Ok(Self)
  }

  pub(crate) fn with_kill_switch(
    _node_path: PathBuf,
    _kill_switch: TscKillSwitch,
  ) -> anyhow::Result<Self> {
    Ok(Self)
  }

  pub fn check(&mut self, _request: TscRequest) -> anyhow::Result<TscDiagnostics> {
    Err(anyhow!(
      "tsc runner skipped: built without `with-node` feature"
    ))
  }

  pub(crate) fn check_cancellable(
    &mut self,
    request: TscRequest,
    _cancel: &AtomicU64,
    _request_id: u64,
  ) -> anyhow::Result<TscDiagnostics> {
    self.check(request)
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
