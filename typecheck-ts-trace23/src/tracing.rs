use serde::Deserialize;
use serde::Serialize;
use std::time::Duration;
use std::time::Instant;

/// A single timed event emitted during type checking.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProfileEvent {
  pub name: String,
  pub file: Option<String>,
  pub body: Option<String>,
  pub duration_ms: f64,
  pub metadata: Option<String>,
}

#[derive(Default)]
pub struct Profiler {
  events: Vec<ProfileEvent>,
}

impl Profiler {
  pub fn new() -> Self {
    Self { events: Vec::new() }
  }

  /// Time the given closure, emitting a tracing span with file/body context
  /// and recording the duration for later profiling output.
  pub fn record<T, F>(
    &mut self,
    name: &'static str,
    file: Option<&str>,
    body: Option<&str>,
    f: F,
  ) -> T
  where
    F: FnOnce() -> T,
  {
    let span = ::tracing::info_span!("typecheck", stage = name, file = file.unwrap_or(""));
    let _guard = span.enter();
    let start = Instant::now();
    let result = f();
    let duration = start.elapsed();

    self.events.push(ProfileEvent {
      name: name.to_string(),
      file: file.map(|s| s.to_string()),
      body: body.map(|s| s.to_string()),
      duration_ms: duration_to_ms(duration),
      metadata: None,
    });

    result
  }

  pub fn push_event(
    &mut self,
    name: &'static str,
    file: Option<&str>,
    body: Option<&str>,
    duration: Duration,
  ) {
    self.events.push(ProfileEvent {
      name: name.to_string(),
      file: file.map(|s| s.to_string()),
      body: body.map(|s| s.to_string()),
      duration_ms: duration_to_ms(duration),
      metadata: None,
    });
  }

  pub fn finish(self) -> Vec<ProfileEvent> {
    self.events
  }
}

pub fn duration_to_ms(duration: Duration) -> f64 {
  (duration.as_secs_f64()) * 1000.0
}
