use parse_js::error::SyntaxErrorType;
use parse_js::{
  parse_with_options, parse_with_options_cancellable, Dialect, ParseOptions, SourceType,
};
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering as AtomicOrdering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

const TIMEOUT_PER_CASE: Duration = Duration::from_millis(500);
const RANDOM_INPUTS: usize = 200;

#[derive(Clone)]
struct SimpleRng(u64);

impl SimpleRng {
  fn new(seed: u64) -> Self {
    SimpleRng(seed)
  }

  fn next_u64(&mut self) -> u64 {
    let mut x = self.0;
    // xorshift64*
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    self.0 = x;
    x
  }

  fn gen_range(&mut self, upper: usize) -> usize {
    if upper <= 1 {
      0
    } else {
      (self.next_u64() % upper as u64) as usize
    }
  }

  fn choose<'a>(&mut self, slice: &'a [&'a str]) -> &'a str {
    let idx = self.gen_range(slice.len());
    slice[idx]
  }

  fn coinflip(&mut self, numerator: u32, denominator: u32) -> bool {
    debug_assert!(numerator <= denominator && denominator != 0);
    (self.next_u64() % denominator as u64) < numerator as u64
  }
}

fn deep_nesting(depth: usize) -> String {
  let mut out = String::new();
  for _ in 0..depth {
    out.push('(');
    out.push('{');
    out.push('[');
  }
  out.push_str("value");
  for _ in 0..depth {
    out.push(']');
    out.push('}');
    out.push(')');
  }
  out
}

fn random_source(rng: &mut SimpleRng) -> String {
  // Operators, delimiters, and keywords exercise lexer paths.
  const ASCII_FRAGMENTS: &[&str] = &[
    "+",
    "-",
    "*",
    "/",
    "%",
    "&",
    "|",
    "^",
    "!",
    "?",
    "~",
    ":",
    ";",
    ",",
    ".",
    "<",
    ">",
    "=>",
    "==",
    "===",
    "!=",
    "!==",
    "<=",
    ">=",
    "<<",
    ">>",
    ">>>",
    "&&",
    "||",
    "??",
    "(",
    ")",
    "[",
    "]",
    "{",
    "}",
    "=>",
    "let",
    "const",
    "var",
    "function",
    "class",
    "interface",
    "type",
    "enum",
    "yield",
    "await",
    "return",
    "extends",
  ];
  const UNICODE_SCALARS: &[&str] = &[
    "λ", "Ж", "中", "ほ", "😀", "💥", "𝛑", "Ω", "‽", "√", "¿", "🧪", "ꝏ", "ß", "ø",
  ];
  // Intentionally malformed escape sequences and string-like fragments.
  const MALFORMED_ESCAPES: &[&str] = &[
    "\\u{}",
    "\\xZZ",
    "\\uZZZZ",
    "\\u{110000}",
    "\\u{",
    "\\x0G",
    "\\9",
    "\\u{nothex}",
    "\\",
  ];

  let mut out = String::new();
  if rng.coinflip(1, 3) {
    let depth = 1 + rng.gen_range(8);
    out.push_str(&deep_nesting(depth));
  }

  let target_len = 16 + rng.gen_range(96);
  while out.len() < target_len {
    match rng.gen_range(6) {
      0 => out.push_str(rng.choose(ASCII_FRAGMENTS)),
      1 => out.push_str(rng.choose(UNICODE_SCALARS)),
      2 => {
        out.push('"');
        out.push_str(rng.choose(MALFORMED_ESCAPES));
        out.push('"');
      }
      3 => {
        out.push('\'');
        out.push_str(rng.choose(MALFORMED_ESCAPES));
        out.push('\'');
      }
      4 => {
        out.push('`');
        out.push_str(rng.choose(MALFORMED_ESCAPES));
        out.push('`');
      }
      _ => {
        if rng.coinflip(1, 2) {
          out.push_str(&deep_nesting(rng.gen_range(6)));
        } else {
          out.push('\n');
        }
      }
    }
  }

  if out.is_empty() {
    out.push(';');
  }
  if out.len() > 512 {
    out.truncate(512);
  }
  out
}

fn regression_inputs() -> &'static [&'static str] {
  &[
    "\"\\\\u{}\";\"\\\\xZZ\";`\\\\u{110000}`",
    "(((((((((((((((((((((() => {}}}}}}}}}}}}}}}}}})",
    "<div>{() => <span>{\\\\u{}}</span>}</div>",
    "for await (let 🧪 of async function*(){ yield* arguments; }()) { continue ??= new.target }",
    "type T = { [K in keyof typeof import(\"mod\")]: \\xZZ }",
  ]
}

fn preview(input: &str) -> String {
  let replaced = input.replace('\n', "\\n");
  let mut preview: String = replaced.chars().take(80).collect();
  if replaced.chars().count() > 80 {
    preview.push('…');
  }
  preview
}

#[test]
fn invalid_literals_report_errors() {
  let opts = ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  };
  for case in ["\"\\u{110000}\"", "`\\u{110000}`", "/a/gg"] {
    let result = parse_with_options(case, opts);
    assert!(result.is_err(), "expected error for {case:?}");
  }
}

struct TimeoutManager {
  inner: Arc<TimeoutManagerInner>,
  next_id: AtomicUsize,
  thread: Mutex<Option<std::thread::JoinHandle<()>>>,
}

struct TimeoutManagerInner {
  state: Mutex<TimeoutManagerState>,
  cv: Condvar,
}

struct TimeoutManagerState {
  active: HashMap<usize, TimeoutEntry>,
  shutdown: bool,
}

struct TimeoutEntry {
  deadline: Instant,
  cancel: Arc<AtomicBool>,
  cancelled: bool,
}

struct TimeoutGuard {
  id: usize,
  inner: Arc<TimeoutManagerInner>,
}

impl TimeoutManager {
  fn new() -> Self {
    let inner = Arc::new(TimeoutManagerInner {
      state: Mutex::new(TimeoutManagerState {
        active: HashMap::new(),
        shutdown: false,
      }),
      cv: Condvar::new(),
    });
    let thread_inner = Arc::clone(&inner);
    let handle = std::thread::spawn(move || timeout_thread(thread_inner));
    Self {
      inner,
      next_id: AtomicUsize::new(1),
      thread: Mutex::new(Some(handle)),
    }
  }

  fn register(&self, deadline: Instant, cancel: Arc<AtomicBool>) -> TimeoutGuard {
    let id = self.next_id.fetch_add(1, AtomicOrdering::Relaxed);
    let mut state = self.inner.state.lock().unwrap();
    state.active.insert(
      id,
      TimeoutEntry {
        deadline,
        cancel,
        cancelled: false,
      },
    );
    self.inner.cv.notify_one();
    TimeoutGuard {
      id,
      inner: Arc::clone(&self.inner),
    }
  }
}

impl Drop for TimeoutManager {
  fn drop(&mut self) {
    {
      let mut state = self.inner.state.lock().unwrap();
      state.shutdown = true;
      self.inner.cv.notify_one();
    }

    if let Some(handle) = self.thread.lock().unwrap().take() {
      let _ = handle.join();
    }
  }
}

impl Drop for TimeoutGuard {
  fn drop(&mut self) {
    let mut state = self.inner.state.lock().unwrap();
    state.active.remove(&self.id);
    self.inner.cv.notify_one();
  }
}

fn timeout_thread(inner: Arc<TimeoutManagerInner>) {
  let mut guard = inner.state.lock().unwrap();
  loop {
    if guard.shutdown {
      return;
    }

    let now = Instant::now();
    let mut next_deadline: Option<Instant> = None;

    for entry in guard.active.values_mut() {
      if entry.cancelled {
        continue;
      }
      if now >= entry.deadline {
        entry.cancelled = true;
        entry.cancel.store(true, AtomicOrdering::Relaxed);
        continue;
      }

      next_deadline = match next_deadline {
        Some(existing) => Some(existing.min(entry.deadline)),
        None => Some(entry.deadline),
      };
    }

    if let Some(deadline) = next_deadline {
      let wait_for = deadline
        .checked_duration_since(now)
        .unwrap_or_else(|| Duration::from_millis(0));
      let (new_guard, _) = inner.cv.wait_timeout(guard, wait_for).unwrap();
      guard = new_guard;
    } else {
      guard = inner.cv.wait(guard).unwrap();
    }
  }
}

fn run_under_budget(input: String, dialect: Dialect, timeouts: &TimeoutManager) {
  let input_preview = preview(&input);
  let cancel = Arc::new(AtomicBool::new(false));
  let start = Instant::now();
  let deadline = start + TIMEOUT_PER_CASE;
  let _guard = timeouts.register(deadline, Arc::clone(&cancel));
  let result = parse_with_options_cancellable(
    &input,
    ParseOptions {
      dialect,
      source_type: SourceType::Module,
    },
    Arc::clone(&cancel),
  );
  let elapsed = start.elapsed();

  if elapsed > TIMEOUT_PER_CASE {
    panic!(
      "dialect {:?} finished in {:?} which exceeds budget {:?} on {:?}",
      dialect, elapsed, TIMEOUT_PER_CASE, input_preview
    );
  }

  match result {
    Ok(_) => {}
    Err(err) => {
      if err.typ == SyntaxErrorType::Cancelled {
        panic!(
          "dialect {:?} timed out after {:?} on {:?}",
          dialect, TIMEOUT_PER_CASE, input_preview
        );
      }
    }
  }
}

#[test]
fn parser_handles_adversarial_inputs_quickly() {
  let timeouts = TimeoutManager::new();
  let mut rng = SimpleRng::new(0xBEEF_F00D_FACE_FEED);
  let mut cases: Vec<String> = regression_inputs().iter().map(|s| s.to_string()).collect();
  while cases.len() < RANDOM_INPUTS {
    cases.push(random_source(&mut rng));
  }

  for (i, case) in cases.into_iter().enumerate() {
    for dialect in [Dialect::Ts, Dialect::Tsx] {
      run_under_budget(case.clone(), dialect, &timeouts);
    }
    // Keep iteration count deterministic.
    assert!(i < RANDOM_INPUTS);
  }
}
