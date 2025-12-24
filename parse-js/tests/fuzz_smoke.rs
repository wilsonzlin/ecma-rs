use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use std::sync::mpsc;
use std::thread;
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

fn run_under_budget(input: String, dialect: Dialect) {
  let input_len = input.len();
  let input_preview = preview(&input);
  let (tx, rx) = mpsc::channel();
  let handle = thread::spawn(move || {
    let start = Instant::now();
    let result = std::panic::catch_unwind(|| {
      parse_with_options(
        &input,
        ParseOptions {
          dialect,
          source_type: SourceType::Module,
        },
      )
    });
    let _ = tx.send((result, start.elapsed()));
  });

  match rx.recv_timeout(TIMEOUT_PER_CASE) {
    Ok((Ok(_), elapsed)) => {
      assert!(
        elapsed <= TIMEOUT_PER_CASE,
        "dialect {:?} finished in {:?} which exceeds budget {:?} on {:?}",
        dialect,
        elapsed,
        TIMEOUT_PER_CASE,
        input_preview,
      );
    }
    Ok((Err(panic), _)) => {
      let _ = handle.join();
      panic!(
        "dialect {:?} panicked on {:?}: {:?}",
        dialect, input_preview, panic
      );
    }
    Err(_) => {
      panic!(
        "dialect {:?} timed out after {:?} on {:?}",
        dialect, TIMEOUT_PER_CASE, input_preview
      );
    }
  };

  let _ = handle.join();
}

#[test]
fn parser_handles_adversarial_inputs_quickly() {
  let mut rng = SimpleRng::new(0xBEEF_F00D_FACE_FEED);
  let mut cases: Vec<String> = regression_inputs().iter().map(|s| s.to_string()).collect();
  while cases.len() < RANDOM_INPUTS {
    cases.push(random_source(&mut rng));
  }

  for (i, case) in cases.into_iter().enumerate() {
    for dialect in [Dialect::Ts, Dialect::Tsx] {
      run_under_budget(case.clone(), dialect);
    }
    // Keep iteration count deterministic.
    assert!(i < RANDOM_INPUTS);
  }
}
