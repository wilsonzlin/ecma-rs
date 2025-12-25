use ahash::{HashMap, HashSet};
use parse_js::lex::KEYWORDS_MAPPING;

/// Deterministic name generator for decompiler-emitted locals.
///
/// The constructor seeds the reserved set with ECMAScript keywords and allows
/// callers to provide additional reserved identifiers (e.g. unknown load/store
/// names or builtin roots extracted from `Arg::Builtin`). All generated names
/// are guaranteed to be valid JavaScript identifiers and to avoid collisions
/// with the reserved set.
#[derive(Debug, Clone)]
pub struct NameMangler {
  used: HashSet<String>,
  fresh_counters: HashMap<String, usize>,
  reg_names: HashMap<u32, String>,
  foreign_names: HashMap<u32, String>,
  /// Whether register/foreign locals should be minified (`a`, `b`, ...). When
  /// disabled, names are generated using readable prefixes like `r0`.
  pub minify_locals: bool,
}

impl NameMangler {
  /// Creates a new mangler. The provided reserved identifiers are merged with
  /// ECMAScript keywords and contextual keywords.
  pub fn new(reserved: impl IntoIterator<Item = String>) -> Self {
    let mut reserved_set = default_reserved_names();
    reserved_set.extend(reserved);

    Self {
      used: reserved_set,
      fresh_counters: HashMap::default(),
      reg_names: HashMap::default(),
      foreign_names: HashMap::default(),
      minify_locals: false,
    }
  }

  /// Returns a unique identifier based on the provided prefix.
  pub fn fresh(&mut self, prefix: &str) -> String {
    let base = sanitize_identifier(prefix);
    let mut counter = *self.fresh_counters.get(&base).unwrap_or(&0);

    loop {
      let candidate = if counter == 0 {
        base.clone()
      } else {
        format!("{base}_{counter}")
      };
      counter += 1;

      if !self.is_taken(&candidate) {
        self.fresh_counters.insert(base.clone(), counter);
        self.mark_used(candidate.clone());
        return candidate;
      }
    }
  }

  /// Returns a deterministic, collision-free name for the given register.
  pub fn name_for_reg(&mut self, reg: u32) -> String {
    if let Some(name) = self.reg_names.get(&reg) {
      return name.clone();
    }

    let base = self
      .minify_locals
      .then(|| encode_short_identifier(reg as usize))
      .unwrap_or_else(|| sanitize_identifier(&format!("r{reg}")));
    let name = self.ensure_unique(base);
    self.reg_names.insert(reg, name.clone());
    name
  }

  /// Returns a deterministic, collision-free name for the given foreign binding
  /// index.
  pub fn name_for_foreign(&mut self, idx: u32) -> String {
    if let Some(name) = self.foreign_names.get(&idx) {
      return name.clone();
    }

    let base = self
      .minify_locals
      .then(|| encode_short_identifier(idx as usize))
      .unwrap_or_else(|| sanitize_identifier(&format!("__f{idx}")));
    let name = self.ensure_unique(base);
    self.foreign_names.insert(idx, name.clone());
    name
  }

  fn ensure_unique(&mut self, base: String) -> String {
    let mut candidate = base.clone();
    let mut disambiguator = 1usize;
    while self.is_taken(&candidate) {
      candidate = format!("{base}_{disambiguator}");
      disambiguator += 1;
    }
    self.mark_used(candidate.clone());
    candidate
  }

  fn mark_used(&mut self, name: String) {
    self.used.insert(name);
  }

  fn is_taken(&self, name: &str) -> bool {
    self.used.contains(name)
  }
}

fn default_reserved_names() -> HashSet<String> {
  let mut reserved = HashSet::default();
  for keyword in KEYWORDS_MAPPING.values() {
    reserved.insert((*keyword).to_string());
  }
  // Additional identifiers that can change runtime semantics if shadowed.
  reserved.insert("eval".to_string());
  reserved.insert("arguments".to_string());
  reserved
}

fn encode_short_identifier(mut n: usize) -> String {
  const ALPHABET: &[u8] = b"abcdefghijklmnopqrstuvwxyz";
  let mut out = Vec::new();
  loop {
    out.push(ALPHABET[n % ALPHABET.len()]);
    n /= ALPHABET.len();
    if n == 0 {
      break;
    }
    n -= 1;
  }
  out.reverse();
  String::from_utf8(out).expect("alphabet is ASCII")
}

fn sanitize_identifier(prefix: &str) -> String {
  fn is_start(ch: char) -> bool {
    matches!(ch, 'a'..='z' | 'A'..='Z' | '_' | '$')
  }
  fn is_continue(ch: char) -> bool {
    is_start(ch) || ch.is_ascii_digit()
  }

  let mut out = String::new();
  for (idx, ch) in prefix.chars().enumerate() {
    let valid = if idx == 0 {
      is_start(ch)
    } else {
      is_continue(ch)
    };
    out.push(if valid { ch } else { '_' });
  }

  if out.is_empty() || out.starts_with(|c: char| c.is_ascii_digit()) {
    out.insert(0, '_');
  }
  out
}
