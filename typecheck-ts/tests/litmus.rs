use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use typecheck_ts::{BodyId, ExprId, FileId, Host, HostError, Program, Severity};

#[derive(Clone)]
struct FixtureHost {
  sources: HashMap<FileId, Arc<str>>,
  path_by_id: HashMap<FileId, String>,
  id_by_path: HashMap<String, FileId>,
}

impl FixtureHost {
  fn new(files: &[(String, String)]) -> FixtureHost {
    let mut sources = HashMap::new();
    let mut path_by_id = HashMap::new();
    let mut id_by_path = HashMap::new();
    for (idx, (path, source)) in files.iter().enumerate() {
      let id = FileId(idx as u32);
      sources.insert(id, Arc::from(source.clone()));
      path_by_id.insert(id, path.clone());
      id_by_path.insert(path.clone(), id);
    }
    FixtureHost {
      sources,
      path_by_id,
      id_by_path,
    }
  }

  fn file_id(&self, path: &str) -> FileId {
    *self
      .id_by_path
      .get(path)
      .unwrap_or_else(|| panic!("no file named {path}"))
  }

  fn path(&self, id: FileId) -> &str {
    self
      .path_by_id
      .get(&id)
      .map(|s| s.as_str())
      .unwrap_or("<unknown>")
  }
}

impl Host for FixtureHost {
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    self
      .sources
      .get(&file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {:?}", file)))
  }

  fn resolve(&self, from: FileId, specifier: &str) -> Option<FileId> {
    let from_path = Path::new(self.path(from));
    let mut resolved = PathBuf::new();
    if let Some(parent) = from_path.parent() {
      resolved.push(parent);
    }
    resolved.push(specifier);
    if resolved.extension().is_none() {
      resolved.set_extension("ts");
    }
    let normalized = normalize_path(&resolved);
    self.id_by_path.get(&normalized).copied()
  }
}

#[derive(Default)]
struct FixtureExpectations {
  def_types: Vec<DefTypeExpectation>,
  expr_types: Vec<ExprTypeExpectation>,
  diagnostics: Vec<DiagnosticExpectation>,
  ignored_spans: HashMap<String, Vec<(usize, usize)>>,
}

#[derive(Clone)]
struct DefTypeExpectation {
  file: String,
  name: String,
  ty: String,
}

#[derive(Clone)]
struct ExprTypeExpectation {
  file: String,
  snippet: String,
  ty: String,
  offset: Option<u32>,
}

#[derive(Clone)]
struct DiagnosticExpectation {
  file: Option<String>,
  code: Option<String>,
  snippet: Option<String>,
  span: Option<(u32, u32)>,
  severity: Severity,
}

struct Fixture {
  files: Vec<(String, String)>,
  expectations: FixtureExpectations,
  roots: Vec<String>,
}

#[test]
fn litmus_fixtures() {
  let base = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/litmus");
  let mut fixtures = Vec::new();
  for entry in fs::read_dir(&base).expect("read litmus dir") {
    let entry = entry.expect("dir entry");
    if entry.file_type().expect("file type").is_dir() {
      fixtures.push(entry.path());
    }
  }
  fixtures.sort();
  assert!(
    !fixtures.is_empty(),
    "no fixtures found under {}",
    base.display()
  );
  for fixture in fixtures {
    run_fixture(&fixture);
  }
}

fn run_fixture(path: &Path) {
  let fixture = load_fixture(path);
  let host = FixtureHost::new(&fixture.files);
  let roots: Vec<FileId> = fixture
    .roots
    .iter()
    .map(|root| host.file_id(root))
    .collect();
  let mut program = Program::new(host.clone(), roots);
  let diagnostics = program.check();

  assert_diagnostics(&host, &fixture.expectations, &diagnostics);
  assert_def_types(&mut program, &host, &fixture.expectations);
  assert_expr_types(&mut program, &host, &fixture.expectations);
}

fn load_fixture(dir: &Path) -> Fixture {
  let mut files = Vec::new();
  let mut expectations = FixtureExpectations::default();
  let mut file_map = HashMap::new();
  for entry in fs::read_dir(dir).expect("read fixture dir") {
    let entry = entry.expect("dir entry");
    if entry.file_type().expect("file type").is_file()
      && entry.path().extension().map(|e| e == "ts").unwrap_or(false)
    {
      let relative = entry.file_name().into_string().expect("utf-8 file name");
      let source = fs::read_to_string(entry.path()).expect("read file");
      parse_expectations(&relative, &source, &mut expectations);
      file_map.insert(relative.clone(), source.clone());
      files.push((relative, source));
    }
  }
  files.sort_by(|a, b| a.0.cmp(&b.0));

  finalize_expectations(&file_map, &mut expectations);

  let roots = vec!["main.ts".to_string()];
  if !file_map.contains_key("main.ts") {
    panic!(
      "fixture {} is missing main.ts; found {:?}",
      dir.display(),
      file_map.keys().collect::<Vec<_>>()
    );
  }

  Fixture {
    files,
    expectations,
    roots,
  }
}

fn parse_expectations(file: &str, source: &str, expectations: &mut FixtureExpectations) {
  let mut offset = 0usize;
  for line in source.split_inclusive('\n') {
    let trimmed = line.trim_start();
    if trimmed.starts_with("// expect-") {
      expectations
        .ignored_spans
        .entry(file.to_string())
        .or_default()
        .push((offset, offset + line.len()));
    }
    if let Some(rest) = trimmed.strip_prefix("// expect-def-type:") {
      let (name, ty) = rest
        .split_once('=')
        .expect("def type expectations need `name = type`");
      expectations.def_types.push(DefTypeExpectation {
        file: file.to_string(),
        name: name.trim().to_string(),
        ty: ty.trim().to_string(),
      });
    } else if let Some(rest) = trimmed.strip_prefix("// expect-expr-type:") {
      let (snippet, ty) = rest
        .split_once('=')
        .expect("expr type expectations need `\"snippet\" = type`");
      expectations.expr_types.push(ExprTypeExpectation {
        file: file.to_string(),
        snippet: parse_snippet(snippet.trim()),
        ty: ty.trim().to_string(),
        offset: None,
      });
    } else if let Some(rest) = trimmed.strip_prefix("// expect-diagnostic:") {
      let mut parts = rest.trim().splitn(2, ' ');
      let code_raw = parts
        .next()
        .expect("diagnostic expectation missing code")
        .trim();
      let code = if code_raw.eq_ignore_ascii_case("none") {
        None
      } else {
        Some(code_raw.to_string())
      };
      let snippet = parts.next().map(|s| parse_snippet(s.trim()));
      expectations.diagnostics.push(DiagnosticExpectation {
        file: Some(file.to_string()),
        code,
        snippet,
        span: None,
        severity: Severity::Error,
      });
    }
    offset += line.len();
  }
}

fn finalize_expectations(files: &HashMap<String, String>, expectations: &mut FixtureExpectations) {
  for expr in expectations.expr_types.iter_mut() {
    let source = files
      .get(&expr.file)
      .unwrap_or_else(|| panic!("missing source for {}", expr.file));
    let range = find_snippet(
      source,
      &expr.snippet,
      expectations.ignored_spans.get(&expr.file),
    );
    expr.offset = Some(range.0 as u32);
  }
  for diag in expectations.diagnostics.iter_mut() {
    if let Some(snippet) = &diag.snippet {
      let file = diag.file.as_ref().expect("diagnostic snippets need a file");
      let source = files
        .get(file)
        .unwrap_or_else(|| panic!("missing source for {}", file));
      let range = find_snippet(source, snippet, expectations.ignored_spans.get(file));
      diag.span = Some((range.0 as u32, range.1 as u32));
    }
  }
}

fn parse_snippet(raw: &str) -> String {
  let trimmed = raw.trim();
  let unquoted = if let Some(stripped) = trimmed.strip_prefix('"').and_then(|s| s.strip_suffix('"'))
  {
    stripped.to_string()
  } else if let Some(stripped) = trimmed
    .strip_prefix('\'')
    .and_then(|s| s.strip_suffix('\''))
  {
    stripped.to_string()
  } else {
    trimmed.to_string()
  };
  unquoted.replace("\\\"", "\"")
}

fn find_snippet(
  source: &str,
  snippet: &str,
  ignored: Option<&Vec<(usize, usize)>>,
) -> (usize, usize) {
  let mut start = 0usize;
  while let Some(idx) = source[start..].find(snippet) {
    let abs = start + idx;
    let end = abs + snippet.len();
    if ignored
      .map(|ranges| ranges.iter().any(|(s, e)| abs >= *s && abs < *e))
      .unwrap_or(false)
    {
      start = end;
      continue;
    }
    return (abs, end);
  }
  panic!("snippet `{snippet}` not found in source");
}

fn assert_def_types(program: &mut Program, host: &FixtureHost, expectations: &FixtureExpectations) {
  for expect in expectations.def_types.iter() {
    let file = host.file_id(&expect.file);
    let def = program
      .definitions_in_file(file)
      .into_iter()
      .find(|d| program.def_name(*d).as_deref() == Some(expect.name.as_str()))
      .unwrap_or_else(|| panic!("definition `{}` not found in {}", expect.name, expect.file));
    let ty = program.type_of_def(def);
    let rendered = program.display_type(ty).to_string();
    assert_eq!(
      rendered, expect.ty,
      "expected def `{}` in {} to be {}, got {}",
      expect.name, expect.file, expect.ty, rendered
    );
  }
}

fn assert_expr_types(
  program: &mut Program,
  host: &FixtureHost,
  expectations: &FixtureExpectations,
) {
  for expect in expectations.expr_types.iter() {
    let offset = expect
      .offset
      .unwrap_or_else(|| panic!("missing offset for {}", expect.snippet));
    let file = host.file_id(&expect.file);
    let ty = resolve_expr_type(program, file, offset).unwrap_or_else(|| {
      panic!(
        "no expression found at offset {} in {}",
        offset, expect.file
      )
    });
    let rendered = program.display_type(ty).to_string();
    assert_eq!(
      rendered, expect.ty,
      "expected expr `{}` in {} to be {}, got {}",
      expect.snippet, expect.file, expect.ty, rendered
    );
  }
}

fn resolve_expr_type(
  program: &mut Program,
  file: FileId,
  offset: u32,
) -> Option<typecheck_ts::TypeId> {
  let mut candidates: Vec<BodyId> = Vec::new();
  if let Some(body) = program.file_body(file) {
    candidates.push(body);
  }
  candidates.extend(
    program
      .definitions_in_file(file)
      .into_iter()
      .filter_map(|def| program.body_of_def(def)),
  );
  let mut best: Option<(u32, typecheck_ts::TypeId)> = None;
  for probe in [offset, offset.saturating_sub(1)] {
    for body in candidates.iter().copied() {
      let result = program.check_body(body);
      if let Some((expr_id, ty)) = result.expr_at(probe) {
        if let Some(span) = result.expr_span(expr_id) {
          let width = span.end - span.start;
          if best.map(|(w, _)| width < w).unwrap_or(true) {
            best = Some((width, ty));
          }
        } else {
          best = Some((u32::MAX, ty));
        }
      }
    }
    if best.is_some() {
      break;
    }
  }
  if let Some((_, ty)) = best {
    return Some(ty);
  }

  // Fallback: choose the closest expression span if no exact match was found.
  let mut nearest: Option<(u32, typecheck_ts::TypeId)> = None;
  for body in candidates {
    let result = program.check_body(body);
    for (idx, span) in result.expr_spans().iter().enumerate() {
      let Some(ty) = result.expr_type(ExprId(idx as u32)) else {
        continue;
      };
      let distance = if offset < span.start {
        span.start - offset
      } else if offset > span.end {
        offset - span.end
      } else {
        0
      };
      if nearest.map(|(d, _)| distance < d).unwrap_or(true) {
        nearest = Some((distance, ty));
      }
    }
  }
  nearest.map(|(_, ty)| ty)
}

fn assert_diagnostics(
  host: &FixtureHost,
  expectations: &FixtureExpectations,
  diagnostics: &[typecheck_ts::Diagnostic],
) {
  let mut remaining: Vec<_> = diagnostics
    .iter()
    .map(|d| {
      let primary = &d.primary;
      let span = Some((
        host.path(primary.file).to_string(),
        primary.range.start,
        primary.range.end,
        d.severity,
      ));
      (d.code.as_str().to_string(), span)
    })
    .collect();
  for expected in expectations.diagnostics.iter() {
    let pos = remaining.iter().position(|(code, span)| {
      if let Some(expected_code) = &expected.code {
        if code != expected_code {
          return false;
        }
      }
      match (&expected.span, span) {
        (None, None) => true,
        (None, Some(_)) => true,
        (Some((s, e)), Some((file, actual_start, actual_end, severity))) => {
          if expected.severity != *severity {
            return false;
          }
          let expected_file = expected.file.as_deref().unwrap_or(file.as_str());
          if file != expected_file {
            return false;
          }
          let contains_expected = actual_start <= s && actual_end >= e;
          let within_expected = s <= actual_start && e >= actual_end;
          contains_expected || within_expected
        }
        _ => false,
      }
    });
    if let Some(idx) = pos {
      remaining.swap_remove(idx);
    } else {
      panic!(
        "expected diagnostic {:?} at {:?} missing; got {:?}",
        expected.code, expected.span, diagnostics
      );
    }
  }
  if !remaining.is_empty() {
    panic!("unexpected diagnostics left: {:?}", remaining);
  }
}

fn normalize_path(path: &Path) -> String {
  use std::path::Component;

  let mut components = Vec::new();
  for component in path.components() {
    match component {
      Component::CurDir => {}
      Component::ParentDir => {
        components.pop();
      }
      Component::Normal(seg) => components.push(seg.to_string_lossy()),
      Component::RootDir | Component::Prefix(_) => {
        components.push(component.as_os_str().to_string_lossy())
      }
    }
  }
  components.join("/")
}
