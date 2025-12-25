use clap::{ArgAction, Args, Parser, Subcommand, ValueEnum};
use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::{Diagnostic, FileId, Severity};
use serde::Serialize;
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::{Arc, Mutex};
use tracing::Level;
use tracing_subscriber::fmt::format::FmtSpan;
use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibName, ScriptTarget};
use typecheck_ts::{Host, HostError, Program};

#[derive(Parser)]
#[command(author, version, about = "TypeScript type checking CLI")]
struct Cli {
  #[command(subcommand)]
  command: Commands,
}

#[derive(Subcommand)]
enum Commands {
  /// Type-check one or more entry files.
  Typecheck(TypecheckArgs),
}

#[derive(Args)]
struct TypecheckArgs {
  /// Entry files to type-check.
  #[arg(required = true)]
  entries: Vec<PathBuf>,

  /// Emit JSON diagnostics and query results.
  #[arg(long)]
  json: bool,

  /// Print inferred type at the given byte offset (path:offset).
  #[arg(long)]
  type_at: Option<String>,

  /// Print resolved symbol information at the given byte offset (path:offset).
  #[arg(long)]
  symbol_at: Option<String>,

  /// Print the export map for the given file.
  #[arg(long)]
  exports: Option<PathBuf>,

  /// Additional libs to load (e.g. es2020, dom). Overrides the default lib set.
  #[arg(long)]
  lib: Vec<String>,

  /// Disable automatic default lib loading.
  #[arg(long)]
  no_default_lib: bool,

  /// Target language level for lib selection.
  #[arg(long, value_enum)]
  target: Option<TargetArg>,

  /// Enable strict null checks (disable with --no-strict-null-checks).
  #[arg(long, action = ArgAction::SetTrue)]
  strict_null_checks: bool,

  /// Disable strict null checks.
  #[arg(long, action = ArgAction::SetTrue)]
  no_strict_null_checks: bool,

  /// Disable bivariant function parameter checking.
  #[arg(long, action = ArgAction::SetTrue)]
  no_strict_function_types: bool,

  /// Treat optional properties as exact (like --exactOptionalPropertyTypes).
  #[arg(long, action = ArgAction::SetTrue)]
  exact_optional_property_types: bool,

  /// Enable noUncheckedIndexedAccess semantics.
  #[arg(long, action = ArgAction::SetTrue)]
  no_unchecked_indexed_access: bool,

  /// Use Node/TS style module resolution.
  #[arg(long)]
  node_resolve: bool,

  /// Emit tracing spans (JSON) for profiling/debugging.
  #[arg(long)]
  trace: bool,

  /// Emit tracing spans (JSON) suitable for profiling.
  #[arg(long)]
  profile: bool,
}

#[derive(Clone, Copy)]
enum ResolutionMode {
  Simple,
  Node,
}

#[derive(Clone)]
struct DiskHost {
  state: Arc<Mutex<DiskState>>,
  resolver: ResolutionMode,
  compiler_options: CompilerOptions,
}

#[derive(Default)]
struct DiskState {
  next_id: u32,
  path_to_id: BTreeMap<PathBuf, FileId>,
  id_to_path: Vec<PathBuf>,
  id_to_kind: Vec<FileKind>,
  texts: HashMap<FileId, Arc<str>>,
}

#[derive(Default, Serialize)]
struct JsonQueries {
  #[serde(skip_serializing_if = "Option::is_none")]
  type_at: Option<TypeAtResult>,
  #[serde(skip_serializing_if = "Option::is_none")]
  symbol_at: Option<SymbolAtResult>,
  #[serde(skip_serializing_if = "BTreeMap::is_empty")]
  exports: BTreeMap<String, BTreeMap<String, ExportEntryJson>>,
}

#[derive(Serialize)]
struct JsonOutput {
  diagnostics: Vec<Diagnostic>,
  queries: JsonQueries,
}

#[derive(Serialize)]
struct TypeAtResult {
  file: String,
  offset: u32,
  #[serde(rename = "type")]
  typ: String,
}

#[derive(Serialize)]
struct SymbolAtResult {
  file: String,
  offset: u32,
  symbol: u32,
  #[serde(skip_serializing_if = "Option::is_none")]
  name: Option<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  def: Option<u32>,
  #[serde(skip_serializing_if = "Option::is_none")]
  def_file: Option<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  #[serde(rename = "type")]
  typ: Option<String>,
}

#[derive(Serialize)]
struct ExportEntryJson {
  symbol: u32,
  #[serde(skip_serializing_if = "Option::is_none")]
  def: Option<u32>,
  #[serde(skip_serializing_if = "Option::is_none")]
  #[serde(rename = "type")]
  typ: Option<String>,
}

#[derive(Clone, Copy, ValueEnum)]
enum TargetArg {
  Es3,
  Es5,
  Es2015,
  Es2016,
  Es2017,
  Es2018,
  Es2019,
  Es2020,
  Es2021,
  Es2022,
  EsNext,
}

impl From<TargetArg> for ScriptTarget {
  fn from(value: TargetArg) -> Self {
    match value {
      TargetArg::Es3 => ScriptTarget::Es3,
      TargetArg::Es5 => ScriptTarget::Es5,
      TargetArg::Es2015 => ScriptTarget::Es2015,
      TargetArg::Es2016 => ScriptTarget::Es2016,
      TargetArg::Es2017 => ScriptTarget::Es2017,
      TargetArg::Es2018 => ScriptTarget::Es2018,
      TargetArg::Es2019 => ScriptTarget::Es2019,
      TargetArg::Es2020 => ScriptTarget::Es2020,
      TargetArg::Es2021 => ScriptTarget::Es2021,
      TargetArg::Es2022 => ScriptTarget::Es2022,
      TargetArg::EsNext => ScriptTarget::EsNext,
    }
  }
}

fn main() -> ExitCode {
  let cli = Cli::parse();
  match cli.command {
    Commands::Typecheck(args) => run_typecheck(args),
  }
}

fn run_typecheck(args: TypecheckArgs) -> ExitCode {
  init_tracing(args.trace || args.profile);

  let resolution = if args.node_resolve {
    ResolutionMode::Node
  } else {
    ResolutionMode::Simple
  };

  let options = match build_compiler_options(&args) {
    Ok(opts) => opts,
    Err(err) => {
      eprintln!("{err}");
      return ExitCode::FAILURE;
    }
  };

  let (host, roots) = match DiskHost::new(&args.entries, resolution, options) {
    Ok(res) => res,
    Err(err) => {
      eprintln!("{err}");
      return ExitCode::FAILURE;
    }
  };

  let program = Program::new(host.clone(), roots);
  let mut diagnostics = program.check();
  sort_diagnostics(&mut diagnostics);

  let type_at = match args.type_at {
    Some(raw) => match query_type_at(&program, &host, &raw) {
      Ok(res) => res,
      Err(err) => {
        eprintln!("{err}");
        return ExitCode::FAILURE;
      }
    },
    None => None,
  };

  let symbol_at = match args.symbol_at {
    Some(raw) => match query_symbol_at(&program, &host, &raw) {
      Ok(res) => res,
      Err(err) => {
        eprintln!("{err}");
        return ExitCode::FAILURE;
      }
    },
    None => None,
  };

  let exports = match args.exports {
    Some(path) => match query_exports(&program, &host, path) {
      Ok(res) => res,
      Err(err) => {
        eprintln!("{err}");
        return ExitCode::FAILURE;
      }
    },
    None => BTreeMap::new(),
  };

  let snapshot = host.snapshot();

  if args.json {
    let output = JsonOutput {
      diagnostics: diagnostics.clone(),
      queries: JsonQueries {
        type_at,
        symbol_at,
        exports,
      },
    };
    match serde_json::to_string_pretty(&output) {
      Ok(serialized) => {
        println!("{serialized}");
      }
      Err(err) => {
        eprintln!("failed to serialize JSON: {err}");
        return ExitCode::FAILURE;
      }
    }
  } else {
    for diagnostic in &diagnostics {
      println!("{}", render_diagnostic(&snapshot, diagnostic));
    }

    if let Some(type_at) = &type_at {
      println!(
        "type at {}:{}: {}",
        type_at.file, type_at.offset, type_at.typ
      );
    }

    if let Some(symbol_at) = &symbol_at {
      println!(
        "symbol at {}:{} -> {}{}",
        symbol_at.file,
        symbol_at.offset,
        symbol_at.symbol,
        symbol_at
          .name
          .as_ref()
          .map(|n| format!(" ({n})"))
          .unwrap_or_default()
      );
      if let Some(ref typ) = symbol_at.typ {
        println!("  type: {typ}");
      }
      if let Some(def) = symbol_at.def {
        if let Some(file) = &symbol_at.def_file {
          println!("  def: {def} in {file}");
        } else {
          println!("  def: {def}");
        }
      }
    }

    if !exports.is_empty() {
      for (file, map) in &exports {
        println!("exports for {file}:");
        for (name, entry) in map {
          let mut line = format!("  {name} -> symbol {}", entry.symbol);
          if let Some(def) = entry.def {
            line.push_str(&format!(", def {def}"));
          }
          if let Some(typ) = &entry.typ {
            line.push_str(&format!(", type {typ}"));
          }
          println!("{line}");
        }
      }
    }
  }

  let has_errors = diagnostics.iter().any(|d| d.severity == Severity::Error);
  if has_errors {
    ExitCode::FAILURE
  } else {
    ExitCode::SUCCESS
  }
}

fn build_compiler_options(args: &TypecheckArgs) -> Result<CompilerOptions, String> {
  let mut options = CompilerOptions::default();
  if let Some(target) = args.target {
    options.target = target.into();
  }
  options.no_default_lib = args.no_default_lib;

  if !args.lib.is_empty() {
    let mut libs = Vec::new();
    for raw in &args.lib {
      libs.push(parse_lib_name(raw)?);
    }
    libs.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    libs.dedup();
    options.libs = libs;
  }

  // Type system toggles.
  if args.strict_null_checks {
    options.strict_null_checks = true;
  }
  if args.no_strict_null_checks {
    options.strict_null_checks = false;
  }
  if args.no_strict_function_types {
    options.strict_function_types = false;
  }
  if args.exact_optional_property_types {
    options.exact_optional_property_types = true;
  }
  if args.no_unchecked_indexed_access {
    options.no_unchecked_indexed_access = true;
  }

  // Convenience: include DOM if explicitly requested via --lib dom.
  if options.libs.contains(&LibName::Dom) {
    options.include_dom = true;
  }

  Ok(options)
}

fn parse_lib_name(raw: &str) -> Result<LibName, String> {
  let normalized = raw.trim().to_ascii_lowercase();
  match normalized.as_str() {
    "es5" => Ok(LibName::Es5),
    "es2015" | "es6" => Ok(LibName::Es2015),
    "es2016" => Ok(LibName::Es2016),
    "es2017" => Ok(LibName::Es2017),
    "es2018" => Ok(LibName::Es2018),
    "es2019" => Ok(LibName::Es2019),
    "es2020" => Ok(LibName::Es2020),
    "es2021" => Ok(LibName::Es2021),
    "es2022" => Ok(LibName::Es2022),
    "esnext" => Ok(LibName::EsNext),
    "dom" => Ok(LibName::Dom),
    other => Err(format!("unknown lib '{other}'")),
  }
}

fn init_tracing(enabled: bool) {
  if !enabled {
    return;
  }
  let _ = tracing_subscriber::fmt()
    .with_span_events(FmtSpan::CLOSE)
    .with_max_level(Level::DEBUG)
    .json()
    .with_ansi(false)
    .try_init();
}

impl DiskHost {
  fn new(
    entries: &[PathBuf],
    resolver: ResolutionMode,
    compiler_options: CompilerOptions,
  ) -> Result<(Self, Vec<FileId>), String> {
    let mut state = DiskState::default();
    let mut roots = Vec::new();
    for entry in entries {
      let canonical = canonicalize_path(entry)
        .map_err(|err| format!("failed to read entry {}: {err}", entry.to_string_lossy()))?;
      let id = state.intern_path(canonical);
      roots.push(id);
    }

    Ok((
      DiskHost {
        state: Arc::new(Mutex::new(state)),
        resolver,
        compiler_options,
      },
      roots,
    ))
  }

  fn id_for_path(&self, path: &Path) -> Option<FileId> {
    let canonical = canonicalize_path(path).ok()?;
    let state = self.state.lock().unwrap();
    state.path_to_id.get(&canonical).copied()
  }

  fn path_for_id(&self, file: FileId) -> Option<PathBuf> {
    let state = self.state.lock().unwrap();
    state.id_to_path.get(file.0 as usize).cloned()
  }

  fn snapshot(&self) -> HostSnapshot {
    let state = self.state.lock().unwrap();
    let mut names = Vec::with_capacity(state.id_to_path.len());
    let mut texts = Vec::with_capacity(state.id_to_path.len());
    for (idx, path) in state.id_to_path.iter().enumerate() {
      names.push(path.display().to_string());
      let id = FileId(idx as u32);
      let text = match state.texts.get(&id) {
        Some(text) => text.as_ref().to_string(),
        None => fs::read_to_string(path).unwrap_or_default(),
      };
      texts.push(text);
    }
    HostSnapshot { names, texts }
  }
}

impl DiskState {
  fn intern_path(&mut self, path: PathBuf) -> FileId {
    if let Some(id) = self.path_to_id.get(&path) {
      return *id;
    }
    let id = FileId(self.next_id);
    self.next_id += 1;
    let kind = file_kind_for(&path);
    self.path_to_id.insert(path.clone(), id);
    self.id_to_path.push(path);
    self.id_to_kind.push(kind);
    id
  }
}

impl Host for DiskHost {
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    let mut state = self.state.lock().unwrap();
    if let Some(text) = state.texts.get(&file) {
      return Ok(text.clone());
    }
    let path = state
      .id_to_path
      .get(file.0 as usize)
      .cloned()
      .ok_or_else(|| HostError::new(format!("unknown file {file:?}")))?;
    let text = fs::read_to_string(&path)
      .map_err(|err| HostError::new(format!("failed to read {}: {err}", path.display())))?;
    let arc: Arc<str> = Arc::from(text);
    state.texts.insert(file, arc.clone());
    Ok(arc)
  }

  fn resolve(&self, from: FileId, specifier: &str) -> Option<FileId> {
    let base = self.path_for_id(from)?;
    let resolved = self.resolver.resolve(&base, specifier)?;
    let canonical = canonicalize_path(&resolved).ok()?;
    let mut state = self.state.lock().unwrap();
    Some(state.intern_path(canonical))
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.compiler_options.clone()
  }

  fn file_kind(&self, file: FileId) -> FileKind {
    let state = self.state.lock().unwrap();
    state
      .id_to_kind
      .get(file.0 as usize)
      .copied()
      .unwrap_or(FileKind::Ts)
  }
}

struct HostSnapshot {
  names: Vec<String>,
  texts: Vec<String>,
}

impl SourceProvider for HostSnapshot {
  fn file_name(&self, file: FileId) -> Option<&str> {
    self.names.get(file.0 as usize).map(|s| s.as_str())
  }

  fn file_text(&self, file: FileId) -> Option<&str> {
    self.texts.get(file.0 as usize).map(|s| s.as_str())
  }
}

impl ResolutionMode {
  fn resolve(&self, from: &Path, specifier: &str) -> Option<PathBuf> {
    match self {
      ResolutionMode::Simple => resolve_relative(from, specifier),
      ResolutionMode::Node => resolve_node_like(from, specifier),
    }
  }
}

fn resolve_relative(from: &Path, specifier: &str) -> Option<PathBuf> {
  let base_dir = from.parent().unwrap_or_else(|| Path::new(""));
  let joined = base_dir.join(specifier);
  resolve_with_candidates(&joined)
}

fn resolve_node_like(from: &Path, specifier: &str) -> Option<PathBuf> {
  if specifier.starts_with("./") || specifier.starts_with("../") || specifier.starts_with('/') {
    return resolve_relative(from, specifier);
  }

  let mut current = Some(from.parent().unwrap_or_else(|| Path::new("")));
  while let Some(dir) = current {
    let candidate = dir.join("node_modules").join(specifier);
    if let Some(found) = resolve_with_candidates(&candidate) {
      return Some(found);
    }
    current = dir.parent();
  }

  None
}

fn resolve_with_candidates(base: &Path) -> Option<PathBuf> {
  let candidates = candidate_paths(base);
  for cand in candidates {
    if cand.is_file() {
      if let Ok(canon) = canonicalize_path(&cand) {
        return Some(canon);
      }
    }
  }
  None
}

fn candidate_paths(base: &Path) -> Vec<PathBuf> {
  const EXTENSIONS: &[&str] = &["ts", "d.ts", "tsx", "js", "jsx"];
  let mut candidates = Vec::new();
  let has_extension = has_known_extension(base);
  if has_extension {
    candidates.push(base.to_path_buf());
  } else {
    for ext in EXTENSIONS {
      candidates.push(with_extension(base, ext));
    }
  }

  if !has_extension || base.is_dir() {
    let base_dir = base;
    for ext in EXTENSIONS {
      candidates.push(base_dir.join("index").with_extension(ext));
    }
  }

  candidates
}

fn has_known_extension(path: &Path) -> bool {
  let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
  name.ends_with(".d.ts")
    || matches!(
      path.extension().and_then(|e| e.to_str()),
      Some("ts" | "tsx" | "js" | "jsx")
    )
}

fn with_extension(base: &Path, ext: &str) -> PathBuf {
  if ext == "d.ts" {
    let mut path = base.to_path_buf();
    let current_ext = path.extension().and_then(|e| e.to_str()).unwrap_or("");
    if current_ext == "ts" || current_ext == "tsx" || current_ext == "js" || current_ext == "jsx" {
      path.set_extension("d.ts");
      return path;
    }
    path.with_extension("d.ts")
  } else {
    base.with_extension(ext)
  }
}

fn canonicalize_path(path: &Path) -> std::io::Result<PathBuf> {
  let canonical = if path.is_absolute() {
    path.to_path_buf()
  } else {
    std::env::current_dir()?.join(path)
  };
  canonical.canonicalize()
}

fn file_kind_for(path: &Path) -> FileKind {
  let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
  if name.ends_with(".d.ts") {
    return FileKind::Dts;
  }
  match path.extension().and_then(|e| e.to_str()) {
    Some("ts") => FileKind::Ts,
    Some("tsx") => FileKind::Tsx,
    Some("js") => FileKind::Js,
    Some("jsx") => FileKind::Jsx,
    _ => FileKind::Ts,
  }
}

fn parse_offset_arg(raw: &str) -> Result<(PathBuf, u32), String> {
  let (path, offset) = raw
    .rsplit_once(':')
    .ok_or_else(|| format!("expected <path:offset>, got '{raw}'"))?;
  let offset = offset
    .parse::<u32>()
    .map_err(|err| format!("invalid offset in '{raw}': {err}"))?;
  Ok((PathBuf::from(path), offset))
}

fn query_type_at(
  program: &Program,
  host: &DiskHost,
  raw: &str,
) -> Result<Option<TypeAtResult>, String> {
  let (path, offset) = parse_offset_arg(raw)?;
  let file_id = host
    .id_for_path(&path)
    .ok_or_else(|| format!("unknown file in --type-at: {}", path.to_string_lossy()))?;
  match program.type_at(file_id, offset) {
    Some(ty) => {
      let typ = program.display_type(ty).to_string();
      let file = host
        .path_for_id(file_id)
        .map(|p| p.display().to_string())
        .unwrap_or_else(|| path.to_string_lossy().to_string());
      Ok(Some(TypeAtResult { file, offset, typ }))
    }
    None => Ok(None),
  }
}

fn query_symbol_at(
  program: &Program,
  host: &DiskHost,
  raw: &str,
) -> Result<Option<SymbolAtResult>, String> {
  let (path, offset) = parse_offset_arg(raw)?;
  let file_id = host
    .id_for_path(&path)
    .ok_or_else(|| format!("unknown file in --symbol-at: {}", path.to_string_lossy()))?;
  let symbol = match program.symbol_at(file_id, offset) {
    Some(sym) => sym,
    None => return Ok(None),
  };
  let info = program.symbol_info(symbol);
  let (def, def_file, typ, name) = match info {
    Some(info) => {
      let def_file = info
        .file
        .and_then(|id| host.path_for_id(id))
        .map(|p| p.display().to_string());
      let typ = info.type_id.map(|id| program.display_type(id).to_string());
      (info.def.map(|d| d.0), def_file, typ, info.name)
    }
    None => (None, None, None, None),
  };

  let file = host
    .path_for_id(file_id)
    .map(|p| p.display().to_string())
    .unwrap_or_else(|| path.to_string_lossy().to_string());

  Ok(Some(SymbolAtResult {
    file,
    offset,
    symbol: symbol.0,
    name,
    def,
    def_file,
    typ,
  }))
}

fn query_exports(
  program: &Program,
  host: &DiskHost,
  path: PathBuf,
) -> Result<BTreeMap<String, BTreeMap<String, ExportEntryJson>>, String> {
  let file_id = host
    .id_for_path(&path)
    .ok_or_else(|| format!("unknown file in --exports: {}", path.to_string_lossy()))?;
  let exports = program.exports_of(file_id);
  let mut map: BTreeMap<String, ExportEntryJson> = BTreeMap::new();
  for (name, entry) in exports {
    let typ = entry.type_id.map(|t| program.display_type(t).to_string());
    map.insert(
      name,
      ExportEntryJson {
        symbol: entry.symbol.0,
        def: entry.def.map(|d| d.0),
        typ,
      },
    );
  }
  let mut outer = BTreeMap::new();
  let file_name = host
    .path_for_id(file_id)
    .map(|p| p.display().to_string())
    .unwrap_or_else(|| path.to_string_lossy().to_string());
  outer.insert(file_name, map);
  Ok(outer)
}

fn sort_diagnostics(diagnostics: &mut [Diagnostic]) {
  for diag in diagnostics.iter_mut() {
    diag.labels.sort();
  }
  diagnostics.sort_by(|a, b| {
    a.primary
      .file
      .cmp(&b.primary.file)
      .then(a.primary.range.start.cmp(&b.primary.range.start))
      .then(a.code.cmp(&b.code))
      .then(a.message.cmp(&b.message))
  });
}
