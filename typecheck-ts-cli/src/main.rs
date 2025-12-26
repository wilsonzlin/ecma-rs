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
use typecheck_ts::resolve::{canonicalize_path, normalize_path, NodeResolver, ResolveOptions};
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

#[derive(Clone)]
struct DiskHost {
  state: Arc<Mutex<DiskState>>,
  resolver: NodeResolver,
  compiler_options: CompilerOptions,
}

#[derive(Default, Clone)]
struct DiskState {
  next_id: u32,
  path_to_id: BTreeMap<String, FileId>,
  id_to_path: Vec<PathBuf>,
  id_to_name: Vec<String>,
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
  exports: BTreeMap<String, ExportSpacesJson>,
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

#[derive(Default, Serialize)]
struct ExportSpacesJson {
  #[serde(skip_serializing_if = "BTreeMap::is_empty")]
  values: BTreeMap<String, ExportEntryJson>,
  #[serde(skip_serializing_if = "BTreeMap::is_empty")]
  types: BTreeMap<String, ExportEntryJson>,
  #[serde(skip_serializing_if = "BTreeMap::is_empty")]
  namespaces: BTreeMap<String, ExportEntryJson>,
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

  let resolution = ResolveOptions {
    node_modules: args.node_resolve,
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
    let snapshot = host.snapshot();
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
      for (file, spaces) in &exports {
        println!("exports for {file}:");
        print_export_space("  values", &spaces.values);
        print_export_space("  types", &spaces.types);
        print_export_space("  namespaces", &spaces.namespaces);
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
    resolver: ResolveOptions,
    compiler_options: CompilerOptions,
  ) -> Result<(Self, Vec<FileId>), String> {
    let mut state = DiskState::default();
    let mut roots = Vec::new();
    for entry in entries {
      let canonical = canonicalize_path(entry)
        .map_err(|err| format!("failed to read entry {}: {err}", entry.to_string_lossy()))?;
      let id = state.intern_canonical(canonical);
      roots.push(id);
    }

    Ok((
      DiskHost {
        state: Arc::new(Mutex::new(state)),
        resolver: NodeResolver::new(resolver),
        compiler_options,
      },
      roots,
    ))
  }

  fn id_for_path(&self, path: &Path) -> Option<FileId> {
    let canonical = canonicalize_path(path).ok()?;
    let state = self.state.lock().unwrap();
    state.path_to_id.get(&normalize_path(&canonical)).copied()
  }

  fn path_for_id(&self, file: FileId) -> Option<PathBuf> {
    let state = self.state.lock().unwrap();
    state.id_to_path.get(file.0 as usize).cloned()
  }

  fn display_name(&self, file: FileId) -> Option<String> {
    let state = self.state.lock().unwrap();
    state.id_to_name.get(file.0 as usize).cloned()
  }

  fn snapshot(&self) -> HostSnapshot {
    let mut state = self.state.lock().unwrap();
    let paths = state.id_to_path.clone();
    let names = state.id_to_name.clone();
    let mut texts = Vec::with_capacity(paths.len());
    for (idx, path) in paths.iter().enumerate() {
      let id = FileId(idx as u32);
      let text = match state.texts.get(&id) {
        Some(text) => Some(text.as_ref().to_string()),
        None => match fs::read_to_string(path) {
          Ok(text) => {
            state.texts.insert(id, Arc::from(text.clone()));
            Some(text)
          }
          Err(err) => {
            tracing::warn!("failed to read {}: {err}", path.display());
            None
          }
        },
      };
      texts.push(text);
    }
    HostSnapshot { names, texts }
  }
}

impl DiskState {
  fn intern_with_normalized(&mut self, path: PathBuf, normalized: String) -> FileId {
    if let Some(id) = self.path_to_id.get(&normalized) {
      return *id;
    }
    let id = FileId(self.next_id);
    self.next_id += 1;
    let kind = file_kind_for(&path);
    self.path_to_id.insert(normalized.clone(), id);
    self.id_to_path.push(path);
    self.id_to_name.push(normalized);
    self.id_to_kind.push(kind);
    id
  }

  fn intern_canonical(&mut self, path: PathBuf) -> FileId {
    let normalized = normalize_path(&path);
    self.intern_with_normalized(path, normalized)
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
    let normalized = normalize_path(&resolved);
    let mut state = self.state.lock().unwrap();
    Some(state.intern_with_normalized(resolved, normalized))
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
  texts: Vec<Option<String>>,
}

impl SourceProvider for HostSnapshot {
  fn file_name(&self, file: FileId) -> Option<&str> {
    self.names.get(file.0 as usize).map(|s| s.as_str())
  }

  fn file_text(&self, file: FileId) -> Option<&str> {
    self
      .texts
      .get(file.0 as usize)
      .and_then(|text| text.as_deref())
  }
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
        .display_name(file_id)
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
      let def_file = info.file.and_then(|id| host.display_name(id));
      let typ = info.type_id.map(|id| program.display_type(id).to_string());
      (info.def.map(|d| d.0), def_file, typ, info.name)
    }
    None => (None, None, None, None),
  };

  let file = host
    .display_name(file_id)
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
) -> Result<BTreeMap<String, ExportSpacesJson>, String> {
  let file_id = host
    .id_for_path(&path)
    .ok_or_else(|| format!("unknown file in --exports: {}", path.to_string_lossy()))?;
  let exports = program.exports_of(file_id);
  let mut spaces = ExportSpacesJson::default();
  insert_exports(&mut spaces.values, exports.values, program);
  insert_exports(&mut spaces.types, exports.types, program);
  insert_exports(&mut spaces.namespaces, exports.namespaces, program);
  let mut outer = BTreeMap::new();
  let file_name = host
    .display_name(file_id)
    .unwrap_or_else(|| path.to_string_lossy().to_string());
  outer.insert(file_name, spaces);
  Ok(outer)
}

fn print_export_space(label: &str, exports: &BTreeMap<String, ExportEntryJson>) {
  if exports.is_empty() {
    return;
  }
  println!("{label}:");
  for (name, entry) in exports {
    let mut line = format!("    {name} -> symbol {}", entry.symbol);
    if let Some(def) = entry.def {
      line.push_str(&format!(", def {def}"));
    }
    if let Some(typ) = &entry.typ {
      line.push_str(&format!(", type {typ}"));
    }
    println!("{line}");
  }
}

fn insert_exports(
  target: &mut BTreeMap<String, ExportEntryJson>,
  exports: typecheck_ts::ExportMap,
  program: &Program,
) {
  for (name, entry) in exports {
    let typ = entry.type_id.map(|t| program.display_type(t).to_string());
    target.insert(
      name,
      ExportEntryJson {
        symbol: entry.symbol.0,
        def: entry.def.map(|d| d.0),
        typ,
      },
    );
  }
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
