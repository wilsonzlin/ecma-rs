use clap::{ArgAction, Args, Parser, Subcommand, ValueEnum};
use diagnostics::render::{render_diagnostic_with_options, RenderOptions, SourceProvider};
use diagnostics::{Diagnostic, FileId, Severity};
use serde::Serialize;
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::io::IsTerminal;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::{mpsc, Arc, Mutex};
use std::time::Duration;
use tracing::Level;
use tracing_subscriber::fmt::format::FmtSpan;
use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile, LibName, ScriptTarget};
use typecheck_ts::{FileKey, Host, HostError, Program};

mod tsconfig;

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
  /// TypeScript project file (tsconfig.json) to load.
  #[arg(long, short = 'p')]
  project: Option<PathBuf>,

  /// Entry files to type-check. In project mode these are added as extra roots.
  entries: Vec<PathBuf>,

  /// Emit JSON diagnostics and query results.
  #[arg(long)]
  json: bool,

  /// Force-enable ANSI colors in diagnostics output.
  #[arg(long, action = ArgAction::SetTrue)]
  color: bool,

  /// Disable ANSI colors in diagnostics output.
  #[arg(long, action = ArgAction::SetTrue)]
  no_color: bool,

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

  /// Cancel type checking if it takes longer than this many seconds.
  #[arg(long, value_name = "SECS")]
  timeout_secs: Option<u64>,
}

#[derive(Clone, Copy)]
enum ResolutionMode {
  Simple,
  Node,
}

#[derive(Clone)]
struct ModuleResolver {
  mode: ResolutionMode,
  tsconfig: Option<TsconfigResolver>,
}

#[derive(Clone)]
struct TsconfigResolver {
  base_url: PathBuf,
  paths: Vec<TsconfigPathMapping>,
}

#[derive(Clone)]
struct TsconfigPathMapping {
  prefix: String,
  suffix: String,
  has_wildcard: bool,
  substitutions: Vec<String>,
}

#[derive(Clone)]
struct DiskHost {
  state: Arc<Mutex<DiskState>>,
  resolver: ModuleResolver,
  compiler_options: CompilerOptions,
  lib_files: Vec<LibFile>,
}

#[derive(Default, Clone)]
struct DiskState {
  path_to_key: BTreeMap<PathBuf, FileKey>,
  key_to_path: HashMap<FileKey, PathBuf>,
  key_to_kind: HashMap<FileKey, FileKind>,
  texts: HashMap<FileKey, Arc<str>>,
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
  files: Vec<String>,
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
  symbol: u64,
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
  symbol: u64,
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

  let project = match args.project.as_ref() {
    Some(path) => match tsconfig::load_project_config(path) {
      Ok(cfg) => Some(cfg),
      Err(err) => {
        eprintln!("{err}");
        return ExitCode::FAILURE;
      }
    },
    None => None,
  };

  let options_base = project
    .as_ref()
    .map(|cfg| cfg.compiler_options.clone())
    .unwrap_or_default();
  let options = match build_compiler_options(&args, options_base) {
    Ok(opts) => opts,
    Err(err) => {
      eprintln!("{err}");
      return ExitCode::FAILURE;
    }
  };

  let resolution = if args.node_resolve {
    ResolutionMode::Node
  } else if matches!(
    options
      .module_resolution
      .as_deref()
      .map(|s| s.trim().to_ascii_lowercase())
      .as_deref(),
    Some("node" | "node10" | "node16" | "nodenext" | "bundler")
  ) {
    ResolutionMode::Node
  } else {
    ResolutionMode::Simple
  };

  let mut root_paths = Vec::new();
  if let Some(cfg) = project.as_ref() {
    root_paths.extend(cfg.root_files.iter().cloned());
  }
  for entry in &args.entries {
    let canonical = match canonicalize_path(entry) {
      Ok(path) => path,
      Err(err) => {
        eprintln!("failed to read entry {}: {err}", entry.to_string_lossy());
        return ExitCode::FAILURE;
      }
    };
    root_paths.push(canonical);
  }
  root_paths.sort_by(|a, b| a.display().to_string().cmp(&b.display().to_string()));
  root_paths.dedup();

  if project.is_none() && root_paths.is_empty() {
    eprintln!("no entry files provided (expected at least one file, or use --project)");
    return ExitCode::FAILURE;
  }

  let tsconfig_resolver = project.as_ref().and_then(TsconfigResolver::from_project);
  let resolver = ModuleResolver {
    mode: resolution,
    tsconfig: tsconfig_resolver,
  };

  let extra_libs = match project.as_ref() {
    Some(cfg) => match load_type_libs(cfg, &options) {
      Ok(libs) => libs,
      Err(err) => {
        eprintln!("{err}");
        return ExitCode::FAILURE;
      }
    },
    None => Vec::new(),
  };

  let (host, roots) = match DiskHost::new(&root_paths, resolver, options, extra_libs) {
    Ok(res) => res,
    Err(err) => {
      eprintln!("{err}");
      return ExitCode::FAILURE;
    }
  };

  let program = Arc::new(Program::new(host.clone(), roots));
  let _timeout_guard = ProgramTimeoutGuard::new(&program, args.timeout_secs);
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
    let mut files: Vec<String> = program
      .files()
      .into_iter()
      .filter_map(|id| program.file_key(id))
      .map(|key| key.to_string())
      .collect();
    files.sort();
    let output = JsonOutput {
      files,
      diagnostics: diagnostics.clone(),
      queries: JsonQueries {
        type_at,
        symbol_at,
        exports,
      },
    };
    let stdout = std::io::stdout();
    let mut handle = stdout.lock();
    if let Err(err) = serde_json::to_writer_pretty(&mut handle, &output)
      .and_then(|()| writeln!(&mut handle).map_err(serde_json::Error::io))
    {
      eprintln!("failed to serialize JSON: {err}");
      return ExitCode::FAILURE;
    }
  } else {
    let color = if args.color {
      true
    } else if args.no_color {
      false
    } else {
      std::io::stdout().is_terminal()
    };
    let render_options = RenderOptions {
      context_lines: 1,
      color,
      ..RenderOptions::default()
    };
    let snapshot = snapshot_from_program(&program);
    for diagnostic in &diagnostics {
      println!(
        "{}",
        render_diagnostic_with_options(&snapshot, diagnostic, render_options)
      );
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

fn build_compiler_options(
  args: &TypecheckArgs,
  mut options: CompilerOptions,
) -> Result<CompilerOptions, String> {
  if let Some(target) = args.target {
    options.target = target.into();
  }
  if args.no_default_lib {
    options.no_default_lib = true;
  }

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

struct ProgramTimeoutGuard {
  done: Option<mpsc::Sender<()>>,
  handle: Option<std::thread::JoinHandle<()>>,
}

impl ProgramTimeoutGuard {
  fn new(program: &Arc<Program>, timeout_secs: Option<u64>) -> Self {
    let Some(secs) = timeout_secs else {
      return Self {
        done: None,
        handle: None,
      };
    };

    let timeout = Duration::from_secs(secs);
    if timeout.is_zero() {
      program.cancel();
      return Self {
        done: None,
        handle: None,
      };
    }

    let (done_tx, done_rx) = mpsc::channel::<()>();
    let program = Arc::clone(program);
    let handle = std::thread::Builder::new()
      .name("typecheck-ts-cli-timeout".into())
      .spawn(move || {
        if matches!(
          done_rx.recv_timeout(timeout),
          Err(mpsc::RecvTimeoutError::Timeout)
        ) {
          program.cancel();
        }
      })
      .expect("spawn typecheck-ts-cli timeout thread");

    Self {
      done: Some(done_tx),
      handle: Some(handle),
    }
  }
}

impl Drop for ProgramTimeoutGuard {
  fn drop(&mut self) {
    if let Some(done) = self.done.take() {
      let _ = done.send(());
    }
    if let Some(handle) = self.handle.take() {
      let _ = handle.join();
    }
  }
}

impl DiskHost {
  fn new(
    entries: &[PathBuf],
    resolver: ModuleResolver,
    compiler_options: CompilerOptions,
    lib_files: Vec<LibFile>,
  ) -> Result<(Self, Vec<FileKey>), String> {
    let mut state = DiskState::default();
    let mut roots = Vec::new();
    for entry in entries {
      let canonical = canonicalize_path(entry)
        .map_err(|err| format!("failed to read entry {}: {err}", entry.to_string_lossy()))?;
      let key = state.intern_path(canonical);
      roots.push(key);
    }

    Ok((
      DiskHost {
        state: Arc::new(Mutex::new(state)),
        resolver,
        compiler_options,
        lib_files,
      },
      roots,
    ))
  }

  fn key_for_path(&self, path: &Path) -> Option<FileKey> {
    let canonical = canonicalize_path(path).ok()?;
    let state = self.state.lock().unwrap();
    state.path_to_key.get(&canonical).cloned()
  }

  fn path_for_key(&self, key: &FileKey) -> Option<PathBuf> {
    let state = self.state.lock().unwrap();
    state.key_to_path.get(key).cloned()
  }
}

impl DiskState {
  fn intern_path(&mut self, path: PathBuf) -> FileKey {
    if let Some(key) = self.path_to_key.get(&path) {
      return key.clone();
    }
    let key = FileKey::new(path.display().to_string());
    let kind = file_kind_for(&path);
    self.path_to_key.insert(path.clone(), key.clone());
    self.key_to_path.insert(key.clone(), path);
    self.key_to_kind.insert(key.clone(), kind);
    key
  }
}

impl Host for DiskHost {
  fn file_text(&self, key: &FileKey) -> Result<Arc<str>, HostError> {
    let mut state = self.state.lock().unwrap();
    if let Some(text) = state.texts.get(key) {
      return Ok(text.clone());
    }
    let path = state
      .key_to_path
      .get(key)
      .cloned()
      .ok_or_else(|| HostError::new(format!("unknown file {key}")))?;
    let text = fs::read_to_string(&path)
      .map_err(|err| HostError::new(format!("failed to read {}: {err}", path.display())))?;
    let arc: Arc<str> = Arc::from(text);
    state.texts.insert(key.clone(), arc.clone());
    Ok(arc)
  }

  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey> {
    let base = self.path_for_key(from)?;
    let resolved = self.resolver.resolve(&base, specifier)?;
    let canonical = canonicalize_path(&resolved).ok()?;
    let mut state = self.state.lock().unwrap();
    Some(state.intern_path(canonical))
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.compiler_options.clone()
  }

  fn lib_files(&self) -> Vec<LibFile> {
    self.lib_files.clone()
  }

  fn file_kind(&self, file: &FileKey) -> FileKind {
    let state = self.state.lock().unwrap();
    state.key_to_kind.get(file).copied().unwrap_or(FileKind::Ts)
  }
}

fn load_type_libs(
  cfg: &tsconfig::ProjectConfig,
  options: &CompilerOptions,
) -> Result<Vec<LibFile>, String> {
  let type_roots = match cfg.type_roots.as_ref() {
    Some(roots) => roots.clone(),
    None => default_type_roots(&cfg.root_dir),
  };

  let mut libs = Vec::new();
  if type_roots.is_empty() {
    return Ok(ensure_placeholder_libs(libs, options));
  }

  if let Some(types) = cfg.types.as_ref() {
    for name in types {
      let Some(dir) = resolve_type_package(&type_roots, name) else {
        return Err(format!(
          "failed to resolve type definition package '{name}' from {}",
          cfg.root_dir.display()
        ));
      };
      if let Some(lib) = lib_file_from_type_package(name, &dir)? {
        libs.push(lib);
      }
    }
  } else {
    // No explicit `types` list: include all packages in the type roots.
    let mut packages: BTreeMap<String, PathBuf> = BTreeMap::new();
    for root in &type_roots {
      let entries = match fs::read_dir(root) {
        Ok(entries) => entries,
        Err(_) => continue,
      };
      for entry in entries.filter_map(|e| e.ok()) {
        let path = entry.path();
        let Ok(file_type) = entry.file_type() else {
          continue;
        };
        if !file_type.is_dir() {
          continue;
        }
        let name = entry.file_name().to_string_lossy().to_string();
        packages.entry(name).or_insert(path);
      }
    }

    for (name, dir) in packages {
      if let Some(lib) = lib_file_from_type_package(&name, &dir)? {
        libs.push(lib);
      }
    }
  }

  Ok(ensure_placeholder_libs(libs, options))
}

fn ensure_placeholder_libs(mut libs: Vec<LibFile>, options: &CompilerOptions) -> Vec<LibFile> {
  if !libs.is_empty() || !options.no_default_lib {
    return libs;
  }
  // `typecheck-ts` emits an error diagnostic when zero libs are loaded. Mirror `tsc --noLib`
  // by injecting a single empty `.d.ts` placeholder so the program can proceed without
  // default libs.
  libs.push(LibFile {
    key: FileKey::new("lib:empty.d.ts"),
    name: Arc::from("empty.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(""),
  });
  libs
}

fn default_type_roots(root_dir: &Path) -> Vec<PathBuf> {
  let mut roots = Vec::new();
  for ancestor in root_dir.ancestors() {
    let candidate = ancestor.join("node_modules").join("@types");
    if candidate.is_dir() {
      roots.push(candidate);
    }
  }
  roots
}

fn resolve_type_package(type_roots: &[PathBuf], package: &str) -> Option<PathBuf> {
  for root in type_roots {
    let dir = root.join(package);
    if dir.is_dir() {
      return Some(dir);
    }
  }
  None
}

fn lib_file_from_type_package(package: &str, dir: &Path) -> Result<Option<LibFile>, String> {
  let entry = match type_package_entry(dir) {
    Some(path) => path,
    None => return Ok(None),
  };
  let canonical = entry.canonicalize().unwrap_or(entry.clone());
  let text = fs::read_to_string(&canonical)
    .map_err(|err| format!("failed to read type definitions {}: {err}", canonical.display()))?;
  Ok(Some(LibFile {
    key: FileKey::new(canonical.display().to_string()),
    name: Arc::from(format!("types:{package}")),
    kind: FileKind::Dts,
    text: Arc::from(text),
  }))
}

fn type_package_entry(dir: &Path) -> Option<PathBuf> {
  let pkg_json = dir.join("package.json");
  if pkg_json.is_file() {
    if let Ok(text) = fs::read_to_string(&pkg_json) {
      if let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) {
        let fields = ["types", "typings"];
        for field in fields {
          if let Some(path) = json.get(field).and_then(|v| v.as_str()) {
            let candidate = dir.join(path);
            if candidate.is_file() {
              return Some(candidate);
            }
          }
        }
      }
    }
  }
  let index = dir.join("index.d.ts");
  index.is_file().then_some(index)
}

struct ProgramSourceSnapshot {
  names: HashMap<FileId, String>,
  texts: HashMap<FileId, String>,
}

impl SourceProvider for ProgramSourceSnapshot {
  fn file_name(&self, file: FileId) -> Option<&str> {
    self.names.get(&file).map(|s| s.as_str())
  }

  fn file_text(&self, file: FileId) -> Option<&str> {
    self.texts.get(&file).map(|text| text.as_str())
  }
}

fn snapshot_from_program(program: &Program) -> ProgramSourceSnapshot {
  let mut names = HashMap::new();
  let mut texts = HashMap::new();
  for file in program.files() {
    if let Some(key) = program.file_key(file) {
      names.insert(file, key.to_string());
    }
    if let Some(text) = program.file_text(file) {
      texts.insert(file, text.to_string());
    }
  }
  ProgramSourceSnapshot { names, texts }
}

impl ModuleResolver {
  fn resolve(&self, from: &Path, specifier: &str) -> Option<PathBuf> {
    if let Some(tsconfig) = self.tsconfig.as_ref() {
      if let Some(resolved) = tsconfig.resolve(specifier) {
        return Some(resolved);
      }
    }
    self.mode.resolve(from, specifier)
  }
}

impl TsconfigResolver {
  fn from_project(cfg: &tsconfig::ProjectConfig) -> Option<Self> {
    if cfg.base_url.is_none() && cfg.paths.is_empty() {
      return None;
    }
    let base_url = cfg.base_url.clone().unwrap_or_else(|| cfg.root_dir.clone());
    let mut paths = Vec::new();
    for (pattern, subs) in &cfg.paths {
      let (prefix, suffix, has_wildcard) = match pattern.split_once('*') {
        Some((pre, suf)) => (pre.to_string(), suf.to_string(), true),
        None => (pattern.clone(), String::new(), false),
      };
      paths.push(TsconfigPathMapping {
        prefix,
        suffix,
        has_wildcard,
        substitutions: subs.clone(),
      });
    }
    Some(TsconfigResolver { base_url, paths })
  }

  fn resolve(&self, specifier: &str) -> Option<PathBuf> {
    if is_relative_or_absolute_specifier(specifier) {
      return None;
    }

    if let Some(resolved) = self.resolve_via_paths(specifier) {
      return Some(resolved);
    }

    let candidate = self.base_url.join(specifier);
    resolve_with_candidates(&candidate)
  }

  fn resolve_via_paths(&self, specifier: &str) -> Option<PathBuf> {
    let mut best: Option<(&TsconfigPathMapping, String, (bool, usize, usize))> = None;
    for mapping in &self.paths {
      let Some(capture) = mapping.matches(specifier) else {
        continue;
      };
      let score = (
        !mapping.has_wildcard,
        mapping.prefix.len(),
        mapping.suffix.len(),
      );
      let replace = match best {
        Some((_, _, best_score)) => score > best_score,
        None => true,
      };
      if replace {
        best = Some((mapping, capture, score));
      }
    }

    let (mapping, capture, _) = best?;
    for sub in &mapping.substitutions {
      let substituted = if mapping.has_wildcard {
        sub.replace('*', &capture)
      } else {
        sub.clone()
      };
      let path = Path::new(&substituted);
      let candidate = if path.is_absolute() {
        path.to_path_buf()
      } else {
        self.base_url.join(path)
      };
      if let Some(resolved) = resolve_with_candidates(&candidate) {
        return Some(resolved);
      }
    }
    None
  }
}

impl TsconfigPathMapping {
  fn matches(&self, specifier: &str) -> Option<String> {
    if !self.has_wildcard {
      return (specifier == self.prefix).then_some(String::new());
    }
    let rest = specifier.strip_prefix(&self.prefix)?;
    let middle = rest.strip_suffix(&self.suffix)?;
    Some(middle.to_string())
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

fn is_relative_or_absolute_specifier(specifier: &str) -> bool {
  specifier.starts_with("./")
    || specifier.starts_with("../")
    || Path::new(specifier).is_absolute()
    || specifier.starts_with('/')
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
  const EXTENSIONS: &[&str] = &["ts", "d.ts", "tsx", "js", "jsx"];
  let has_extension = has_known_extension(base);
  let check_candidate = |path: &Path| -> Option<PathBuf> {
    if path.is_file() {
      canonicalize_path(path).ok()
    } else {
      None
    }
  };

  if has_extension {
    if let Some(found) = check_candidate(base) {
      return Some(found);
    }
  } else {
    // Reuse a single `PathBuf` when probing extensions instead of allocating a fresh path per
    // extension.
    let base_buf = base.to_path_buf();
    let mut candidate = base_buf.clone();
    for ext in EXTENSIONS {
      // `set_extension("d.ts")` produces a multi-dot extension. If we then mutate that same
      // `PathBuf` to a single-segment extension (e.g. `"tsx"`), we'd end up with a path like
      // `foo.d.tsx`. Reset to the base path on every iteration to preserve the exact candidates
      // we used to generate with `base.with_extension(ext)`.
      candidate.clone_from(&base_buf);
      candidate.set_extension(ext);
      if let Some(found) = check_candidate(&candidate) {
        return Some(found);
      }
    }
  }

  if !has_extension || base.is_dir() {
    // Resolve `index.*` fallbacks for directories.
    let base_buf = base.join("index");
    let mut candidate = base_buf.clone();
    for ext in EXTENSIONS {
      candidate.clone_from(&base_buf);
      candidate.set_extension(ext);
      if let Some(found) = check_candidate(&candidate) {
        return Some(found);
      }
    }
  }

  None
}

fn has_known_extension(path: &Path) -> bool {
  let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
  name.ends_with(".d.ts")
    || matches!(
      path.extension().and_then(|e| e.to_str()),
      Some("ts" | "tsx" | "js" | "jsx")
    )
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
    .key_for_path(&path)
    .ok_or_else(|| format!("unknown file in --type-at: {}", path.to_string_lossy()))?;
  let file_id = program
    .file_id(&file_id)
    .ok_or_else(|| format!("file not part of program: {}", path.to_string_lossy()))?;
  match program.type_at(file_id, offset) {
    Some(ty) => {
      let typ = program.display_type(ty).to_string();
      let file = host
        .path_for_key(
          &program
            .file_key(file_id)
            .unwrap_or_else(|| FileKey::new(path.display().to_string())),
        )
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
    .key_for_path(&path)
    .ok_or_else(|| format!("unknown file in --symbol-at: {}", path.to_string_lossy()))?;
  let file_id = program
    .file_id(&file_id)
    .ok_or_else(|| format!("file not part of program: {}", path.to_string_lossy()))?;
  let symbol = match program.symbol_at(file_id, offset) {
    Some(sym) => sym,
    None => return Ok(None),
  };
  let info = program.symbol_info(symbol);
  let (def, def_file, typ, name) = match info {
    Some(info) => {
      let def_file = info
        .file
        .and_then(|id| program.file_key(id))
        .and_then(|key| host.path_for_key(&key))
        .map(|p| p.display().to_string());
      let typ = info.type_id.map(|id| program.display_type(id).to_string());
      (info.def.map(|d| d.0), def_file, typ, info.name)
    }
    None => (None, None, None, None),
  };

  let file = host
    .path_for_key(
      &program
        .file_key(file_id)
        .unwrap_or_else(|| FileKey::new(path.display().to_string())),
    )
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
    .key_for_path(&path)
    .ok_or_else(|| format!("unknown file in --exports: {}", path.to_string_lossy()))?;
  let file_id = program
    .file_id(&file_id)
    .ok_or_else(|| format!("file not part of program: {}", path.to_string_lossy()))?;
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
    .path_for_key(
      &program
        .file_key(file_id)
        .unwrap_or_else(|| FileKey::new(path.display().to_string())),
    )
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
