use crate::db::{collect_specifiers, Db, Database};
use crate::graph::ModuleGraph;
use crate::host::{FileId, Host};
use crate::options::CompilerOptions;
use crate::{Diagnostic, ParseOutput};
use std::collections::BTreeSet;
use std::collections::VecDeque;
use std::sync::Arc;

/// Input key representing a program within the salsa database.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ProgramInput {
  /// Root files that seed module graph construction.
  pub roots: Vec<FileId>,
}

/// User-facing program handle.
///
/// # Example
///
/// ```
/// use std::sync::Arc;
/// use typecheck_ts_salsa6::{CompilerOptions, FileId, FileKind, Host, Program, Resolver};
///
/// struct SingleFileHost;
///
/// impl Resolver for SingleFileHost {
///   fn resolve(&self, _from: FileId, _spec: &str) -> Option<FileId> {
///     None
///   }
/// }
///
/// impl Host for SingleFileHost {
///   fn file_text(&self, _file: FileId) -> Arc<str> {
///     Arc::<str>::from("function () {")
///   }
///
///   fn file_kind(&self, _file: FileId) -> FileKind {
///     FileKind::Ts
///   }
///
///   fn options(&self) -> CompilerOptions {
///     CompilerOptions::default()
///   }
/// }
///
/// let mut program = Program::new(Arc::new(SingleFileHost), vec![FileId(0)]);
/// let diagnostics = program.check_parse_only();
/// assert_eq!(diagnostics.len(), 1);
/// ```
pub struct Program {
  db: Database,
  host: Arc<dyn Host>,
  input: ProgramInput,
  registered_files: BTreeSet<FileId>,
  registered_resolutions: BTreeSet<(FileId, Arc<str>)>,
}

impl Program {
  /// Creates a new program backed by `host` and `root_files`.
  pub fn new(host: Arc<dyn Host>, root_files: impl Into<Vec<FileId>>) -> Self {
    let mut db = Database::new();
    let options: CompilerOptions = host.options();
    db.set_compiler_options(options);

    let mut roots = root_files.into();
    roots.sort();
    roots.dedup();

    let mut program = Self {
      db,
      host,
      input: ProgramInput { roots },
      registered_files: BTreeSet::new(),
      registered_resolutions: BTreeSet::new(),
    };

    let roots = program.input.roots.clone();
    for root in roots {
      program.register_file(root);
    }

    program
  }

  /// Returns the underlying salsa database.
  pub fn db(&self) -> &Database {
    &self.db
  }

  /// Returns the module graph for this program.
  pub fn module_graph(&mut self) -> ModuleGraph {
    self.prime_reachable();
    self.db.module_graph(self.input.clone())
  }

  /// Parses the given file, returning the AST and diagnostics.
  pub fn parse_file(&mut self, file: FileId) -> ParseOutput {
    self.register_file(file);
    self.db.parse(file)
  }

  /// Performs a parse-only check across all reachable files.
  pub fn check_parse_only(&mut self) -> Vec<Diagnostic<FileId>> {
    let files = self.prime_reachable();

    let mut diagnostics = Vec::new();
    for file in files {
      let mut diags = self.db.parse(file).diagnostics;
      diagnostics.append(&mut diags);
    }

    diagnostics
  }

  fn register_file(&mut self, file: FileId) {
    if self.registered_files.insert(file) {
      let text = self.host.file_text(file);
      let kind = self.host.file_kind(file);
      self.db.set_file_text(file, text);
      self.db.set_file_kind(file, kind);
    }
  }

  fn register_resolution(&mut self, from: FileId, spec: Arc<str>) -> Option<FileId> {
    if self.registered_resolutions.insert((from, spec.clone())) {
      let target = self.host.resolve(from, &spec);
      self.db.set_module_resolve(from, spec.clone(), target);
      if let Some(target) = target {
        self.register_file(target);
      }
      target
    } else {
      self.db.module_resolve(from, spec)
    }
  }

  fn prime_reachable(&mut self) -> BTreeSet<FileId> {
    let mut queue: VecDeque<FileId> = self.input.roots.iter().copied().collect();
    let mut visited = BTreeSet::new();

    while let Some(file) = queue.pop_front() {
      if !visited.insert(file) {
        continue;
      }

      self.register_file(file);
      let parsed = self.db.parse(file);
      for spec in collect_specifiers(&parsed.ast) {
        if let Some(target) = self.register_resolution(file, spec.clone()) {
          if !visited.contains(&target) {
            queue.push_back(target);
          }
        }
      }
    }

    visited
  }
}
