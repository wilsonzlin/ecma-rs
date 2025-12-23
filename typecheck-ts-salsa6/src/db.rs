use crate::graph::ModuleEdge;
use crate::graph::ModuleGraph;
use crate::host::FileId;
use crate::host::FileKind;
use crate::options::CompilerOptions;
use crate::parse::ParseOutput;
use crate::parse::{self};
use crate::program::ProgramInput;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::ModuleName;
use std::collections::BTreeSet;
use std::collections::VecDeque;
use std::sync::Arc;

/// Salsa query interface for the type checker.
#[salsa::query_group(TypecheckStorage)]
pub trait Db: salsa::Database {
  /// Compiler options input.
  #[salsa::input]
  fn compiler_options(&self) -> CompilerOptions;

  /// Source text for a file.
  #[salsa::input]
  fn file_text(&self, file: FileId) -> Arc<str>;

  /// File kind for a file.
  #[salsa::input]
  fn file_kind(&self, file: FileId) -> FileKind;

  /// Host-driven module resolution.
  #[salsa::input]
  fn module_resolve(&self, from: FileId, spec: Arc<str>) -> Option<FileId>;

  /// Parses a single file.
  fn parse(&self, file: FileId) -> ParseOutput;

  /// Computes the module graph for a program.
  fn module_graph(&self, program: ProgramInput) -> ModuleGraph;
}

fn parse(db: &dyn Db, file: FileId) -> ParseOutput {
  parse::parse(db, file)
}

fn module_graph(db: &dyn Db, program: ProgramInput) -> ModuleGraph {
  let mut graph = ModuleGraph::default();
  let mut queue: VecDeque<FileId> = program.roots.iter().copied().collect();
  let mut seen = BTreeSet::new();

  while let Some(file) = queue.pop_front() {
    if !seen.insert(file) {
      continue;
    }

    let parsed = db.parse(file);
    let mut edges = Vec::new();

    for spec in collect_specifiers(&parsed.ast) {
      let target = db.module_resolve(file, spec.clone());
      if let Some(target) = target {
        if !seen.contains(&target) {
          queue.push_back(target);
        }
      }
      edges.push(ModuleEdge::new(spec, target));
    }

    edges.sort_by(|a, b| {
      let spec_ord = a.specifier.cmp(&b.specifier);
      if spec_ord == std::cmp::Ordering::Equal {
        a.target.cmp(&b.target)
      } else {
        spec_ord
      }
    });

    graph.edges.insert(file, edges);
  }

  graph
}

pub(crate) fn collect_specifiers(ast: &Node<TopLevel>) -> Vec<Arc<str>> {
  let mut specs = Vec::new();

  for stmt in &ast.stx.body {
    match stmt.stx.as_ref() {
      Stmt::Import(node) => specs.push(Arc::<str>::from(node.stx.module.clone())),
      Stmt::ExportList(node) => {
        if let Some(from) = &node.stx.from {
          specs.push(Arc::<str>::from(from.clone()));
        }
      }
      Stmt::ImportTypeDecl(node) => specs.push(Arc::<str>::from(node.stx.module.clone())),
      Stmt::ExportTypeDecl(node) => {
        if let Some(from) = &node.stx.module {
          specs.push(Arc::<str>::from(from.clone()));
        }
      }
      Stmt::ImportEqualsDecl(node) => specs.push(Arc::<str>::from(node.stx.module.clone())),
      Stmt::ModuleDecl(node) => match &node.stx.name {
        ModuleName::String(value) => specs.push(Arc::<str>::from(value.clone())),
        ModuleName::Identifier(_) => {}
      },
      _ => {}
    }
  }

  specs
}

/// Concrete salsa database.
#[salsa::database(TypecheckStorage)]
pub struct Database {
  storage: salsa::Storage<Database>,
}

impl Database {
  /// Creates a new database backed by `host`.
  pub fn new() -> Self {
    Self {
      storage: salsa::Storage::default(),
    }
  }
}

impl Default for Database {
  fn default() -> Self {
    Database::new()
  }
}

impl salsa::Database for Database {}

impl salsa::ParallelDatabase for Database {
  fn snapshot(&self) -> salsa::Snapshot<Self> {
    salsa::Snapshot::new(Database {
      storage: self.storage.snapshot(),
    })
  }
}
