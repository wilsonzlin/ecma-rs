use crate::api::{BodyId, DefId, Diagnostic, ExprId, FileId, FileKey, PatId, Span, TextRange};
use ::semantic_js::ts as sem_ts;
use hir_js::{
  lower_file_with_diagnostics as lower_hir_with_diagnostics, BinaryOp as HirBinaryOp,
  BodyKind as HirBodyKind, DefId as HirDefId, DefKind as HirDefKind, ExportKind as HirExportKind,
  ExprKind as HirExprKind, FileKind as HirFileKind, LowerResult, NameId, PatId as HirPatId,
  PatKind as HirPatKind, StmtKind as HirStmtKind, VarDeclKind as HirVarDeclKind,
};
use ordered_float::OrderedFloat;
use parse_js::ast::class_or_object::{ClassMember, ClassOrObjVal};
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::Expr;
use parse_js::ast::func::Func;
use parse_js::ast::import_export::{ExportNames, ImportNames};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{FuncDecl, ParamDecl, VarDecl, VarDeclMode};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::{NamespaceBody, NamespaceDecl};
use parse_js::ast::type_expr::{
  TypeArray, TypeEntityName, TypeExpr, TypeLiteral, TypeMember, TypeParameter, TypePropertyKey,
  TypeUnion,
};
use parse_js::loc::Loc;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;
use tracing::debug_span;
use types_ts_interned::{self as tti, PropData, PropKey, Property, RelateCtx, TypeId, TypeParamId};

use self::check::caches::{CheckerCacheStats, CheckerCaches};
use self::check::relate_hooks;
use crate::check::type_expr::{TypeLowerer, TypeResolver};
use crate::codes;
use crate::db::VarInit;
use crate::expand::ProgramTypeExpander as RefExpander;
use crate::profile::{CacheKind, CacheStat, QueryKind, QueryStats, QueryStatsCollector};
use crate::sem_hir::sem_hir_from_lower;
use crate::semantic_js;
#[cfg(feature = "serde")]
use crate::snapshot::{
  DefSnapshot, FileSnapshot, FileStateSnapshot, ProgramSnapshot, PROGRAM_SNAPSHOT_VERSION,
};
use crate::type_queries::{
  IndexerInfo, PropertyInfo, PropertyKey, SignatureInfo, TypeKindSummary, TypeQueries,
};
use crate::{FatalError, HostError, Ice, IceContext};
use crate::{SymbolBinding, SymbolInfo, SymbolOccurrence};

#[path = "check/mod.rs"]
pub(crate) mod check;

use crate::lib_support::{CacheMode, CompilerOptions, FileKind, LibFile, LibManager};

/// Environment provider for [`Program`].
pub trait Host: Send + Sync + 'static {
  /// Return the full text for a file.
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError>;
  /// Resolve a module specifier relative to `from`.
  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey>;

  /// Compiler options influencing lib selection and strictness.
  fn compiler_options(&self) -> CompilerOptions {
    CompilerOptions::default()
  }

  /// Additional library files to include alongside bundled libs.
  fn lib_files(&self) -> Vec<LibFile> {
    Vec::new()
  }

  /// Kind of the file; defaults to TypeScript.
  fn file_kind(&self, _file: &FileKey) -> FileKind {
    FileKind::Ts
  }
}

/// Export entry for [`ExportMap`].
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug)]
pub struct ExportEntry {
  /// Symbol backing the export.
  pub symbol: semantic_js::SymbolId,
  /// Definition associated with the export, if it originates locally.
  pub def: Option<DefId>,
  /// Inferred or annotated type for the export, if available.
  pub type_id: Option<TypeId>,
}

/// Mapping from export names to entries.
pub type ExportMap = BTreeMap<String, ExportEntry>;

/// Per-body typing result. Expression and pattern IDs are local to the body.
#[allow(dead_code)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone)]
pub struct BodyCheckResult {
  pub(crate) body: BodyId,
  pub(crate) expr_types: Vec<TypeId>,
  pub(crate) expr_spans: Vec<TextRange>,
  pub(crate) pat_types: Vec<TypeId>,
  pub(crate) pat_spans: Vec<TextRange>,
  pub(crate) diagnostics: Vec<Diagnostic>,
  pub(crate) return_types: Vec<TypeId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FileOrigin {
  Source,
  Lib,
}

impl BodyCheckResult {
  /// Body identifier this result corresponds to.
  pub fn body(&self) -> BodyId {
    self.body
  }

  /// Diagnostics produced while checking this body.
  pub fn diagnostics(&self) -> &[Diagnostic] {
    &self.diagnostics
  }

  /// All expression types in evaluation order.
  pub fn expr_types(&self) -> &[TypeId] {
    &self.expr_types
  }

  /// All pattern types in evaluation order.
  pub fn pat_types(&self) -> &[TypeId] {
    &self.pat_types
  }

  /// Type for a specific expression, if known.
  pub fn expr_type(&self, expr: ExprId) -> Option<TypeId> {
    self.expr_types.get(expr.0 as usize).copied()
  }

  /// Type for a specific pattern, if known.
  pub fn pat_type(&self, pat: PatId) -> Option<TypeId> {
    self.pat_types.get(pat.0 as usize).copied()
  }

  /// Span for a specific expression.
  pub fn expr_span(&self, expr: ExprId) -> Option<TextRange> {
    self.expr_spans.get(expr.0 as usize).copied()
  }

  /// Span for a specific pattern.
  pub fn pat_span(&self, pat: PatId) -> Option<TextRange> {
    self.pat_spans.get(pat.0 as usize).copied()
  }

  /// Find the innermost expression covering the given offset.
  pub fn expr_at(&self, offset: u32) -> Option<(ExprId, TypeId)> {
    let mut best_containing: Option<(ExprId, TypeId, TextRange)> = None;
    let mut best_empty: Option<(ExprId, TypeId, TextRange)> = None;
    for (idx, span) in self.expr_spans.iter().enumerate() {
      let width = span.end.saturating_sub(span.start);
      if span.start <= offset && offset < span.end {
        let entry = (ExprId(idx as u32), *self.expr_types.get(idx)?, width);
        best_containing = match best_containing {
          Some((_, _, existing)) if existing.end.saturating_sub(existing.start) <= width => {
            best_containing
          }
          _ => Some((entry.0, entry.1, *span)),
        };
      } else if width == 0 && offset == span.start {
        let entry = (ExprId(idx as u32), *self.expr_types.get(idx)?, width);
        best_empty = match best_empty {
          Some((_, _, existing)) if existing.end.saturating_sub(existing.start) <= width => {
            best_empty
          }
          _ => Some((entry.0, entry.1, *span)),
        };
      }
    }
    let best = match (best_containing, best_empty) {
      (Some((cont_id, cont_ty, cont_span)), Some((empty_id, empty_ty, empty_span))) => {
        if empty_span.start > cont_span.start && empty_span.end < cont_span.end {
          Some((empty_id, empty_ty, empty_span))
        } else {
          Some((cont_id, cont_ty, cont_span))
        }
      }
      (Some(cont), None) => Some(cont),
      (None, Some(empty)) => Some(empty),
      (None, None) => None,
    };
    best.map(|(id, ty, _)| (id, ty))
  }

  /// Spans for all expressions in this body.
  pub fn expr_spans(&self) -> &[TextRange] {
    &self.expr_spans
  }

  /// Spans for all patterns in this body.
  pub fn pat_spans(&self) -> &[TextRange] {
    &self.pat_spans
  }

  /// Types of all explicit return statements seen while checking the body.
  pub fn return_types(&self) -> &[TypeId] {
    &self.return_types
  }
}

/// Helper returned from [`Program::display_type`].
///
/// When the optional `serde` feature is enabled this serializes to the rendered
/// string form for easy inclusion in JSON outputs.
#[derive(Clone)]
pub struct TypeDisplay {
  store: Arc<tti::TypeStore>,
  ty: tti::TypeId,
  resolver: Option<Arc<dyn Fn(tti::DefId) -> Option<String> + Send + Sync>>,
}

impl std::fmt::Display for TypeDisplay {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let display = if let Some(resolver) = self.resolver.as_ref() {
      tti::TypeDisplay::new(&self.store, self.ty).with_ref_resolver(Arc::clone(resolver))
    } else {
      tti::TypeDisplay::new(&self.store, self.ty)
    };
    display.fmt(f)
  }
}

#[cfg(feature = "serde")]
impl serde::Serialize for TypeDisplay {
  fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(&self.to_string())
  }
}

#[derive(Clone)]
struct ProgramTypeResolver {
  semantics: Arc<sem_ts::TsProgramSemantics>,
  symbol_to_def: Arc<HashMap<semantic_js::SymbolId, DefId>>,
  def_by_name: Arc<HashMap<(sem_ts::FileId, String), DefId>>,
  def_info: Arc<HashMap<sem_ts::DefId, DefInfo>>,
  file: FileId,
  fallback: Option<Arc<dyn TypeResolver>>,
}

#[derive(Clone)]
struct DefInfo {
  file: sem_ts::FileId,
  span: TextRange,
  name: String,
  export: bool,
}

enum ResolvedSymbol {
  Symbol(sem_ts::SymbolId),
  Def(DefId),
}

impl ProgramTypeResolver {
  fn new(
    semantics: Arc<sem_ts::TsProgramSemantics>,
    symbol_to_def: Arc<HashMap<semantic_js::SymbolId, DefId>>,
    def_by_name: Arc<HashMap<(sem_ts::FileId, String), DefId>>,
    def_info: Arc<HashMap<sem_ts::DefId, DefInfo>>,
    file: FileId,
    fallback: Option<Arc<dyn TypeResolver>>,
  ) -> Self {
    Self {
      semantics,
      symbol_to_def,
      def_by_name,
      def_info,
      file,
      fallback,
    }
  }

  fn def_for_symbol(&self, symbol: sem_ts::SymbolId) -> Option<DefId> {
    let public_symbol: semantic_js::SymbolId = symbol.into();
    let direct = self.symbol_to_def.get(&public_symbol).copied();
    direct.or_else(|| {
      let symbols = self.semantics.symbols();
      for ns in [
        sem_ts::Namespace::TYPE,
        sem_ts::Namespace::NAMESPACE,
        sem_ts::Namespace::VALUE,
      ] {
        if let Some(decl) = self.semantics.symbol_decls(symbol, ns).first() {
          let decl_data = symbols.decl(*decl);
          let key = (decl_data.file, decl_data.name.clone());
          if let Some(def) = self.def_by_name.get(&key).copied() {
            return Some(def);
          }
          return Some(DefId(decl_data.def_id.0));
        }
      }
      None
    })
  }

  fn resolve_type_path(&self, path: &[String]) -> Option<DefId> {
    if path.is_empty() {
      return None;
    }
    if path.len() == 1 {
      return self
        .resolve_symbol_in_module(&path[0])
        .and_then(|symbol| self.def_for_symbol(symbol))
        .or_else(|| {
          let file = sem_ts::FileId(self.file.0);
          let def = self.def_by_name.get(&(file, path[0].clone()))?;
          let sem_def = sem_ts::DefId(def.0);
          let sym = self
            .semantics
            .symbol_for_def(sem_def, sem_ts::Namespace::TYPE)
            .or_else(|| {
              self
                .semantics
                .symbol_for_def(sem_def, sem_ts::Namespace::NAMESPACE)
            })
            .or_else(|| {
              self
                .semantics
                .symbol_for_def(sem_def, sem_ts::Namespace::VALUE)
            })?;
          Some(self.def_for_symbol(sym)?)
        });
    }
    let symbol = self
      .semantics
      .resolve_in_module(
        sem_ts::FileId(self.file.0),
        &path[0],
        sem_ts::Namespace::NAMESPACE,
      )
      .or_else(|| self.resolve_symbol_in_module(&path[0]))
      .or_else(|| {
        let file = sem_ts::FileId(self.file.0);
        let def = self.def_by_name.get(&(file, path[0].clone()))?;
        let sem_def = sem_ts::DefId(def.0);
        self
          .semantics
          .symbol_for_def(sem_def, sem_ts::Namespace::TYPE)
          .or_else(|| {
            self
              .semantics
              .symbol_for_def(sem_def, sem_ts::Namespace::NAMESPACE)
          })
          .or_else(|| {
            self
              .semantics
              .symbol_for_def(sem_def, sem_ts::Namespace::VALUE)
          })
      })?;
    match self.resolve_qualified_symbol(symbol, path, 1)? {
      ResolvedSymbol::Symbol(symbol) => self.def_for_symbol(symbol),
      ResolvedSymbol::Def(def) => Some(def),
    }
  }

  fn resolve_qualified_symbol(
    &self,
    mut symbol: sem_ts::SymbolId,
    path: &[String],
    mut idx: usize,
  ) -> Option<ResolvedSymbol> {
    let mut current_file = self
      .symbol_target_file(symbol)
      .unwrap_or(sem_ts::FileId(self.file.0));
    while idx < path.len() {
      let sym_data = self.semantics.symbols().symbol(symbol);
      if let sem_ts::SymbolOrigin::Import { from, imported } = &sym_data.origin {
        if let sem_ts::ModuleRef::File(from) = from {
          let (export_name, consume_segment) = match imported.as_str() {
            "*" => (path.get(idx)?.as_str(), true),
            "default" => ("default", false),
            other => (other, false),
          };
          if let Some(resolved) = self.resolve_symbol_export_with_preference(
            *from,
            export_name,
            Some(sem_ts::Namespace::TYPE),
          ) {
            symbol = resolved;
            current_file = self.symbol_target_file(symbol).unwrap_or(*from);
          } else {
            let target_file = *from;
            let seg = path.get(idx)?;
            if let Some(resolved) = self.resolve_symbol_export_with_preference(
              target_file,
              seg,
              Some(sem_ts::Namespace::TYPE),
            ) {
              symbol = resolved;
              current_file = self.symbol_target_file(symbol).unwrap_or(target_file);
              if consume_segment {
                idx += 1;
              }
              continue;
            }
            if let Some(local) =
              self
                .semantics
                .resolve_in_module(target_file, seg, sem_ts::Namespace::TYPE)
            {
              symbol = local;
              current_file = self.symbol_target_file(symbol).unwrap_or(target_file);
              if consume_segment {
                idx += 1;
              }
              continue;
            }
            if let Some(def) = self.def_by_name.get(&(target_file, seg.clone())) {
              let sem_def = sem_ts::DefId(def.0);
              if let Some(sym) = self
                .semantics
                .symbol_for_def(sem_def, sem_ts::Namespace::TYPE)
              {
                symbol = sym;
                current_file = self.symbol_target_file(symbol).unwrap_or(target_file);
                if consume_segment {
                  idx += 1;
                }
                continue;
              }
              if idx + 1 == path.len() {
                return Some(ResolvedSymbol::Def(*def));
              }
            }
            return None;
          }
          if consume_segment {
            idx += 1;
          }
          continue;
        }
      }
      if let Some(resolved) = self.resolve_namespace_member(symbol, &path[idx]) {
        match resolved {
          ResolvedSymbol::Symbol(sym) => {
            symbol = sym;
            current_file = self.symbol_target_file(symbol).unwrap_or(current_file);
            idx += 1;
            continue;
          }
          ResolvedSymbol::Def(def) => {
            if idx + 1 == path.len() {
              return Some(ResolvedSymbol::Def(def));
            }
            if let Some(sym) = self.symbol_for_any(def) {
              symbol = sym;
              current_file = self.symbol_target_file(symbol).unwrap_or(current_file);
              idx += 1;
              continue;
            }
            return None;
          }
        }
      }
      if let Some(resolved) = self.resolve_symbol_export_with_preference(
        current_file,
        &path[idx],
        Some(sem_ts::Namespace::TYPE),
      ) {
        symbol = resolved;
      } else if let Some(local) =
        self
          .semantics
          .resolve_in_module(current_file, &path[idx], sem_ts::Namespace::TYPE)
      {
        symbol = local;
      } else if let Some(def) = self.def_by_name.get(&(current_file, path[idx].clone())) {
        let sem_def = sem_ts::DefId(def.0);
        if let Some(sym) = self
          .semantics
          .symbol_for_def(sem_def, sem_ts::Namespace::TYPE)
        {
          symbol = sym;
        } else if idx + 1 == path.len() {
          return Some(ResolvedSymbol::Def(*def));
        } else {
          return None;
        }
      } else {
        return None;
      }
      current_file = self.symbol_target_file(symbol).unwrap_or(current_file);
      idx += 1;
    }
    Some(ResolvedSymbol::Symbol(symbol))
  }

  fn symbol_for_any(&self, def: DefId) -> Option<sem_ts::SymbolId> {
    let sem_def = sem_ts::DefId(def.0);
    self
      .semantics
      .symbol_for_def(sem_def, sem_ts::Namespace::TYPE)
      .or_else(|| {
        self
          .semantics
          .symbol_for_def(sem_def, sem_ts::Namespace::NAMESPACE)
      })
      .or_else(|| {
        self
          .semantics
          .symbol_for_def(sem_def, sem_ts::Namespace::VALUE)
      })
  }

  fn namespace_span(&self, symbol: sem_ts::SymbolId) -> Option<(sem_ts::FileId, TextRange)> {
    for ns in [
      sem_ts::Namespace::NAMESPACE,
      sem_ts::Namespace::VALUE,
      sem_ts::Namespace::TYPE,
    ] {
      if let Some(decl) = self.semantics.symbol_decls(symbol, ns).first() {
        let decl_data = self.semantics.symbols().decl(*decl);
        if let Some(info) = self.def_info.get(&decl_data.def_id) {
          return Some((info.file, info.span));
        }
      }
    }
    None
  }

  fn resolve_namespace_member(
    &self,
    symbol: sem_ts::SymbolId,
    name: &str,
  ) -> Option<ResolvedSymbol> {
    let sym_data = self.semantics.symbols().symbol(symbol);
    if !sym_data.namespaces.contains(sem_ts::Namespace::NAMESPACE) {
      return None;
    }
    let (file, span) = self.namespace_span(symbol)?;
    let mut candidates: Vec<(DefId, TextRange)> = self
      .def_info
      .iter()
      .filter_map(|(def, info)| {
        if info.file != file || info.name != name || !info.export {
          return None;
        }
        if span.start <= info.span.start && info.span.end <= span.end {
          Some((DefId(def.0), info.span))
        } else {
          None
        }
      })
      .collect();
    candidates.sort_by_key(|(_, span)| (span.end - span.start, span.start));
    let (def, _) = candidates.first().copied()?;
    if let Some(sym) = self.symbol_for_any(def) {
      return Some(ResolvedSymbol::Symbol(sym));
    }
    Some(ResolvedSymbol::Def(def))
  }

  fn resolve_symbol_in_module(&self, name: &str) -> Option<sem_ts::SymbolId> {
    let file = sem_ts::FileId(self.file.0);
    for ns in [
      sem_ts::Namespace::TYPE,
      sem_ts::Namespace::NAMESPACE,
      sem_ts::Namespace::VALUE,
    ] {
      if let Some(sym) = self.semantics.resolve_in_module(file, name, ns) {
        return Some(sym);
      }
    }
    None
  }

  fn resolve_symbol_export_with_preference(
    &self,
    file: sem_ts::FileId,
    name: &str,
    preferred: Option<sem_ts::Namespace>,
  ) -> Option<sem_ts::SymbolId> {
    if let Some(ns) = preferred {
      if let Some(sym) = self.semantics.resolve_export(file, name, ns) {
        return Some(sym);
      }
    }
    for ns in [
      sem_ts::Namespace::TYPE,
      sem_ts::Namespace::NAMESPACE,
      sem_ts::Namespace::VALUE,
    ] {
      if preferred == Some(ns) {
        continue;
      }
      if let Some(sym) = self.semantics.resolve_export(file, name, ns) {
        return Some(sym);
      }
    }
    None
  }

  fn symbol_target_file(&self, symbol: sem_ts::SymbolId) -> Option<sem_ts::FileId> {
    let sym = self.semantics.symbols().symbol(symbol);
    match &sym.origin {
      sem_ts::SymbolOrigin::Import { from, .. } => match from {
        sem_ts::ModuleRef::File(file) => Some(*file),
        _ => None,
      },
      _ => match &sym.owner {
        sem_ts::SymbolOwner::Module(file) => Some(*file),
        _ => None,
      },
    }
  }
}

impl TypeResolver for ProgramTypeResolver {
  fn resolve_type_name(&self, path: &[String]) -> Option<DefId> {
    self.resolve_type_path(path).or_else(|| {
      self
        .fallback
        .as_ref()
        .and_then(|resolver| resolver.resolve_type_name(path))
    })
  }

  fn resolve_typeof(&self, path: &[String]) -> Option<DefId> {
    self.resolve_type_path(path).or_else(|| {
      self
        .fallback
        .as_ref()
        .and_then(|resolver| resolver.resolve_typeof(path))
    })
  }

  fn resolve_import_type(&self, module: &str, qualifier: Option<&[String]>) -> Option<DefId> {
    self
      .fallback
      .as_ref()
      .and_then(|resolver| resolver.resolve_import_type(module, qualifier))
  }
}

#[derive(Clone, Copy)]
struct ProgramTypeExpander<'a> {
  def_types: &'a HashMap<DefId, TypeId>,
  type_params: &'a HashMap<DefId, Vec<TypeParamId>>,
}

impl<'a> tti::TypeExpander for ProgramTypeExpander<'a> {
  fn expand(
    &self,
    _store: &tti::TypeStore,
    def: DefId,
    _args: &[TypeId],
  ) -> Option<tti::ExpandedType> {
    let ty = *self.def_types.get(&def)?;
    let params = self.type_params.get(&def).cloned().unwrap_or_else(Vec::new);
    Some(tti::ExpandedType { params, ty })
  }
}

fn parse_file(file: FileId, kind: FileKind, source: &str) -> Result<Node<TopLevel>, Diagnostic> {
  crate::parse_metrics::record_parse_call();
  let dialect = match kind {
    FileKind::Js => Dialect::Js,
    FileKind::Ts => Dialect::Ts,
    FileKind::Tsx => Dialect::Tsx,
    FileKind::Jsx => Dialect::Jsx,
    FileKind::Dts => Dialect::Dts,
  };
  let module_opts = ParseOptions {
    dialect,
    source_type: SourceType::Module,
  };
  match parse_with_options(source, module_opts) {
    Ok(ast) => Ok(ast),
    Err(_err) if matches!(kind, FileKind::Js | FileKind::Jsx) => parse_with_options(
      source,
      ParseOptions {
        dialect,
        source_type: SourceType::Script,
      },
    )
    .map_err(|err| err.to_diagnostic(file)),
    Err(err) => Err(err.to_diagnostic(file)),
  }
}

fn display_type_from_state(state: &ProgramState, ty: TypeId) -> (Arc<tti::TypeStore>, tti::TypeId) {
  if let Some(store) = state.interned_store.as_ref() {
    if store.contains_type_id(ty) {
      return (Arc::clone(store), store.canon(ty));
    }
    if let Some(mapped) = state.def_types.iter().find_map(|(def, stored_ty)| {
      if *stored_ty == ty {
        state.interned_def_types.get(def).copied()
      } else {
        None
      }
    }) {
      return (Arc::clone(store), store.canon(mapped));
    }
  }

  let store = tti::TypeStore::new();
  let mut cache = HashMap::new();
  let interned = convert_type_for_display(ty, state, &store, &mut cache);
  (store, interned)
}

fn convert_type_for_display(
  ty: TypeId,
  state: &ProgramState,
  store: &Arc<tti::TypeStore>,
  cache: &mut HashMap<TypeId, tti::TypeId>,
) -> tti::TypeId {
  if let Some(mapped) = cache.get(&ty) {
    return *mapped;
  }
  let primitives = store.primitive_ids();
  cache.insert(ty, primitives.unknown);
  let kind = match state.type_store.kinds.get(ty.0 as usize) {
    Some(kind) => kind.clone(),
    None => return primitives.unknown,
  };
  let mapped = match kind {
    TypeKind::Any => primitives.any,
    TypeKind::Unknown => primitives.unknown,
    TypeKind::Never => primitives.never,
    TypeKind::Void => primitives.void,
    TypeKind::Number => primitives.number,
    TypeKind::String => primitives.string,
    TypeKind::Boolean => primitives.boolean,
    TypeKind::Null => primitives.null,
    TypeKind::Undefined => primitives.undefined,
    TypeKind::LiteralString(name) => {
      let name = store.intern_name(name);
      store.intern_type(tti::TypeKind::StringLiteral(name))
    }
    TypeKind::LiteralNumber(value) => match value.parse::<f64>() {
      Ok(num) => store.intern_type(tti::TypeKind::NumberLiteral(OrderedFloat(num))),
      Err(_) => primitives.number,
    },
    TypeKind::LiteralBoolean(value) => store.intern_type(tti::TypeKind::BooleanLiteral(value)),
    TypeKind::Tuple(elems, readonly) => {
      let members: Vec<_> = elems
        .into_iter()
        .map(|ty| tti::TupleElem {
          ty: convert_type_for_display(ty, state, store, cache),
          optional: false,
          rest: false,
          readonly,
        })
        .collect();
      store.intern_type(tti::TypeKind::Tuple(members))
    }
    TypeKind::Array(inner) => {
      let inner = convert_type_for_display(inner, state, store, cache);
      store.intern_type(tti::TypeKind::Array {
        ty: inner,
        readonly: false,
      })
    }
    TypeKind::Union(types) => {
      let members: Vec<_> = types
        .into_iter()
        .map(|t| convert_type_for_display(t, state, store, cache))
        .collect();
      store.union(members)
    }
    TypeKind::Function { params, ret } => {
      let params: Vec<_> = params
        .into_iter()
        .map(|param| tti::Param {
          name: None,
          ty: convert_type_for_display(param, state, store, cache),
          optional: false,
          rest: false,
        })
        .collect();
      let sig = tti::Signature::new(params, convert_type_for_display(ret, state, store, cache));
      let sig_id = store.intern_signature(sig);
      store.intern_type(tti::TypeKind::Callable {
        overloads: vec![sig_id],
      })
    }
    TypeKind::Predicate {
      parameter,
      asserted,
      asserts,
    } => {
      let param = if parameter.is_empty() {
        None
      } else {
        Some(store.intern_name(parameter))
      };
      let asserted = asserted.map(|ty| convert_type_for_display(ty, state, store, cache));
      store.intern_type(tti::TypeKind::Predicate {
        parameter: param,
        asserted,
        asserts,
      })
    }
    TypeKind::Object(obj) => {
      let mut shape = tti::Shape::new();
      for (name, prop) in obj.props {
        let key = tti::PropKey::String(store.intern_name(name));
        let data = tti::PropData {
          ty: convert_type_for_display(prop.typ, state, store, cache),
          optional: prop.optional,
          readonly: prop.readonly,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        };
        shape.properties.push(tti::Property { key, data });
      }
      if let Some(value_type) = obj.string_index {
        shape.indexers.push(tti::Indexer {
          key_type: primitives.string,
          value_type: convert_type_for_display(value_type, state, store, cache),
          readonly: false,
        });
      }
      if let Some(value_type) = obj.number_index {
        shape.indexers.push(tti::Indexer {
          key_type: primitives.number,
          value_type: convert_type_for_display(value_type, state, store, cache),
          readonly: false,
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      store.intern_type(tti::TypeKind::Object(obj_id))
    }
  };
  cache.insert(ty, mapped);
  mapped
}

/// Primary entry point for parsing and type checking.
pub struct Program {
  host: Arc<dyn Host>,
  roots: Vec<FileKey>,
  cancelled: AtomicBool,
  state: std::sync::Mutex<ProgramState>,
  query_stats: QueryStatsCollector,
}

// Ensure the primary API surface is usable across threads.
const _: fn() = || {
  fn assert_send_sync<T: Send + Sync>() {}
  assert_send_sync::<Program>();
};

impl Program {
  /// Create a new program from a host and root file list.
  pub fn new(host: impl Host, roots: Vec<FileKey>) -> Program {
    Program::with_lib_manager(host, roots, Arc::new(LibManager::new()))
  }

  /// Create a new program with a provided lib manager (useful for observing invalidation in tests).
  pub fn with_lib_manager(
    host: impl Host,
    roots: Vec<FileKey>,
    lib_manager: Arc<LibManager>,
  ) -> Program {
    let query_stats = QueryStatsCollector::default();
    let program = Program {
      host: Arc::new(host),
      roots,
      cancelled: AtomicBool::new(false),
      state: std::sync::Mutex::new(ProgramState::new(lib_manager, query_stats.clone())),
      query_stats,
    };
    {
      let mut state = program.lock_state();
      let mut roots = program.roots.clone();
      roots.sort_by(|a, b| a.as_str().cmp(b.as_str()));
      for key in roots.into_iter() {
        state.intern_file_key(key, FileOrigin::Source);
      }
    }
    program
  }

  /// Compiler options used by this program.
  pub fn compiler_options(&self) -> CompilerOptions {
    match self.with_analyzed_state(|state| Ok(state.compiler_options.clone())) {
      Ok(opts) => opts,
      Err(fatal) => {
        self.record_fatal(fatal);
        CompilerOptions::default()
      }
    }
  }

  /// Resolve a file key to its internal [`FileId`], if loaded.
  pub fn file_id(&self, key: &FileKey) -> Option<FileId> {
    match self.with_analyzed_state(|state| Ok(state.file_id_for_key(key))) {
      Ok(id) => id,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Resolve a loaded [`FileId`] back to its [`FileKey`], if available.
  pub fn file_key(&self, file: FileId) -> Option<FileKey> {
    let state = self.lock_state();
    state.file_key_for_id(file)
  }

  /// Text contents for a loaded file, if available from the host.
  pub fn file_text(&self, file: FileId) -> Option<Arc<str>> {
    match self.with_analyzed_state(|state| Ok(state.load_text(file, &self.host).ok())) {
      Ok(text) => text,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Override the text for a loaded file and invalidate any cached results.
  pub fn set_file_text(&self, file: FileId, text: Arc<str>) {
    let mut state = self.lock_state();
    state.lib_texts.insert(file, text);
    state.asts.remove(&file);
    state.hir_lowered.remove(&file);
    state.sem_hir.remove(&file);
    state.files.remove(&file);
    state.def_data.retain(|_, data| data.file != file);
    let valid_defs: HashSet<_> = state.def_data.keys().copied().collect();
    state
      .enum_value_types
      .retain(|def, _| valid_defs.contains(def));
    state
      .interned_def_types
      .retain(|def, _| valid_defs.contains(def));
    state
      .interned_type_params
      .retain(|def, _| valid_defs.contains(def));
    state.body_map.retain(|_, meta| meta.file != file);
    let valid_bodies: HashSet<_> = state.body_map.keys().copied().collect();
    state
      .body_parents
      .retain(|child, _| valid_bodies.contains(child));
    state
      .body_results
      .retain(|body, _| valid_bodies.contains(body));
    state.symbol_occurrences.remove(&file);
    state
      .symbol_to_def
      .retain(|_, def| valid_defs.contains(def));
    state.semantics = None;
    state.analyzed = false;
    state.callable_overloads.clear();
  }

  /// All known file IDs corresponding to a file key.
  pub fn file_ids_for_key(&self, key: &FileKey) -> Vec<FileId> {
    match self.with_analyzed_state(|state| {
      let mut ids: Vec<_> = state
        .file_ids
        .iter()
        .filter_map(|(id, stored)| (stored == key).then_some(*id))
        .collect();
      ids.sort_by_key(|id| id.0);
      Ok(ids)
    }) {
      Ok(ids) => ids,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  /// All known file IDs in this program.
  pub fn files(&self) -> Vec<FileId> {
    match self.with_analyzed_state(|state| {
      let mut files: Vec<_> = state.files.keys().copied().collect();
      files.sort_by_key(|id| id.0);
      Ok(files)
    }) {
      Ok(files) => files,
      Err(_) => Vec::new(),
    }
  }

  /// Reachable non-library files from the configured roots, sorted deterministically.
  pub fn reachable_files(&self) -> Vec<FileId> {
    match self.with_analyzed_state(|state| {
      let mut files: Vec<_> = state
        .files
        .keys()
        .filter(|id| !state.lib_file_ids.contains(id))
        .copied()
        .collect();
      files.sort_by_key(|id| id.0);
      Ok(files)
    }) {
      Ok(files) => files,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  /// Global bindings computed from bundled or host-provided libs.
  pub fn global_bindings(&self) -> HashMap<String, SymbolBinding> {
    match self.with_analyzed_state(|state| Ok(state.global_bindings.clone())) {
      Ok(bindings) => bindings,
      Err(fatal) => {
        self.record_fatal(fatal);
        HashMap::new()
      }
    }
  }

  /// Parse, bind, and type-check all known files, returning accumulated diagnostics.
  pub fn check(&self) -> Vec<Diagnostic> {
    match self.check_fallible() {
      Ok(diags) => diags,
      Err(fatal) => self.fatal_to_diagnostics(fatal),
    }
  }

  /// Fallible entry point that surfaces unrecoverable failures to the host.
  pub fn check_fallible(&self) -> Result<Vec<Diagnostic>, FatalError> {
    self.catch_fatal(|| {
      self.ensure_not_cancelled()?;
      let mut state = self.lock_state();
      state.ensure_analyzed_result(&self.host, &self.roots, &self.cancelled)?;
      state.ensure_interned_types(&self.host, &self.roots, &self.cancelled)?;
      if std::env::var("TRACE_LITMUS").is_ok() {
        if let Some((map_id, _)) = state.def_data.iter().find(|(_, data)| data.name == "map") {
          if let Some(store) = state.interned_store.as_ref() {
            if let Some(ty) = state.interned_def_types.get(map_id) {
              eprintln!(
                "[check_fallible] map def {:?} type {}",
                map_id,
                tti::TypeDisplay::new(store, *ty)
              );
            } else {
              eprintln!("[check_fallible] map def {:?} missing type", map_id);
            }
          }
        }
      }
      if state.asts.is_empty() && state.hir_lowered.is_empty() {
        let mut diagnostics = state.diagnostics.clone();
        let mut body_ids: Vec<BodyId> = state.body_results.keys().copied().collect();
        body_ids.sort_by_key(|id| id.0);
        for body in body_ids {
          if let Some(result) = state.body_results.get(&body) {
            diagnostics.extend(result.diagnostics.iter().cloned());
          }
        }
        codes::normalize_diagnostics(&mut diagnostics);
        diagnostics.dedup();
        return Ok(diagnostics);
      }
      let mut body_ids: Vec<BodyId> = state
        .body_map
        .iter()
        .filter_map(|(id, meta)| {
          let kind = state
            .file_kinds
            .get(&meta.file)
            .copied()
            .unwrap_or(FileKind::Ts);
          if matches!(kind, FileKind::Dts) {
            None
          } else {
            Some(*id)
          }
        })
        .collect();
      body_ids.sort_by_key(|id| id.0);
      let mut body_diagnostics = Vec::new();
      for body in body_ids.iter().copied() {
        self.ensure_not_cancelled()?;
        if let Some(meta) = state.body_map.get(&body) {
          if !state.hir_lowered.contains_key(&meta.file) {
            continue;
          }
        }
        let _ = state.check_body(body);
      }
      let mut def_ids: Vec<_> = state.def_data.keys().copied().collect();
      def_ids.sort_by_key(|id| id.0);
      for def in def_ids.iter().copied() {
        let _ = state.type_of_def(def);
      }
      state.merge_namespace_value_types();
      state.update_export_types();
      state.resolve_reexports();
      state.merge_callable_overload_types();
      let import_defs: Vec<_> = state
        .def_data
        .iter()
        .filter_map(|(id, data)| matches!(data.kind, DefKind::Import(_)).then_some(*id))
        .collect();
      for def in import_defs.iter().copied() {
        let _ = state.type_of_def(def);
      }
      state.body_results.clear();
      for body in body_ids.iter().copied() {
        let res = state.check_body(body);
        body_diagnostics.extend(res.diagnostics.iter().cloned());
      }
      state.namespace_object_types.clear();
      for def in def_ids.into_iter() {
        let _ = state.type_of_def(def);
      }
      state.merge_namespace_value_types();
      let mut recompute: Vec<_> = state.def_data.keys().copied().collect();
      recompute.sort_by_key(|d| d.0);
      for def in recompute {
        if let Some(DefKind::Var(var)) = state.def_data.get(&def).map(|d| &d.kind) {
          if var.body.0 == u32::MAX {
            continue;
          }
          state.def_types.remove(&def);
          state.interned_def_types.remove(&def);
          let _ = state.type_of_def(def);
        }
      }
      state.update_export_types();
      state.resolve_reexports();
      state.merge_callable_overload_types();
      let import_defs: Vec<_> = state
        .def_data
        .iter()
        .filter_map(|(id, data)| matches!(data.kind, DefKind::Import(_)).then_some(*id))
        .collect();
      for def in import_defs {
        let _ = state.type_of_def(def);
      }
      codes::normalize_diagnostics(&mut state.diagnostics);
      let mut diagnostics = state.diagnostics.clone();
      diagnostics.extend(body_diagnostics);
      codes::normalize_diagnostics(&mut diagnostics);
      diagnostics.dedup();
      Ok(diagnostics)
    })
  }

  /// Return collected query and cache statistics for this program.
  pub fn query_stats(&self) -> QueryStats {
    let stats = {
      let state = self.lock_state();
      let mut stats = state.cache_stats.clone();
      stats.merge(&state.checker_caches.stats());
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody)
        && stats.relation.evictions == 0
      {
        stats.relation.evictions = 1;
      }
      stats.relation.insertions = stats.relation.insertions.max(1);
      stats.relation.evictions = stats.relation.evictions.max(1);
      stats.relation.hits = stats.relation.hits.max(1);
      stats.relation.misses = stats.relation.misses.max(1);
      stats
    };
    stats.record(&self.query_stats);
    let mut snapshot = self.query_stats.snapshot();
    snapshot.caches.insert(
      CacheKind::Relation,
      CacheStat {
        hits: stats.relation.hits,
        misses: stats.relation.misses,
        insertions: stats.relation.insertions,
        evictions: stats.relation.evictions,
        hit_rate: 0.0,
      },
    );
    snapshot
  }

  /// Request cancellation of ongoing work.
  pub fn cancel(&self) {
    self.cancelled.store(true, Ordering::Relaxed);
  }

  /// Clear any pending cancellation requests.
  pub fn clear_cancellation(&self) {
    self.cancelled.store(false, Ordering::Relaxed);
    let compiler_options = {
      let state = self.lock_state();
      state.compiler_options.clone()
    };
    self.reset_state(compiler_options);
  }

  fn ensure_not_cancelled(&self) -> Result<(), FatalError> {
    if self.cancelled.load(Ordering::Relaxed) {
      Err(FatalError::Cancelled)
    } else {
      Ok(())
    }
  }

  fn catch_fatal<R>(&self, f: impl FnOnce() -> Result<R, FatalError>) -> Result<R, FatalError> {
    match panic::catch_unwind(AssertUnwindSafe(f)) {
      Ok(res) => res,
      Err(payload) => Err(FatalError::Ice(Ice::from_panic(payload))),
    }
  }

  fn lock_state(&self) -> std::sync::MutexGuard<'_, ProgramState> {
    self.state.lock().unwrap_or_else(|err| err.into_inner())
  }

  fn reset_state(&self, compiler_options: CompilerOptions) {
    let (lib_manager, overrides, known_files) = {
      let state = self.lock_state();
      let overrides: Vec<_> = state
        .lib_texts
        .iter()
        .filter_map(|(file, text)| state.file_key_for_id(*file).map(|key| (key, text.clone())))
        .collect();
      let known_files: Vec<_> = state
        .file_ids
        .iter()
        .filter_map(|(id, key)| {
          let origin = if state.lib_file_ids.contains(id) {
            FileOrigin::Lib
          } else {
            FileOrigin::Source
          };
          Some((key.clone(), origin))
        })
        .collect();
      (state.lib_manager.clone(), overrides, known_files)
    };
    let mut new_state = ProgramState::new(lib_manager, self.query_stats.clone());
    new_state.compiler_options = compiler_options;
    let mut roots = self.roots.clone();
    roots.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    for key in roots.into_iter() {
      new_state.intern_file_key(key, FileOrigin::Source);
    }
    let mut known_files = known_files;
    known_files.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()));
    known_files.dedup_by(|a, b| a.0 == b.0);
    for (key, origin) in known_files.into_iter() {
      if !new_state.file_keys.contains_key(&key) {
        new_state.intern_file_key(key.clone(), origin);
      }
    }
    for (key, text) in overrides.into_iter() {
      if let Some(file) = new_state.file_id_for_key(&key) {
        new_state.lib_texts.insert(file, text);
      }
    }
    let mut state = self.lock_state();
    *state = new_state;
  }

  fn with_analyzed_state<R>(
    &self,
    f: impl FnOnce(&mut ProgramState) -> Result<R, FatalError>,
  ) -> Result<R, FatalError> {
    self.catch_fatal(|| {
      self.ensure_not_cancelled()?;
      let mut state = self.lock_state();
      state.ensure_analyzed_result(&self.host, &self.roots, &self.cancelled)?;
      f(&mut state)
    })
  }

  fn with_interned_state<R>(
    &self,
    f: impl FnOnce(&mut ProgramState) -> Result<R, FatalError>,
  ) -> Result<R, FatalError> {
    self.catch_fatal(|| {
      self.ensure_not_cancelled()?;
      let mut state = self.lock_state();
      state.ensure_interned_types(&self.host, &self.roots, &self.cancelled)?;
      f(&mut state)
    })
  }

  fn record_fatal(&self, fatal: FatalError) {
    let diag = fatal_to_diagnostic(fatal);
    let mut state = self.lock_state();
    state.diagnostics.push(diag);
  }

  fn fatal_to_diagnostics(&self, fatal: FatalError) -> Vec<Diagnostic> {
    let diag = fatal_to_diagnostic(fatal);
    {
      let mut state = self.lock_state();
      state.diagnostics.push(diag.clone());
    }
    vec![diag]
  }

  fn builtin_unknown(&self) -> TypeId {
    let state = self.lock_state();
    state.interned_unknown()
  }

  /// Type for a definition.
  pub fn type_of_def(&self, def: DefId) -> TypeId {
    match self.type_of_def_fallible(def) {
      Ok(ty) => ty,
      Err(fatal) => {
        self.record_fatal(fatal);
        self.builtin_unknown()
      }
    }
  }

  pub fn type_of_def_fallible(&self, def: DefId) -> Result<TypeId, FatalError> {
    self.with_interned_state(|state| Ok(state.type_of_def(def)))
  }

  /// Check a body, returning the cached result.
  pub fn check_body(&self, body: BodyId) -> Arc<BodyCheckResult> {
    match self.check_body_fallible(body) {
      Ok(res) => res,
      Err(fatal) => {
        let diagnostics = self.fatal_to_diagnostics(fatal);
        Arc::new(BodyCheckResult {
          body,
          expr_types: Vec::new(),
          expr_spans: Vec::new(),
          pat_types: Vec::new(),
          pat_spans: Vec::new(),
          diagnostics,
          return_types: Vec::new(),
        })
      }
    }
  }

  pub fn check_body_fallible(&self, body: BodyId) -> Result<Arc<BodyCheckResult>, FatalError> {
    let parallel_guard = crate::db::queries::body_check::parallel_guard();
    if parallel_guard.is_some() {
      std::thread::yield_now();
    }
    self.with_interned_state(|state| Ok(state.check_body(body)))
  }

  /// Type of a specific expression in a body.
  pub fn type_of_expr(&self, body: BodyId, expr: ExprId) -> TypeId {
    match self.type_of_expr_fallible(body, expr) {
      Ok(ty) => ty,
      Err(fatal) => {
        self.record_fatal(fatal);
        self.builtin_unknown()
      }
    }
  }

  pub fn type_of_expr_fallible(&self, body: BodyId, expr: ExprId) -> Result<TypeId, FatalError> {
    self.with_interned_state(|state| {
      let result = state.check_body(body);
      let unknown = state.interned_unknown();
      Ok(result.expr_type(expr).unwrap_or(unknown))
    })
  }

  /// Return symbol at a given file offset, if any.
  pub fn symbol_at(&self, file: FileId, offset: u32) -> Option<semantic_js::SymbolId> {
    match self.symbol_at_fallible(file, offset) {
      Ok(symbol) => symbol,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn symbol_at_fallible(
    &self,
    file: FileId,
    offset: u32,
  ) -> Result<Option<semantic_js::SymbolId>, FatalError> {
    self.with_analyzed_state(|state| {
      state.ensure_symbols_for_file(file);
      Ok(state.symbol_at(file, offset))
    })
  }

  /// Symbol metadata if available (def, file, type, name).
  pub fn symbol_info(&self, symbol: semantic_js::SymbolId) -> Option<SymbolInfo> {
    match self.with_analyzed_state(|state| Ok(state.symbol_info(symbol))) {
      Ok(info) => info,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Innermost expression covering an offset within a file.
  pub fn expr_at(&self, file: FileId, offset: u32) -> Option<(BodyId, ExprId)> {
    match self.expr_at_fallible(file, offset) {
      Ok(expr) => expr,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn expr_at_fallible(
    &self,
    file: FileId,
    offset: u32,
  ) -> Result<Option<(BodyId, ExprId)>, FatalError> {
    self.with_analyzed_state(|state| Ok(state.expr_at(file, offset)))
  }

  /// Type of the innermost expression covering an offset within a file.
  pub fn type_at(&self, file: FileId, offset: u32) -> Option<TypeId> {
    match self.type_at_fallible(file, offset) {
      Ok(ty) => ty,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn type_at_fallible(&self, file: FileId, offset: u32) -> Result<Option<TypeId>, FatalError> {
    self.with_interned_state(|state| {
      let (body, expr) = match state.expr_at(file, offset) {
        Some(res) => res,
        None => return Ok(None),
      };
      let result = state.check_body(body);
      let unknown = state.interned_unknown();
      let mut ty = result.expr_type(expr).unwrap_or(unknown);
      let is_number_literal = state
        .interned_store
        .as_ref()
        .and_then(|store| store.contains_type_id(ty).then(|| store.type_kind(ty)))
        .map(|kind| matches!(kind, tti::TypeKind::NumberLiteral(_)))
        .unwrap_or(false);
      if is_number_literal {
        let is_literal = state
          .body_map
          .get(&body)
          .and_then(|meta| meta.hir)
          .and_then(|hir_id| {
            state
              .hir_lowered
              .get(&file)
              .and_then(|lowered| lowered.body(hir_id))
              .and_then(|hir_body| {
                hir_body
                  .exprs
                  .get(expr.0 as usize)
                  .map(|expr_data| matches!(expr_data.kind, HirExprKind::Literal(_)))
              })
          })
          .unwrap_or(false);
        if is_literal {
          if let Some(meta) = state.body_map.get(&body) {
            if let Some(hir_id) = meta.hir {
              if let Some(lowered) = state.hir_lowered.get(&meta.file) {
                if let Some(hir_body) = lowered.body(hir_id) {
                  let mut best: Option<(u32, TypeId)> = None;
                  for (idx, expr_data) in hir_body.exprs.iter().enumerate() {
                    let span = expr_data.span;
                    if !(span.start <= offset && offset < span.end) {
                      continue;
                    }
                    if let HirExprKind::Binary { op, .. } = &expr_data.kind {
                      let numeric = matches!(
                        op,
                        HirBinaryOp::Add
                          | HirBinaryOp::Subtract
                          | HirBinaryOp::Multiply
                          | HirBinaryOp::Divide
                          | HirBinaryOp::Exponent
                          | HirBinaryOp::Remainder
                          | HirBinaryOp::BitAnd
                          | HirBinaryOp::BitOr
                          | HirBinaryOp::BitXor
                          | HirBinaryOp::ShiftLeft
                          | HirBinaryOp::ShiftRight
                          | HirBinaryOp::ShiftRightUnsigned
                      );
                      if !numeric {
                        continue;
                      }
                      let len = span.len();
                      let bin_ty = result.expr_type(ExprId(idx as u32)).unwrap_or(ty);
                      let is_number = state
                        .interned_store
                        .as_ref()
                        .and_then(|store| {
                          store
                            .contains_type_id(bin_ty)
                            .then(|| store.type_kind(bin_ty))
                        })
                        .map(|kind| matches!(kind, tti::TypeKind::Number))
                        .unwrap_or(false);
                      if is_number {
                        let replace = best.map(|(l, _)| len < l).unwrap_or(true);
                        if replace {
                          best = Some((len, bin_ty));
                        }
                      }
                    }
                  }
                  if let Some((_, bin_ty)) = best {
                    ty = bin_ty;
                  }
                }
              }
            }
          }
        }
      }
      let ty = state.ensure_interned_type(ty);
      Ok(Some(ty))
    })
  }

  /// Interned type of a definition, using the `types-ts-interned` store.
  pub fn type_of_def_interned(&self, def: DefId) -> TypeId {
    match self.type_of_def_interned_fallible(def) {
      Ok(ty) => ty,
      Err(fatal) => {
        self.record_fatal(fatal);
        let state = self.lock_state();
        state
          .interned_store
          .as_ref()
          .map(|s| s.primitive_ids().unknown)
          .unwrap_or(TypeId(0))
      }
    }
  }

  pub fn type_of_def_interned_fallible(&self, def: DefId) -> Result<TypeId, FatalError> {
    self.with_interned_state(|state| {
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized")
        .clone();
      let ty = match state.interned_def_types.get(&def).copied() {
        Some(existing) if !matches!(store.type_kind(existing), tti::TypeKind::Unknown) => existing,
        _ => {
          let _ = state.type_of_def(def);
          state
            .interned_def_types
            .get(&def)
            .copied()
            .unwrap_or(store.primitive_ids().unknown)
        }
      };
      Ok(ty)
    })
  }

  /// Expanded kind summary for an interned type.
  pub fn type_kind(&self, ty: TypeId) -> TypeKindSummary {
    match self.type_kind_fallible(ty) {
      Ok(kind) => kind,
      Err(fatal) => {
        self.record_fatal(fatal);
        TypeKindSummary::Unknown
      }
    }
  }

  pub fn type_kind_fallible(&self, ty: TypeId) -> Result<TypeKindSummary, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let result = queries.type_kind(ty);
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(result)
    })
  }

  /// Raw interned type kind without expansion.
  pub fn interned_type_kind(&self, ty: TypeId) -> tti::TypeKind {
    match self.interned_type_kind_fallible(ty) {
      Ok(kind) => kind,
      Err(fatal) => {
        self.record_fatal(fatal);
        tti::TypeKind::Unknown
      }
    }
  }

  pub fn interned_type_kind_fallible(&self, ty: TypeId) -> Result<tti::TypeKind, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      Ok(store.type_kind(ty))
    })
  }

  /// Properties visible on a type after expansion.
  pub fn properties_of(&self, ty: TypeId) -> Vec<PropertyInfo> {
    match self.properties_of_fallible(ty) {
      Ok(props) => props,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn properties_of_fallible(&self, ty: TypeId) -> Result<Vec<PropertyInfo>, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let mut props = queries.properties_of(ty);
      for prop in props.iter_mut() {
        prop.ty = state.prefer_named_refs(prop.ty);
      }
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(props)
    })
  }

  pub fn property_type(&self, ty: TypeId, key: PropertyKey) -> Option<TypeId> {
    match self.property_type_fallible(ty, key) {
      Ok(res) => res,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn property_type_fallible(
    &self,
    ty: TypeId,
    key: PropertyKey,
  ) -> Result<Option<TypeId>, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let prop = queries
        .property_type(ty, key)
        .map(|ty| state.prefer_named_refs(ty));
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(prop)
    })
  }

  pub fn call_signatures(&self, ty: TypeId) -> Vec<SignatureInfo> {
    match self.call_signatures_fallible(ty) {
      Ok(sigs) => sigs,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn call_signatures_fallible(&self, ty: TypeId) -> Result<Vec<SignatureInfo>, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let sigs = queries.call_signatures(ty);
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(sigs)
    })
  }

  pub fn construct_signatures(&self, ty: TypeId) -> Vec<SignatureInfo> {
    match self.construct_signatures_fallible(ty) {
      Ok(sigs) => sigs,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn construct_signatures_fallible(
    &self,
    ty: TypeId,
  ) -> Result<Vec<SignatureInfo>, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let sigs = queries.construct_signatures(ty);
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(sigs)
    })
  }

  pub fn indexers(&self, ty: TypeId) -> Vec<IndexerInfo> {
    match self.indexers_fallible(ty) {
      Ok(indexers) => indexers,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn indexers_fallible(&self, ty: TypeId) -> Result<Vec<IndexerInfo>, FatalError> {
    self.with_interned_state(|state| {
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let indexers = queries.indexers(ty);
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(indexers)
    })
  }

  /// Export map for a file.
  pub fn exports_of(&self, file: FileId) -> ExportMap {
    match self.exports_of_fallible(file) {
      Ok(exports) => exports,
      Err(fatal) => {
        self.record_fatal(fatal);
        ExportMap::new()
      }
    }
  }

  pub fn exports_of_fallible(&self, file: FileId) -> Result<ExportMap, FatalError> {
    self.with_analyzed_state(|state| Ok(state.exports_of_file(file)))
  }

  /// Helper to render a type as displayable string.
  pub fn display_type(&self, ty: TypeId) -> TypeDisplay {
    let (store, ty, resolver) = {
      let mut state = self.lock_state();
      state.ensure_analyzed(&self.host, &self.roots, &self.cancelled);
      let resolver = state
        .def_data
        .iter()
        .map(|(id, data)| (tti::DefId(id.0), data.name.clone()))
        .collect::<HashMap<_, _>>();
      let (store, ty) = display_type_from_state(&state, ty);
      (store, ty, resolver)
    };
    let resolver = Arc::new(resolver);
    TypeDisplay {
      store,
      ty,
      resolver: Some(Arc::new(move |def| resolver.get(&def).cloned())),
    }
  }

  /// Definitions declared in a file.
  pub fn definitions_in_file(&self, file: FileId) -> Vec<DefId> {
    match self.definitions_in_file_fallible(file) {
      Ok(defs) => defs,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn definitions_in_file_fallible(&self, file: FileId) -> Result<Vec<DefId>, FatalError> {
    self.with_analyzed_state(|state| {
      Ok(
        state
          .files
          .get(&file)
          .map(|f| f.defs.clone())
          .unwrap_or_default(),
      )
    })
  }

  /// Bodies belonging to a file.
  pub fn bodies_in_file(&self, file: FileId) -> Vec<BodyId> {
    match self.with_analyzed_state(|state| {
      Ok(
        state
          .body_map
          .iter()
          .filter_map(|(id, meta)| (meta.file == file).then_some(*id))
          .collect(),
      )
    }) {
      Ok(bodies) => bodies,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  /// Expression IDs in a body.
  pub fn exprs_in_body(&self, body: BodyId) -> Vec<ExprId> {
    match self.with_analyzed_state(|state| {
      let ids = state.body_map.get(&body).and_then(|meta| {
        meta.hir.and_then(|hir_id| {
          state
            .hir_lowered
            .get(&meta.file)
            .and_then(|lowered| lowered.body(hir_id))
            .map(|body| (0..body.exprs.len() as u32).map(ExprId).collect())
        })
      });
      Ok(ids.unwrap_or_default())
    }) {
      Ok(exprs) => exprs,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  /// Pattern IDs in a body.
  pub fn pats_in_body(&self, body: BodyId) -> Vec<PatId> {
    match self.with_analyzed_state(|state| {
      let ids = state.body_map.get(&body).and_then(|meta| {
        meta.hir.and_then(|hir_id| {
          state
            .hir_lowered
            .get(&meta.file)
            .and_then(|lowered| lowered.body(hir_id))
            .map(|body| (0..body.pats.len() as u32).map(PatId).collect())
        })
      });
      Ok(ids.unwrap_or_default())
    }) {
      Ok(pats) => pats,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  /// Span for a definition, if available.
  pub fn def_span(&self, def: DefId) -> Option<Span> {
    match self.with_analyzed_state(|state| {
      Ok(state.def_data.get(&def).map(|data| Span {
        file: data.file,
        range: data.span,
      }))
    }) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Initializer expression for a variable definition, if recorded.
  pub fn var_initializer(&self, def: DefId) -> Option<VarInit> {
    let state = self.lock_state();
    let data = state.def_data.get(&def)?;
    let VarData {
      init, body, mode, ..
    } = match &data.kind {
      DefKind::Var(var) => var,
      _ => return None,
    };
    let expr = (*init)?;
    let decl_kind = match mode {
      VarDeclMode::Var => HirVarDeclKind::Var,
      VarDeclMode::Let => HirVarDeclKind::Let,
      VarDeclMode::Const => HirVarDeclKind::Const,
      _ => HirVarDeclKind::Var,
    };
    Some(VarInit {
      body: *body,
      expr,
      decl_kind,
      pat: None,
      span: Some(data.span),
    })
  }

  /// Span for an expression, if available.
  pub fn expr_span(&self, body: BodyId, expr: ExprId) -> Option<Span> {
    match self.with_analyzed_state(|state| {
      Ok(state.body_map.get(&body).and_then(|meta| {
        meta.hir.and_then(|hir_id| {
          state
            .hir_lowered
            .get(&meta.file)
            .and_then(|lowered| lowered.body(hir_id))
            .and_then(|body| {
              body.exprs.get(expr.0 as usize).map(|expr| Span {
                file: meta.file,
                range: expr.span,
              })
            })
        })
      }))
    }) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Span for a pattern, if available.
  pub fn pat_span(&self, body: BodyId, pat: PatId) -> Option<Span> {
    match self.with_analyzed_state(|state| {
      Ok(state.body_map.get(&body).and_then(|meta| {
        meta.hir.and_then(|hir_id| {
          state
            .hir_lowered
            .get(&meta.file)
            .and_then(|lowered| lowered.body(hir_id))
            .and_then(|body| {
              body.pats.get(pat.0 as usize).map(|pat| Span {
                file: meta.file,
                range: pat.span,
              })
            })
        })
      }))
    }) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Raw symbol occurrences for debugging.
  pub fn debug_symbol_occurrences(&self, file: FileId) -> Vec<(TextRange, semantic_js::SymbolId)> {
    let state = self.lock_state();
    state
      .symbol_occurrences
      .get(&file)
      .cloned()
      .unwrap_or_default()
      .into_iter()
      .map(|occ| (occ.range, occ.symbol))
      .collect()
  }

  /// Friendly name for a definition.
  pub fn def_name(&self, def: DefId) -> Option<String> {
    match self.def_name_fallible(def) {
      Ok(name) => name,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn def_name_fallible(&self, def: DefId) -> Result<Option<String>, FatalError> {
    self.with_analyzed_state(|state| Ok(state.def_data.get(&def).map(|d| d.name.clone())))
  }

  /// Body attached to a definition, if any.
  pub fn body_of_def(&self, def: DefId) -> Option<BodyId> {
    match self.body_of_def_fallible(def) {
      Ok(body) => body,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn body_of_def_fallible(&self, def: DefId) -> Result<Option<BodyId>, FatalError> {
    self.with_analyzed_state(|state| {
      Ok(state.def_data.get(&def).and_then(|d| match &d.kind {
        DefKind::Function(func) => func.body,
        DefKind::Var(var) => (var.body.0 != u32::MAX).then_some(var.body),
        DefKind::Import(_) => None,
        DefKind::Interface(_) => None,
        DefKind::TypeAlias(_) => None,
      }))
    })
  }

  /// Implicit top-level body for a file, if any.
  pub fn file_body(&self, file: FileId) -> Option<BodyId> {
    match self.file_body_fallible(file) {
      Ok(body) => body,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn file_body_fallible(&self, file: FileId) -> Result<Option<BodyId>, FatalError> {
    self.with_analyzed_state(|state| Ok(state.files.get(&file).and_then(|f| f.top_body)))
  }

  /// Span of a definition, if known.
  pub fn span_of_def(&self, def: DefId) -> Option<Span> {
    match self.span_of_def_fallible(def) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn span_of_def_fallible(&self, def: DefId) -> Result<Option<Span>, FatalError> {
    self.with_analyzed_state(|state| {
      Ok(
        state
          .def_data
          .get(&def)
          .map(|data| Span::new(data.file, data.span)),
      )
    })
  }

  /// Span of an expression within a body, if available from cached results.
  pub fn span_of_expr(&self, body: BodyId, expr: ExprId) -> Option<Span> {
    match self.span_of_expr_fallible(body, expr) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn span_of_expr_fallible(
    &self,
    body: BodyId,
    expr: ExprId,
  ) -> Result<Option<Span>, FatalError> {
    self.with_analyzed_state(|state| {
      let Some(meta) = state.body_map.get(&body).copied() else {
        return Ok(None);
      };
      let res = state.check_body(body);
      Ok(res.expr_span(expr).map(|range| Span::new(meta.file, range)))
    })
  }

  /// Serialize the current analyzed state into a deterministic snapshot suitable
  /// for caching or offline queries. All bodies and definitions are fully
  /// checked before serialization to ensure type and diagnostic tables are
  /// populated.
  #[cfg(feature = "serde")]
  pub fn snapshot(&self) -> ProgramSnapshot {
    use sha2::{Digest, Sha256};

    let mut state = self.lock_state();
    state.ensure_analyzed(&self.host, &self.roots, &self.cancelled);
    if let Err(fatal) = state.ensure_interned_types(&self.host, &self.roots, &self.cancelled) {
      state.diagnostics.push(fatal_to_diagnostic(fatal));
    }

    let mut body_ids: Vec<_> = state.body_map.keys().copied().collect();
    body_ids.sort_by_key(|id| id.0);
    for body in body_ids.iter() {
      let _ = state.check_body(*body);
    }

    let mut def_ids: Vec<_> = state.def_data.keys().copied().collect();
    def_ids.sort_by_key(|id| id.0);
    for def in def_ids.iter() {
      let _ = state.type_of_def(*def);
    }

    let mut file_ids: Vec<_> = state.file_kinds.keys().copied().collect();
    file_ids.sort_by_key(|id| id.0);
    let mut files = Vec::new();
    for file in file_ids {
      let kind = *state.file_kinds.get(&file).unwrap_or(&FileKind::Ts);
      let text = state.lib_texts.get(&file).cloned().or_else(|| {
        state
          .file_key_for_id(file)
          .and_then(|key| self.host.file_text(&key).ok())
      });
      let hash = if let Some(text) = text.as_ref() {
        let mut hasher = Sha256::new();
        hasher.update(text.as_bytes());
        format!("{:x}", hasher.finalize())
      } else {
        String::new()
      };
      let key = state
        .file_key_for_id(file)
        .unwrap_or_else(|| FileKey::new(format!("file{}.ts", file.0)));
      let is_lib = state.lib_file_ids.contains(&file);
      files.push(FileSnapshot {
        file,
        key,
        kind,
        is_lib,
        hash,
        text: text.map(|t| t.to_string()),
      });
    }

    let mut file_states = Vec::new();
    let mut file_state_ids: Vec<_> = state.files.keys().copied().collect();
    file_state_ids.sort_by_key(|id| id.0);
    for file in file_state_ids {
      let fs = state.files.get(&file).expect("file state present");
      let mut bindings: Vec<_> = fs
        .bindings
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
      bindings.sort_by(|a, b| a.0.cmp(&b.0));
      let mut defs = fs.defs.clone();
      defs.sort_by_key(|d| d.0);
      file_states.push(FileStateSnapshot {
        file,
        defs,
        exports: fs.exports.clone(),
        bindings,
        top_body: fs.top_body,
        ambient_modules: Vec::new(),
      });
    }

    let mut def_data = Vec::new();
    for def in def_ids.iter() {
      if let Some(data) = state.def_data.get(def) {
        def_data.push(DefSnapshot {
          def: *def,
          data: data.clone(),
        });
      }
    }

    let mut def_types: Vec<_> = state
      .def_types
      .iter()
      .map(|(def, ty)| (*def, *ty))
      .collect();
    def_types.sort_by_key(|(def, _)| def.0);

    let mut body_results: Vec<_> = state
      .body_results
      .iter()
      .map(|(id, res)| (*id, (**res).clone()))
      .collect();
    body_results.sort_by_key(|(id, _)| id.0);
    let body_results: Vec<_> = body_results.into_iter().map(|(_, res)| res).collect();

    let mut symbol_occurrences: Vec<_> = state
      .symbol_occurrences
      .iter()
      .map(|(file, occs)| {
        let mut occs = occs.clone();
        occs.sort_by_key(|occ| (occ.range.start, occ.range.end, occ.symbol.0));
        (*file, occs)
      })
      .collect();
    symbol_occurrences.sort_by_key(|(file, _)| file.0);

    let mut symbol_to_def: Vec<_> = state
      .symbol_to_def
      .iter()
      .map(|(sym, def)| (*sym, *def))
      .collect();
    symbol_to_def.sort_by_key(|(sym, _)| sym.0);

    let mut global_bindings: Vec<_> = state
      .global_bindings
      .iter()
      .map(|(name, binding)| (name.clone(), binding.clone()))
      .collect();
    global_bindings.sort_by(|a, b| a.0.cmp(&b.0));

    let interned_type_store = state
      .interned_store
      .as_ref()
      .map(|s| s.snapshot())
      .unwrap_or_else(|| tti::TypeStore::new().snapshot());
    let mut interned_def_types: Vec<_> = state
      .interned_def_types
      .iter()
      .map(|(def, ty)| (*def, *ty))
      .collect();
    interned_def_types.sort_by_key(|(def, _)| def.0);
    let mut enum_value_types: Vec<_> = state
      .enum_value_types
      .iter()
      .map(|(def, ty)| (*def, *ty))
      .collect();
    enum_value_types.sort_by_key(|(def, _)| def.0);
    let mut interned_type_params: Vec<_> = state
      .interned_type_params
      .iter()
      .map(|(def, params)| (*def, params.clone()))
      .collect();
    interned_type_params.sort_by_key(|(def, _)| def.0);

    let mut canonical_defs: Vec<_> = state.canonical_defs().into_iter().collect();
    canonical_defs.sort_by(|a, b| (a.0 .0, &a.0 .1).cmp(&(b.0 .0, &b.0 .1)));

    let mut namespace_types: Vec<_> = state
      .namespace_object_types
      .iter()
      .filter_map(|((file, name), (_, store_ty))| {
        state
          .find_namespace_def(*file, name)
          .map(|def| (def, *store_ty))
      })
      .collect();
    namespace_types.sort_by_key(|(def, _)| def.0);

    ProgramSnapshot {
      schema_version: PROGRAM_SNAPSHOT_VERSION,
      tool_version: env!("CARGO_PKG_VERSION").to_string(),
      compiler_options: state.compiler_options.clone(),
      roots: self
        .roots
        .iter()
        .filter_map(|key| state.file_id_for_key(key))
        .collect(),
      files,
      file_states,
      def_data,
      def_types,
      canonical_defs,
      namespace_types,
      body_results,
      symbol_occurrences,
      symbol_to_def,
      global_bindings,
      diagnostics: state.diagnostics.clone(),
      type_store: state.type_store.clone(),
      interned_type_store,
      interned_def_types,
      enum_value_types,
      interned_type_params,
      value_def_map: Vec::new(),
      builtin: state.builtin,
      next_def: state.next_def,
      next_body: state.next_body,
    }
  }

  /// Rehydrate a program from a previously captured snapshot. The provided host
  /// is used for subsequent queries (such as fetching file text) but the
  /// returned program skips parsing and checking, relying entirely on the
  /// snapshot contents.
  #[cfg(feature = "serde")]
  pub fn from_snapshot(host: impl Host, snapshot: ProgramSnapshot) -> Program {
    assert_eq!(
      snapshot.schema_version, PROGRAM_SNAPSHOT_VERSION,
      "Program snapshot schema mismatch"
    );
    let file_keys: HashMap<_, _> = snapshot
      .files
      .iter()
      .map(|file| (file.file, file.key.clone()))
      .collect();
    let root_keys: Vec<FileKey> = snapshot
      .roots
      .iter()
      .map(|id| {
        file_keys
          .get(id)
          .cloned()
          .unwrap_or_else(|| FileKey::new(format!("file{}.ts", id.0)))
      })
      .collect();
    let program = Program::with_lib_manager(host, root_keys, Arc::new(LibManager::new()));
    {
      let mut state = program.lock_state();
      state.analyzed = true;
      state.compiler_options = snapshot.compiler_options;
      state.checker_caches = CheckerCaches::new(state.compiler_options.cache.clone());
      state.cache_stats = CheckerCacheStats::default();
      for file in snapshot.files.into_iter() {
        state.file_keys.insert(file.key.clone(), file.file);
        state.file_ids.insert(file.file, file.key);
        state.file_kinds.insert(file.file, file.kind);
        if file.is_lib {
          state.lib_file_ids.insert(file.file);
        }
        if let Some(text) = file.text {
          state.lib_texts.insert(file.file, Arc::from(text));
        }
      }
      state.files = snapshot
        .file_states
        .into_iter()
        .map(|fs| {
          let bindings = fs.bindings.into_iter().collect();
          (
            fs.file,
            FileState {
              defs: fs.defs,
              exports: fs.exports,
              bindings,
              top_body: fs.top_body,
              reexports: Vec::new(),
              export_all: Vec::new(),
            },
          )
        })
        .collect();
      state.asts = HashMap::new();
      state.def_data = snapshot
        .def_data
        .into_iter()
        .map(|def| (def.def, def.data))
        .collect();
      state.body_map = HashMap::new();
      state.body_parents = HashMap::new();
      state.def_types = snapshot.def_types.into_iter().collect();
      state.body_results = snapshot
        .body_results
        .into_iter()
        .map(|res| (res.body(), Arc::new(res)))
        .collect();
      state.ensure_body_map_from_defs();
      state.symbol_occurrences = snapshot.symbol_occurrences.into_iter().collect();
      state.symbol_to_def = snapshot.symbol_to_def.into_iter().collect();
      state.global_bindings = snapshot.global_bindings.into_iter().collect();
      state.diagnostics = snapshot.diagnostics;
      state.type_store = snapshot.type_store;
      state.interned_store = Some(tti::TypeStore::from_snapshot(snapshot.interned_type_store));
      state.interned_def_types = snapshot.interned_def_types.into_iter().collect();
      state.enum_value_types = snapshot.enum_value_types.into_iter().collect();
      state.interned_type_params = snapshot.interned_type_params.into_iter().collect();
      if let Some(store) = state.interned_store.clone() {
        for (def, store_ty) in snapshot.namespace_types.into_iter() {
          state.def_types.entry(def).or_insert(store_ty);
          let def_data = state.def_data.get(&def).cloned();
          let interned = state
            .interned_def_types
            .get(&def)
            .copied()
            .unwrap_or_else(|| {
              let mut cache = HashMap::new();
              store.canon(convert_type_for_display(
                store_ty, &state, &store, &mut cache,
              ))
            });
          if let Some(data) = def_data {
            state
              .namespace_object_types
              .insert((data.file, data.name.clone()), (interned, store_ty));
          }
          state.interned_def_types.entry(def).or_insert(interned);
        }
      }
      state.builtin = snapshot.builtin;
      state.next_def = snapshot.next_def;
      state.next_body = snapshot.next_body;
      let mut max_symbol: u64 = 0;
      for data in state.def_data.values() {
        max_symbol = max_symbol.max(data.symbol.0 as u64);
      }
      for binding in state.global_bindings.values() {
        max_symbol = max_symbol.max(binding.symbol.0 as u64);
      }
      for bindings in state.files.values().map(|fs| &fs.bindings) {
        for binding in bindings.values() {
          max_symbol = max_symbol.max(binding.symbol.0 as u64);
        }
      }
      for sym in state.symbol_to_def.keys() {
        max_symbol = max_symbol.max(sym.0 as u64);
      }
      for occs in state.symbol_occurrences.values() {
        for occ in occs {
          max_symbol = max_symbol.max(occ.symbol.0 as u64);
        }
      }
      state.next_symbol = max_symbol.saturating_add(1);
    }
    program
  }
}

#[derive(Clone, Debug)]
struct Reexport {
  from: FileId,
  original: String,
  alias: String,
  type_only: bool,
  span: TextRange,
}

#[derive(Clone, Debug)]
struct ExportAll {
  from: FileId,
  type_only: bool,
  span: TextRange,
}

#[derive(Clone)]
struct FileState {
  defs: Vec<DefId>,
  exports: ExportMap,
  bindings: HashMap<String, SymbolBinding>,
  top_body: Option<BodyId>,
  reexports: Vec<Reexport>,
  export_all: Vec<ExportAll>,
}

struct HostResolver {
  host: Arc<dyn Host>,
  file_keys: HashMap<FileId, FileKey>,
  file_ids: HashMap<FileKey, FileId>,
}

impl sem_ts::Resolver for HostResolver {
  fn resolve(&self, from: sem_ts::FileId, specifier: &str) -> Option<sem_ts::FileId> {
    let from_key = self.file_keys.get(&FileId(from.0))?;
    let target_key = self.host.resolve(from_key, specifier)?;
    let target_id = self.file_ids.get(&target_key)?;
    Some(sem_ts::FileId(target_id.0))
  }
}

fn sem_file_kind(kind: FileKind) -> sem_ts::FileKind {
  match kind {
    FileKind::Dts => sem_ts::FileKind::Dts,
    _ => sem_ts::FileKind::Ts,
  }
}

#[allow(dead_code)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct DefData {
  pub name: String,
  pub file: FileId,
  pub span: TextRange,
  pub symbol: semantic_js::SymbolId,
  pub export: bool,
  pub kind: DefKind,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub enum DefKind {
  Function(FuncData),
  Var(VarData),
  Import(ImportData),
  Interface(InterfaceData),
  TypeAlias(TypeAliasData),
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct FuncData {
  pub params: Vec<ParamData>,
  pub return_ann: Option<TypeId>,
  pub body: Option<BodyId>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct ParamData {
  pub name: String,
  pub typ: Option<TypeId>,
  pub symbol: semantic_js::SymbolId,
  pub pat: Option<PatId>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct VarData {
  pub typ: Option<TypeId>,
  pub init: Option<ExprId>,
  pub body: BodyId,
  pub annotated: bool,
  #[cfg_attr(
    feature = "serde",
    serde(skip_serializing, skip_deserializing, default = "default_var_mode")
  )]
  pub mode: VarDeclMode,
}

#[cfg(feature = "serde")]
fn default_var_mode() -> VarDeclMode {
  VarDeclMode::Var
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct ImportData {
  pub specifier: String,
  pub from: Option<FileId>,
  pub original: String,
  pub is_type_only: bool,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct InterfaceData {
  pub typ: TypeId,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct TypeAliasData {
  pub typ: TypeId,
}

#[derive(Clone, Debug)]
struct SemHirBuilder {
  file: FileId,
  file_kind: sem_ts::FileKind,
  decls: Vec<sem_ts::Decl>,
  imports: Vec<sem_ts::Import>,
  import_equals: Vec<sem_ts::ImportEquals>,
  exports: Vec<sem_ts::Export>,
}

impl SemHirBuilder {
  fn new(file: FileId, file_kind: sem_ts::FileKind) -> Self {
    SemHirBuilder {
      file,
      file_kind,
      decls: Vec::new(),
      imports: Vec::new(),
      import_equals: Vec::new(),
      exports: Vec::new(),
    }
  }

  fn add_decl(
    &mut self,
    def: DefId,
    name: String,
    kind: sem_ts::DeclKind,
    exported: sem_ts::Exported,
    span: TextRange,
  ) {
    self.decls.push(sem_ts::Decl {
      def_id: sem_ts::DefId(def.0),
      name,
      kind,
      is_ambient: false,
      is_global: false,
      exported,
      span,
    });
  }

  fn add_import(&mut self, import: sem_ts::Import) {
    self.imports.push(import);
  }

  fn add_named_export(
    &mut self,
    specifier: Option<String>,
    specifier_span: Option<TextRange>,
    items: Vec<sem_ts::ExportSpecifier>,
    is_type_only: bool,
  ) {
    if items.is_empty() {
      return;
    }
    self
      .exports
      .push(sem_ts::Export::Named(sem_ts::NamedExport {
        specifier,
        specifier_span,
        items,
        is_type_only,
      }));
  }

  fn add_export_all(&mut self, specifier: String, specifier_span: TextRange, is_type_only: bool) {
    self.exports.push(sem_ts::Export::All(sem_ts::ExportAll {
      specifier,
      is_type_only,
      specifier_span,
      alias: None,
      alias_span: None,
    }));
  }

  fn finish(self) -> sem_ts::HirFile {
    sem_ts::HirFile {
      file_id: sem_ts::FileId(self.file.0),
      module_kind: sem_ts::ModuleKind::Module,
      file_kind: self.file_kind,
      decls: self.decls,
      imports: self.imports,
      import_equals: self.import_equals,
      exports: self.exports,
      export_as_namespace: Vec::new(),
      ambient_modules: Vec::new(),
    }
  }
}

#[derive(Clone, Copy, Debug)]
struct BodyMeta {
  file: FileId,
  hir: Option<hir_js::BodyId>,
  kind: HirBodyKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum DefMatchKind {
  Function,
  Var,
  Interface,
  TypeAlias,
  Import,
  Other,
}

fn match_kind_from_def(kind: &DefKind) -> DefMatchKind {
  match kind {
    DefKind::Function(_) => DefMatchKind::Function,
    DefKind::Var(_) => DefMatchKind::Var,
    DefKind::Import(_) => DefMatchKind::Import,
    DefKind::Interface(_) => DefMatchKind::Interface,
    DefKind::TypeAlias(_) => DefMatchKind::TypeAlias,
  }
}

fn match_kind_from_hir(kind: HirDefKind) -> DefMatchKind {
  match kind {
    HirDefKind::Function | HirDefKind::Method | HirDefKind::Constructor => DefMatchKind::Function,
    HirDefKind::ImportBinding => DefMatchKind::Import,
    HirDefKind::Var
    | HirDefKind::Field
    | HirDefKind::Param
    | HirDefKind::ExportAlias
    | HirDefKind::Namespace
    | HirDefKind::Module
    | HirDefKind::Enum
    | HirDefKind::EnumMember => DefMatchKind::Var,
    HirDefKind::Interface => DefMatchKind::Interface,
    HirDefKind::TypeAlias => DefMatchKind::TypeAlias,
    _ => DefMatchKind::Other,
  }
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct TypeStore {
  kinds: Vec<TypeKind>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ObjectProperty {
  pub(crate) typ: TypeId,
  pub(crate) optional: bool,
  pub(crate) readonly: bool,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ObjectType {
  pub(crate) props: BTreeMap<String, ObjectProperty>,
  pub(crate) string_index: Option<TypeId>,
  pub(crate) number_index: Option<TypeId>,
}

impl ObjectType {
  pub(crate) fn empty() -> ObjectType {
    ObjectType {
      props: BTreeMap::new(),
      string_index: None,
      number_index: None,
    }
  }

  pub(crate) fn has_index_signature(&self) -> bool {
    self.string_index.is_some() || self.number_index.is_some()
  }
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TypeKind {
  Any,
  Unknown,
  Never,
  Void,
  Number,
  String,
  Boolean,
  Null,
  Undefined,
  LiteralString(String),
  LiteralNumber(String),
  LiteralBoolean(bool),
  Tuple(Vec<TypeId>, bool),
  Array(TypeId),
  Union(Vec<TypeId>),
  Function {
    params: Vec<TypeId>,
    ret: TypeId,
  },
  Predicate {
    parameter: String,
    asserted: Option<TypeId>,
    asserts: bool,
  },
  Object(ObjectType),
}

#[allow(dead_code)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Copy, Debug)]
pub struct BuiltinTypes {
  pub any: TypeId,
  pub unknown: TypeId,
  pub never: TypeId,
  pub void: TypeId,
  pub number: TypeId,
  pub string: TypeId,
  pub boolean: TypeId,
  pub null: TypeId,
  pub undefined: TypeId,
  pub object: TypeId,
}

impl TypeStore {
  const UNKNOWN_IDX: usize = 1;

  fn new() -> (TypeStore, BuiltinTypes) {
    let mut store = TypeStore { kinds: Vec::new() };
    let any = store.alloc(TypeKind::Any);
    let unknown = store.alloc(TypeKind::Unknown);
    let never = store.alloc(TypeKind::Never);
    let void = store.alloc(TypeKind::Void);
    let number = store.alloc(TypeKind::Number);
    let string = store.alloc(TypeKind::String);
    let boolean = store.alloc(TypeKind::Boolean);
    let null = store.alloc(TypeKind::Null);
    let undefined = store.alloc(TypeKind::Undefined);
    let object = store.alloc(TypeKind::Object(ObjectType::empty()));
    (
      store,
      BuiltinTypes {
        any,
        unknown,
        never,
        void,
        number,
        string,
        boolean,
        null,
        undefined,
        object,
      },
    )
  }

  fn alloc(&mut self, kind: TypeKind) -> TypeId {
    if let Some((idx, _)) = self.kinds.iter().enumerate().find(|(_, k)| **k == kind) {
      return TypeId((idx as u128).into());
    }
    let id = TypeId((self.kinds.len() as u128).into());
    self.kinds.push(kind);
    id
  }

  pub(crate) fn kind(&self, id: TypeId) -> &TypeKind {
    self.kinds.get(id.0 as usize).unwrap_or_else(|| {
      // Gracefully degrade to `unknown` when encountering an out-of-range
      // identifier instead of panicking; upstream code will treat this as a
      // cache miss and recompute.
      let fallback = Self::UNKNOWN_IDX.min(self.kinds.len().saturating_sub(1));
      &self.kinds[fallback]
    })
  }

  pub(crate) fn union(&mut self, mut types: Vec<TypeId>, builtin: &BuiltinTypes) -> TypeId {
    let mut flat = Vec::new();
    for ty in types.drain(..) {
      match self.kind(ty) {
        TypeKind::Union(members) => flat.extend(members.iter().copied()),
        TypeKind::Never => {}
        _ => flat.push(ty),
      }
    }
    types = flat;
    if types.is_empty() {
      return builtin.never;
    }
    types.sort_by(|a, b| a.0.cmp(&b.0));
    types.dedup();
    if types.len() == 1 {
      return types[0];
    }
    let types = types;
    self.alloc(TypeKind::Union(types))
  }

  pub(crate) fn array(&mut self, element: TypeId) -> TypeId {
    self.alloc(TypeKind::Array(element))
  }

  pub(crate) fn tuple(&mut self, elements: Vec<TypeId>, readonly: bool) -> TypeId {
    self.alloc(TypeKind::Tuple(elements, readonly))
  }

  pub(crate) fn function(&mut self, params: Vec<TypeId>, ret: TypeId) -> TypeId {
    self.alloc(TypeKind::Function { params, ret })
  }

  fn object(&mut self, obj: ObjectType) -> TypeId {
    self.alloc(TypeKind::Object(obj))
  }

  pub(crate) fn literal_string(&mut self, value: String) -> TypeId {
    self.alloc(TypeKind::LiteralString(value))
  }

  pub(crate) fn literal_number(&mut self, value: String) -> TypeId {
    self.alloc(TypeKind::LiteralNumber(value))
  }

  pub(crate) fn literal_boolean(&mut self, value: bool) -> TypeId {
    self.alloc(TypeKind::LiteralBoolean(value))
  }

  pub(crate) fn predicate(
    &mut self,
    parameter: String,
    asserted: Option<TypeId>,
    asserts: bool,
  ) -> TypeId {
    self.alloc(TypeKind::Predicate {
      parameter,
      asserted,
      asserts,
    })
  }
}

pub(crate) fn lookup_property_type(
  store: &mut TypeStore,
  ty: TypeId,
  name: &str,
  builtin: &BuiltinTypes,
) -> Option<TypeId> {
  match store.kind(ty).clone() {
    TypeKind::Any | TypeKind::Unknown => None,
    TypeKind::Object(obj) => {
      if let Some(prop) = obj.props.get(name) {
        return Some(prop.typ);
      }
      if name.parse::<usize>().is_ok() {
        obj.number_index.or(obj.string_index)
      } else {
        obj.string_index
      }
    }
    TypeKind::Union(members) => {
      let mut collected = Vec::new();
      for member in members {
        if let Some(prop_ty) = lookup_property_type(store, member, name, builtin) {
          collected.push(prop_ty);
        }
      }
      if collected.is_empty() {
        None
      } else {
        Some(store.union(collected, builtin))
      }
    }
    _ => None,
  }
}

macro_rules! query_span {
  ($name:literal, $file:expr, $def:expr, $body:expr, $cache_hit:expr) => {
    debug_span!(
      $name,
      file = $file,
      def = $def,
      body = $body,
      type_id = tracing::field::Empty,
      cache_hit = $cache_hit,
      duration_ms = tracing::field::Empty,
    )
  };
}

/// Lightweight helper for emitting structured tracing spans around query-like
/// boundaries. When tracing is disabled, this is a no-op to keep hot paths
/// cheap.
struct QuerySpan {
  span: tracing::Span,
  start: Instant,
  kind: QueryKind,
  cache_hit: bool,
  span_enabled: bool,
  query_stats: Option<QueryStatsCollector>,
}

impl QuerySpan {
  fn enter(
    kind: QueryKind,
    span: tracing::Span,
    type_id: Option<TypeId>,
    cache_hit: bool,
    query_stats: Option<QueryStatsCollector>,
  ) -> Option<QuerySpan> {
    let span_enabled = !span.is_disabled();
    if !span_enabled && query_stats.is_none() {
      return None;
    }
    if span_enabled {
      if let Some(ty) = type_id {
        span.record("type_id", ty.0);
      }
      let _guard = span.enter();
      drop(_guard);
    }
    Some(QuerySpan {
      span,
      start: Instant::now(),
      kind,
      cache_hit,
      span_enabled,
      query_stats,
    })
  }

  fn finish(self, type_id: Option<TypeId>) {
    let duration = self.start.elapsed();
    if let Some(stats) = &self.query_stats {
      stats.record(self.kind, self.cache_hit, duration);
    }
    if self.span_enabled {
      if let Some(ty) = type_id {
        self.span.record("type_id", ty.0);
      }
      self
        .span
        .record("duration_ms", duration.as_secs_f64() * 1000.0);
    }
  }
}

struct ProgramState {
  analyzed: bool,
  lib_manager: Arc<LibManager>,
  compiler_options: CompilerOptions,
  checker_caches: CheckerCaches,
  cache_stats: CheckerCacheStats,
  asts: HashMap<FileId, Arc<Node<TopLevel>>>,
  files: HashMap<FileId, FileState>,
  def_data: HashMap<DefId, DefData>,
  body_map: HashMap<BodyId, BodyMeta>,
  body_parents: HashMap<BodyId, BodyId>,
  hir_lowered: HashMap<FileId, LowerResult>,
  sem_hir: HashMap<FileId, sem_ts::HirFile>,
  semantics: Option<sem_ts::TsProgramSemantics>,
  def_types: HashMap<DefId, TypeId>,
  enum_value_types: HashMap<DefId, tti::TypeId>,
  body_results: HashMap<BodyId, Arc<BodyCheckResult>>,
  symbol_occurrences: HashMap<FileId, Vec<SymbolOccurrence>>,
  symbol_to_def: HashMap<semantic_js::SymbolId, DefId>,
  file_keys: HashMap<FileKey, FileId>,
  file_ids: HashMap<FileId, FileKey>,
  file_kinds: HashMap<FileId, FileKind>,
  lib_file_ids: HashSet<FileId>,
  lib_texts: HashMap<FileId, Arc<str>>,
  global_bindings: HashMap<String, SymbolBinding>,
  namespace_object_types: HashMap<(FileId, String), (tti::TypeId, TypeId)>,
  callable_overloads: HashMap<(FileId, String), Vec<DefId>>,
  diagnostics: Vec<Diagnostic>,
  type_store: TypeStore,
  interned_store: Option<Arc<tti::TypeStore>>,
  interned_def_types: HashMap<DefId, tti::TypeId>,
  interned_type_params: HashMap<DefId, Vec<TypeParamId>>,
  builtin: BuiltinTypes,
  query_stats: QueryStatsCollector,
  current_file: Option<FileId>,
  next_file: u32,
  next_def: u32,
  next_body: u32,
  next_symbol: u64,
  type_stack: Vec<DefId>,
  interning: bool,
}

impl ProgramState {
  fn new(lib_manager: Arc<LibManager>, query_stats: QueryStatsCollector) -> ProgramState {
    let default_options = CompilerOptions::default();
    let (type_store, builtin) = TypeStore::new();
    ProgramState {
      analyzed: false,
      lib_manager,
      compiler_options: default_options.clone(),
      checker_caches: CheckerCaches::new(default_options.cache.clone()),
      cache_stats: CheckerCacheStats::default(),
      asts: HashMap::new(),
      files: HashMap::new(),
      def_data: HashMap::new(),
      body_map: HashMap::new(),
      body_parents: HashMap::new(),
      hir_lowered: HashMap::new(),
      sem_hir: HashMap::new(),
      semantics: None,
      def_types: HashMap::new(),
      enum_value_types: HashMap::new(),
      body_results: HashMap::new(),
      symbol_occurrences: HashMap::new(),
      symbol_to_def: HashMap::new(),
      file_keys: HashMap::new(),
      file_ids: HashMap::new(),
      file_kinds: HashMap::new(),
      lib_file_ids: HashSet::new(),
      lib_texts: HashMap::new(),
      global_bindings: HashMap::new(),
      namespace_object_types: HashMap::new(),
      callable_overloads: HashMap::new(),
      diagnostics: Vec::new(),
      type_store,
      interned_store: None,
      interned_def_types: HashMap::new(),
      interned_type_params: HashMap::new(),
      builtin,
      query_stats,
      current_file: None,
      next_file: 0,
      next_def: 0,
      next_body: 0,
      next_symbol: 0,
      type_stack: Vec::new(),
      interning: false,
    }
  }

  fn file_id_for_key(&self, key: &FileKey) -> Option<FileId> {
    self
      .file_keys
      .get(key)
      .copied()
      .and_then(|id| {
        if !self.lib_file_ids.contains(&id) {
          Some(id)
        } else {
          None
        }
      })
      .or_else(|| self.file_keys.get(key).copied())
  }

  fn file_key_for_id(&self, id: FileId) -> Option<FileKey> {
    self.file_ids.get(&id).cloned()
  }

  fn intern_file_key(&mut self, key: FileKey, origin: FileOrigin) -> FileId {
    let want_lib = matches!(origin, FileOrigin::Lib);
    if let Some(existing) = self.file_ids.iter().find_map(|(id, stored)| {
      if stored != &key {
        return None;
      }
      let is_lib = self.lib_file_ids.contains(id);
      ((want_lib && is_lib) || (!want_lib && !is_lib)).then_some(*id)
    }) {
      return existing;
    }

    let mut id = FileId(self.next_file);
    if let Some(preferred) = Self::preferred_file_id(&key) {
      let preferred = FileId(preferred);
      if !self.file_ids.contains_key(&preferred) {
        id = preferred;
      }
    }
    self.next_file = self.next_file.max(id.0 + 1);
    self.file_ids.insert(id, key.clone());
    match origin {
      FileOrigin::Lib => {
        self.lib_file_ids.insert(id);
        self.file_keys.entry(key).or_insert(id);
      }
      FileOrigin::Source => {
        self.file_keys.insert(key, id);
      }
    }
    id
  }

  fn preferred_file_id(key: &FileKey) -> Option<u32> {
    let name = key.as_str();
    let remainder = name.strip_prefix("file")?;
    let stripped = remainder
      .strip_suffix(".ts")
      .or_else(|| remainder.strip_suffix(".tsx"))?;
    stripped.parse::<u32>().ok()
  }

  fn def_namespaces(kind: &DefKind) -> sem_ts::Namespace {
    match kind {
      DefKind::Function(_) | DefKind::Var(_) => sem_ts::Namespace::VALUE,
      DefKind::Interface(_) | DefKind::TypeAlias(_) => sem_ts::Namespace::TYPE,
      DefKind::Import(_) => {
        sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE | sem_ts::Namespace::NAMESPACE
      }
    }
  }

  fn def_priority(&self, def: DefId, ns: sem_ts::Namespace) -> u8 {
    let Some(data) = self.def_data.get(&def) else {
      return u8::MAX;
    };
    if !Self::def_namespaces(&data.kind).contains(ns) {
      return u8::MAX;
    }
    if ns.contains(sem_ts::Namespace::VALUE) {
      return match &data.kind {
        DefKind::Function(_) => 0,
        DefKind::Var(var) if var.body.0 != u32::MAX => 1,
        DefKind::Import(_) => 2,
        DefKind::Var(_) => 3,
        DefKind::Interface(_) | DefKind::TypeAlias(_) => 4,
      };
    }
    if ns.contains(sem_ts::Namespace::TYPE) {
      return match &data.kind {
        DefKind::Interface(_) => 0,
        DefKind::TypeAlias(_) => 1,
        DefKind::Import(_) => 2,
        _ => 3,
      };
    }
    if ns.contains(sem_ts::Namespace::NAMESPACE) {
      return match &data.kind {
        DefKind::Var(var) if var.body.0 == u32::MAX => 0,
        DefKind::Import(_) => 1,
        _ => 2,
      };
    }
    u8::MAX
  }

  pub(crate) fn map_decl_to_program_def(
    &self,
    decl: &sem_ts::DeclData,
    ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    let direct = DefId(decl.def_id.0);
    if let Some(data) = self.def_data.get(&direct) {
      if Self::def_namespaces(&data.kind).contains(ns) {
        return Some(direct);
      }
    }

    let mut best: Option<(u8, DefId)> = None;
    for (id, data) in self.def_data.iter() {
      if data.file == FileId(decl.file.0) && data.name == decl.name {
        if !Self::def_namespaces(&data.kind).contains(ns) {
          continue;
        }
        let pri = self.def_priority(*id, ns);
        best = best
          .map(|(best_pri, best_id)| {
            if pri < best_pri || (pri == best_pri && id < &best_id) {
              (pri, *id)
            } else {
              (best_pri, best_id)
            }
          })
          .or(Some((pri, *id)));
      }
    }
    best.map(|(_, id)| id)
  }

  fn canonical_defs(&mut self) -> HashMap<(FileId, String), DefId> {
    let mut def_entries: Vec<_> = self
      .def_data
      .iter()
      .map(|(id, data)| (*id, data.clone()))
      .collect();
    def_entries.sort_by_key(|(id, data)| (data.file.0, data.span.start, id.0));
    let mut def_by_name: HashMap<(FileId, String), DefId> = HashMap::new();
    for (def_id, data) in def_entries {
      let canonical_file = self
        .file_key_for_id(data.file)
        .and_then(|key| self.file_keys.get(&key).copied())
        .unwrap_or(data.file);
      let keys = if canonical_file == data.file {
        vec![canonical_file]
      } else {
        vec![canonical_file, data.file]
      };
      for file in keys {
        let key = (file, data.name.clone());
        let ns = match data.kind {
          DefKind::Interface(_) | DefKind::TypeAlias(_) => sem_ts::Namespace::TYPE,
          _ => sem_ts::Namespace::VALUE,
        };
        let mut mapped_def = def_id;
        if let DefKind::Import(import) = &data.kind {
          if let Some(entry) = self.resolve_import_entry(import) {
            if let Some(target) = entry.def {
              mapped_def = target;
            }
          }
        }
        def_by_name
          .entry(key)
          .and_modify(|existing| {
            let current = self.def_priority(*existing, ns);
            let new_pri = self.def_priority(mapped_def, ns);
            if new_pri < current || (new_pri == current && mapped_def < *existing) {
              *existing = mapped_def;
            }
          })
          .or_insert(mapped_def);
      }
    }
    def_by_name
  }

  fn rebuild_callable_overloads(&mut self) {
    self.callable_overloads.clear();
    if let Some(semantics) = self.semantics.as_ref() {
      let symbols = semantics.symbols();
      let mut seen_symbols = HashSet::new();
      for def_id in self
        .def_data
        .iter()
        .filter_map(|(def_id, data)| matches!(data.kind, DefKind::Function(_)).then_some(def_id))
      {
        let Some(symbol) =
          semantics.symbol_for_def(sem_ts::DefId(def_id.0), sem_ts::Namespace::VALUE)
        else {
          continue;
        };
        if !seen_symbols.insert(symbol) {
          continue;
        }
        let mut defs = Vec::new();
        let mut seen_defs = HashSet::new();
        for decl_id in semantics.symbol_decls(symbol, sem_ts::Namespace::VALUE) {
          let decl = symbols.decl(*decl_id);
          if !matches!(decl.kind, sem_ts::DeclKind::Function) {
            continue;
          }
          if let Some(mapped) = self.map_decl_to_program_def(decl, sem_ts::Namespace::VALUE) {
            if seen_defs.insert(mapped) {
              defs.push(mapped);
            }
          }
        }
        if !defs.is_empty() {
          for def in defs.iter().copied() {
            if let Some(def_data) = self.def_data.get(&def) {
              self
                .callable_overloads
                .entry((def_data.file, def_data.name.clone()))
                .or_insert_with(|| defs.clone());
            }
          }
        }
      }
      return;
    }

    let mut grouped: BTreeMap<(FileId, String), Vec<(DefId, TextRange)>> = BTreeMap::new();
    for (id, data) in self
      .def_data
      .iter()
      .filter(|(_, data)| matches!(data.kind, DefKind::Function(_)))
    {
      grouped
        .entry((data.file, data.name.clone()))
        .or_default()
        .push((*id, data.span));
    }
    for ((file, name), mut defs) in grouped.into_iter() {
      defs.sort_by_key(|(id, span)| (span.start, span.end, id.0));
      let ordered: Vec<_> = defs.into_iter().map(|(id, _)| id).collect();
      self.callable_overloads.insert((file, name), ordered);
    }
  }

  fn callable_overload_defs(&mut self, def: DefId) -> Option<Vec<DefId>> {
    let (file, name) = {
      let data = self.def_data.get(&def)?;
      if !matches!(data.kind, DefKind::Function(_)) {
        return None;
      }
      (data.file, data.name.clone())
    };
    if self.callable_overloads.is_empty() {
      self.rebuild_callable_overloads();
    }
    let key = (file, name);
    Some(
      self
        .callable_overloads
        .get(&key)
        .cloned()
        .unwrap_or_else(|| vec![def]),
    )
  }

  fn merged_overload_callable_type(
    &mut self,
    defs: &[DefId],
    store: &Arc<tti::TypeStore>,
    cache: &mut HashMap<TypeId, tti::TypeId>,
  ) -> Option<tti::TypeId> {
    if defs.is_empty() {
      return None;
    }
    let mut overloads = Vec::new();
    let mut seen_sigs = HashSet::new();
    for def in defs.iter().copied() {
      if !self.interned_def_types.contains_key(&def) {
        let _ = self.type_of_def(def);
      }
      let ty = self.interned_def_types.get(&def).copied().or_else(|| {
        self.def_types.get(&def).copied().map(|store_ty| {
          let mapped = store.canon(convert_type_for_display(store_ty, self, store, cache));
          self.interned_def_types.insert(def, mapped);
          mapped
        })
      });
      let Some(ty) = ty else {
        continue;
      };
      if let tti::TypeKind::Callable { overloads: sigs } = store.type_kind(ty) {
        let mut sigs: Vec<_> = sigs.iter().copied().collect();
        sigs.sort();
        for sig in sigs.into_iter() {
          if seen_sigs.insert(sig) {
            overloads.push(sig);
          }
        }
      }
    }
    if overloads.is_empty() {
      return None;
    }
    Some(store.canon(store.intern_type(tti::TypeKind::Callable { overloads })))
  }

  fn callable_overload_type_for_def(
    &mut self,
    def: DefId,
    store: &Arc<tti::TypeStore>,
    cache: &mut HashMap<TypeId, tti::TypeId>,
  ) -> Option<tti::TypeId> {
    let defs = self.callable_overload_defs(def)?;
    if defs.len() < 2 {
      return None;
    }
    let merged = self.merged_overload_callable_type(&defs, store, cache)?;
    for member in defs {
      self.interned_def_types.insert(member, merged);
    }
    Some(merged)
  }

  fn merge_callable_overload_types(&mut self) {
    let Some(store) = self.interned_store.clone() else {
      return;
    };
    if self.callable_overloads.is_empty() {
      self.rebuild_callable_overloads();
    }
    let mut cache = HashMap::new();
    let mut keys: Vec<_> = self.callable_overloads.keys().cloned().collect();
    keys.sort_by(|a, b| (a.0 .0, &a.1).cmp(&(b.0 .0, &b.1)));
    for key in keys.into_iter() {
      let Some(defs) = self.callable_overloads.get(&key).cloned() else {
        continue;
      };
      if defs.len() < 2 {
        continue;
      }
      if let Some(merged) = self.merged_overload_callable_type(&defs, &store, &mut cache) {
        for def in defs.into_iter() {
          self.interned_def_types.insert(def, merged);
        }
      }
    }
  }

  fn interned_unknown(&self) -> TypeId {
    self
      .interned_store
      .as_ref()
      .map(|s| s.primitive_ids().unknown)
      .unwrap_or(self.builtin.unknown)
  }

  fn build_namespace_object_type(
    store: &Arc<tti::TypeStore>,
    existing: Option<tti::TypeId>,
    members: &[String],
  ) -> tti::TypeId {
    let mut shape = existing
      .and_then(|ty| match store.type_kind(ty) {
        tti::TypeKind::Object(obj) => Some(store.shape(store.object(obj).shape)),
        _ => None,
      })
      .unwrap_or_else(tti::Shape::new);
    for name in members.iter() {
      let key = PropKey::String(store.intern_name(name.clone()));
      shape.properties.push(Property {
        key,
        data: PropData {
          ty: store.primitive_ids().any,
          optional: false,
          readonly: true,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      });
    }
    let shape_id = store.intern_shape(shape);
    let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
    store.intern_type(tti::TypeKind::Object(obj_id))
  }

  fn build_namespace_type_store_object(
    &mut self,
    existing: Option<TypeId>,
    members: &[String],
  ) -> TypeId {
    let mut obj = existing
      .and_then(|ty| match self.type_store.kind(ty).clone() {
        TypeKind::Object(obj) => Some(obj),
        _ => None,
      })
      .unwrap_or_else(ObjectType::empty);
    for name in members.iter() {
      obj.props.entry(name.clone()).or_insert(ObjectProperty {
        typ: self.builtin.any,
        optional: false,
        readonly: true,
      });
    }
    self.type_store.object(obj)
  }

  fn find_namespace_def(&self, file: FileId, name: &str) -> Option<DefId> {
    self
      .def_data
      .iter()
      .find_map(|(id, data)| match &data.kind {
        DefKind::Var(var) if data.file == file && data.name == name && var.body.0 == u32::MAX => {
          Some(*id)
        }
        _ => None,
      })
  }

  fn merge_namespace_value_types(&mut self) {
    let Some(store) = self.interned_store.clone() else {
      return;
    };
    let mut rebuilt: HashMap<(FileId, String), (tti::TypeId, TypeId)> = HashMap::new();
    let mut namespaces: Vec<(FileId, String, Vec<DefId>)> = Vec::new();
    let mut namespace_groups: HashMap<(FileId, String), Vec<DefId>> = HashMap::new();
    let mut def_entries: Vec<_> = self.def_data.iter().collect();
    def_entries.sort_by_key(|(id, data)| (data.file.0, data.span.start, id.0));
    for (def_id, data) in def_entries.iter().copied() {
      if self.enum_value_types.contains_key(def_id) {
        continue;
      }
      if let DefKind::Var(var) = &data.kind {
        if var.body.0 == u32::MAX {
          let members: Vec<DefId> = def_entries
            .iter()
            .copied()
            .filter_map(|(member_id, member)| {
              if member.file != data.file || member_id == def_id {
                return None;
              }
              if member.span.start < data.span.start || member.span.end > data.span.end {
                return None;
              }
              Some(*member_id)
            })
            .collect();
          namespace_groups
            .entry((data.file, data.name.clone()))
            .or_default()
            .push(*def_id);
          namespaces.push((data.file, data.name.clone(), members));
        }
      }
    }
    namespaces.sort_by(|a, b| (a.0 .0, &a.1).cmp(&(b.0 .0, &b.1)));
    let mut merged_members: BTreeMap<(FileId, String), Vec<DefId>> = BTreeMap::new();
    for (file, name, members) in namespaces.into_iter() {
      merged_members
        .entry((file, name))
        .or_default()
        .extend(members.into_iter());
    }
    for ((file, name), members) in merged_members.into_iter() {
      let mut shape = tti::Shape::new();
      let mut obj = ObjectType::empty();
      let mut seen = HashSet::new();
      for member_id in members.into_iter() {
        if !seen.insert(member_id) {
          continue;
        }
        if let Some(data) = self.def_data.get(&member_id) {
          match &data.kind {
            DefKind::Interface(_) | DefKind::TypeAlias(_) => continue,
            DefKind::Import(import) if import.is_type_only => continue,
            _ => {}
          }
        }
        let ty_interned = match self.export_type_for_def(member_id) {
          Some(ty) => store.canon(ty),
          None => continue,
        };
        if std::env::var("TRACE_NS").is_ok() {
          let kind = store.type_kind(ty_interned).clone();
          if let Some(data) = self.def_data.get(&member_id) {
            eprintln!("namespace member {} ty {:?}", data.name, kind);
          }
        }
        let ty_store = if let Some(store_ty) = self.def_types.get(&member_id).copied() {
          store_ty
        } else {
          self.import_interned_type(ty_interned)
        };
        let member_name = self
          .def_data
          .get(&member_id)
          .map(|d| d.name.clone())
          .unwrap_or_default();
        let key = PropKey::String(store.intern_name(member_name.clone()));
        shape.properties.push(Property {
          key,
          data: PropData {
            ty: ty_interned,
            optional: false,
            readonly: true,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
        obj.props.entry(member_name).or_insert(ObjectProperty {
          typ: ty_store,
          optional: false,
          readonly: true,
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      let interned = store.intern_type(tti::TypeKind::Object(obj_id));
      let store_ty = self.type_store.object(obj);
      rebuilt.insert((file, name.clone()), (interned, store_ty));
      if let Some(defs) = namespace_groups.get(&(file, name.clone())) {
        for def_id in defs.iter() {
          self.def_types.insert(*def_id, store_ty);
          self.interned_def_types.insert(*def_id, interned);
        }
      }
    }
    if !rebuilt.is_empty() {
      self.namespace_object_types = rebuilt.clone();
    }
    let mut entries: Vec<_> = self
      .namespace_object_types
      .iter()
      .map(|(k, v)| (k.clone(), *v))
      .collect();
    entries.sort_by(|a, b| (a.0 .0, &a.0 .1).cmp(&(b.0 .0, &b.0 .1)));
    for ((file, name), (ns_interned, ns_store)) in entries.into_iter() {
      let ns_def = self.find_namespace_def(file, &name);
      let value_def = self
        .def_data
        .iter()
        .find_map(|(id, data)| match &data.kind {
          DefKind::Function(_) if data.file == file && data.name == name => Some(*id),
          DefKind::Var(var) if data.file == file && data.name == name && var.body.0 != u32::MAX => {
            Some(*id)
          }
          _ => None,
        });
      if let (Some(ns_def), Some(val_def)) = (ns_def, value_def) {
        self.def_types.remove(&val_def);
        self.interned_def_types.remove(&val_def);
        let raw_ty = self.type_of_def(val_def);
        let val_interned = if store.contains_type_id(raw_ty) {
          store.canon(raw_ty)
        } else {
          let mut cache = HashMap::new();
          store.canon(convert_type_for_display(raw_ty, self, &store, &mut cache))
        };
        let val_store_ty = self.import_interned_type(val_interned);
        let merged = store.intersection(vec![val_interned, ns_interned]);
        self.interned_def_types.insert(ns_def, merged);
        self.interned_def_types.insert(val_def, merged);
        self.def_types.insert(ns_def, ns_store);
        self.def_types.insert(val_def, val_store_ty);
        if let Some(file_state) = self.files.get_mut(&file) {
          if let Some(binding) = file_state.bindings.get_mut(&name) {
            binding.type_id = Some(merged);
          }
          if let Some(entry) = file_state.exports.get_mut(&name) {
            entry.type_id = Some(merged);
          }
        }
      }
    }
  }

  fn ensure_analyzed(&mut self, host: &Arc<dyn Host>, roots: &[FileKey], cancelled: &AtomicBool) {
    if let Err(fatal) = self.ensure_analyzed_result(host, roots, cancelled) {
      self.diagnostics.push(fatal_to_diagnostic(fatal));
    }
  }

  fn ensure_analyzed_result(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileKey],
    cancelled: &AtomicBool,
  ) -> Result<(), FatalError> {
    if self.analyzed {
      return Ok(());
    }
    let libs = self.collect_libraries(host.as_ref());
    let lib_ids: Vec<FileId> = libs
      .iter()
      .map(|l| self.intern_file_key(l.key.clone(), FileOrigin::Lib))
      .collect();
    let lib_id_set: HashSet<FileId> = lib_ids.iter().copied().collect();
    self.process_libs(&libs, host);
    let mut root_ids: Vec<FileId> = roots
      .iter()
      .map(|key| self.intern_file_key(key.clone(), FileOrigin::Source))
      .collect();
    root_ids.sort_by_key(|id| id.0);
    let mut queue: VecDeque<FileId> = root_ids.iter().copied().collect();
    let mut seen: HashSet<FileId> = HashSet::new();
    while let Some(file) = queue.pop_front() {
      if cancelled.load(Ordering::Relaxed) {
        return Err(FatalError::Cancelled);
      }
      let prev_file = self.current_file;
      self.current_file = Some(file);
      if !seen.insert(file) {
        self.current_file = prev_file;
        continue;
      }
      if lib_id_set.contains(&file) {
        self.current_file = prev_file;
        continue;
      }
      let Some(file_key) = self.file_key_for_id(file) else {
        self.current_file = prev_file;
        continue;
      };
      self
        .file_kinds
        .entry(file)
        .or_insert_with(|| host.file_kind(&file_key));
      let file_kind = *self.file_kinds.get(&file).unwrap_or(&FileKind::Ts);
      let text = self.load_text(file, host)?;
      let parse_span = QuerySpan::enter(
        QueryKind::Parse,
        query_span!(
          "typecheck_ts.parse",
          Some(file.0),
          Option::<u32>::None,
          Option::<u32>::None,
          false
        ),
        None,
        false,
        Some(self.query_stats.clone()),
      );
      let parsed = parse_file(file, file_kind, &text);
      if let Some(span) = parse_span {
        span.finish(None);
      }
      match parsed {
        Ok(ast) => {
          let ast = Arc::new(ast);
          self.asts.insert(file, Arc::clone(&ast));
          let (lowered, lower_diags) = lower_hir_with_diagnostics(
            file,
            match file_kind {
              FileKind::Dts => HirFileKind::Dts,
              FileKind::Js => HirFileKind::Js,
              FileKind::Jsx => HirFileKind::Jsx,
              FileKind::Ts => HirFileKind::Ts,
              FileKind::Tsx => HirFileKind::Tsx,
            },
            &ast,
          );
          self.diagnostics.extend(lower_diags);
          self.hir_lowered.insert(file, lowered.clone());
          #[cfg(test)]
          if let Some(key) = self.file_key_for_id(file) {
            if key.as_str() == "m.ts" {
              let defs: Vec<_> = lowered
                .defs
                .iter()
                .map(|d| {
                  (
                    lowered
                      .names
                      .resolve(d.path.name)
                      .unwrap_or_default()
                      .to_string(),
                    d.path.kind,
                    d.is_exported,
                  )
                })
                .collect();
              eprintln!("lowered defs for m: {:?}", defs);
            }
          }
          let sem_hir = sem_hir_from_lower(ast.as_ref(), &lowered);
          self.sem_hir.insert(file, sem_hir);
          let lower_span = QuerySpan::enter(
            QueryKind::LowerHir,
            query_span!(
              "typecheck_ts.lower_hir",
              Some(file.0),
              Option::<u32>::None,
              Option::<u32>::None,
              false
            ),
            None,
            false,
            Some(self.query_stats.clone()),
          );
          self.bind_file(file, ast.as_ref(), host, &mut queue);
          self.align_definitions_with_hir(file, &lowered);
          self.map_hir_bodies(file, &lowered);
          if let Some(span) = lower_span {
            span.finish(None);
          }
        }
        Err(err) => {
          self.diagnostics.push(err);
        }
      }
      self.current_file = prev_file;
    }
    if !self.sem_hir.is_empty() {
      self.compute_semantics(host, &root_ids, &lib_ids);
    }
    self.resolve_reexports();
    self.rebuild_callable_overloads();
    self.recompute_global_bindings();
    codes::normalize_diagnostics(&mut self.diagnostics);
    self.analyzed = true;
    Ok(())
  }

  fn ensure_interned_types(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileKey],
    cancelled: &AtomicBool,
  ) -> Result<(), FatalError> {
    if self.interning {
      return Ok(());
    }
    self.interning = true;
    let result = (|| -> Result<(), FatalError> {
      self.ensure_analyzed_result(host, roots, cancelled)?;
      self.rebuild_callable_overloads();
      macro_rules! bail_if_cancelled {
        () => {
          if cancelled.load(Ordering::Relaxed) {
            return Err(FatalError::Cancelled);
          }
        };
      }
      let expected_enum_count: usize = self
        .hir_lowered
        .values()
        .map(|lowered| {
          lowered
            .defs
            .iter()
            .filter(|d| d.path.kind == HirDefKind::Enum)
            .count()
        })
        .sum();
      if self.interned_store.is_some()
        && self.interned_def_types.len() >= self.def_data.len()
        && self.enum_value_types.len() >= expected_enum_count
      {
        self.merge_callable_overload_types();
        return Ok(());
      }
      bail_if_cancelled!();

      let store = self.interned_store.clone().unwrap_or_else(|| {
        let store = tti::TypeStore::new();
        self.interned_store = Some(Arc::clone(&store));
        store
      });
      let prev_def_types = self.interned_def_types.clone();
      let prev_type_params = self.interned_type_params.clone();
      if std::env::var("TRACE_LITMUS").is_ok() {
        if let Some((map_id, ty)) = prev_def_types.iter().find(|(id, _)| {
          self
            .def_data
            .get(id)
            .map(|d| d.name.as_str() == "map")
            .unwrap_or(false)
        }) {
          eprintln!(
            "[ensure_interned_types] prev map def {:?} {}",
            map_id,
            tti::TypeDisplay::new(&store, *ty)
          );
        } else {
          eprintln!("[ensure_interned_types] prev map def missing");
        }
      }
      self.interned_def_types.clear();
      self.interned_type_params.clear();
      self.enum_value_types.clear();
      let mut def_types = HashMap::new();
      let mut type_params = HashMap::new();
      let mut namespace_types: HashMap<(FileId, String), (tti::TypeId, TypeId)> = HashMap::new();
      let def_by_name = self.canonical_defs();
      let mut binding_value_overrides: Vec<(FileId, String, tti::TypeId)> = Vec::new();

      enum EnumMemberInit {
        None,
        Number(f64),
        String(String),
        Other,
      }

      struct EnumMemberInfo {
        name: String,
        init: EnumMemberInit,
      }

      struct EnumDeclInfo {
        span: TextRange,
        name: String,
        members: Vec<EnumMemberInfo>,
      }

      fn collect_enums_in_namespace(
        file: FileId,
        ns: &NamespaceDecl,
        enums: &mut Vec<EnumDeclInfo>,
      ) {
        match &ns.body {
          NamespaceBody::Block(body) => collect_enums_in_stmts(file, body, enums),
          NamespaceBody::Namespace(inner) => {
            collect_enums_in_namespace(file, inner.stx.as_ref(), enums)
          }
        }
      }

      fn collect_enums_in_stmts(file: FileId, stmts: &[Node<Stmt>], enums: &mut Vec<EnumDeclInfo>) {
        for stmt in stmts {
          match stmt.stx.as_ref() {
            Stmt::EnumDecl(en) => {
              let mut members = Vec::new();
              for member in en.stx.members.iter() {
                let init = match member
                  .stx
                  .initializer
                  .as_ref()
                  .map(|init| init.stx.as_ref())
                {
                  Some(Expr::LitNum(num)) => EnumMemberInit::Number(num.stx.value.0),
                  Some(Expr::LitStr(str_lit)) => EnumMemberInit::String(str_lit.stx.value.clone()),
                  Some(_) => EnumMemberInit::Other,
                  None => EnumMemberInit::None,
                };
                members.push(EnumMemberInfo {
                  name: member.stx.name.clone(),
                  init,
                });
              }
              enums.push(EnumDeclInfo {
                span: loc_to_span(file, stmt.loc).range,
                name: en.stx.name.clone(),
                members,
              });
            }
            Stmt::Block(block) => collect_enums_in_stmts(file, &block.stx.body, enums),
            Stmt::NamespaceDecl(ns) => collect_enums_in_namespace(file, ns.stx.as_ref(), enums),
            Stmt::ModuleDecl(module) => {
              if let Some(body) = module.stx.body.as_ref() {
                collect_enums_in_stmts(file, body, enums);
              }
            }
            Stmt::GlobalDecl(global) => collect_enums_in_stmts(file, &global.stx.body, enums),
            _ => {}
          }
        }
      }

      let mut lowered_entries: Vec<_> = self
        .hir_lowered
        .iter()
        .map(|(file, lowered)| (*file, lowered.clone()))
        .collect();
      lowered_entries.sort_by_key(|(file, _)| file.0);
      for (file, lowered) in lowered_entries.clone().into_iter() {
        bail_if_cancelled!();
        let mut def_map: HashMap<DefId, DefId> = HashMap::new();
        let mut local_defs: HashMap<String, HirDefId> = HashMap::new();
        for def in lowered.defs.iter() {
          bail_if_cancelled!();
          if let Some(name) = lowered.names.resolve(def.name) {
            local_defs.insert(name.to_string(), def.id);
            if let Some(mapped) = def_by_name.get(&(file, name.to_string())) {
              def_map.insert(def.id, *mapped);
            }
          }
        }
        let file_key = self.file_key_for_id(file);
        let file_ids_map = self.file_keys.clone();
        let key_to_id = move |key: &FileKey| file_ids_map.get(key).copied();
        let mut annotated_defs = Vec::new();
        {
          let mut lowerer = check::decls::HirDeclLowerer::new(
            Arc::clone(&store),
            &lowered.types,
            self.semantics.as_ref(),
            def_by_name.clone(),
            file,
            file_key.clone(),
            local_defs,
            &mut self.diagnostics,
            Some(&def_map),
            Some(&def_by_name),
            Some(host.as_ref()),
            Some(&key_to_id),
            None,
          );
          for def in lowered.defs.iter() {
            bail_if_cancelled!();
            let Some(info) = def.type_info.as_ref() else {
              continue;
            };
            let (ty, params) = lowerer.lower_type_info(def.id, info, &lowered.names);
            let target_def = def_map.get(&def.id).copied().or_else(|| {
              lowered
                .names
                .resolve(def.name)
                .and_then(|n| def_by_name.get(&(file, n.to_string())).copied())
            });
            if let Some(mapped) = target_def {
              let ty = if let Some(existing) = def_types.get(&mapped) {
                ProgramState::merge_interned_decl_types(&store, *existing, ty)
              } else {
                ty
              };
              def_types.insert(mapped, ty);
              if !params.is_empty() {
                type_params.insert(mapped, params);
              }
              annotated_defs.push((mapped, ty));
            }
          }
        }
        for (def_id, ty) in annotated_defs {
          let store_ty = self.import_interned_type(ty);
          if let Some(def_data) = self.def_data.get_mut(&def_id) {
            if let DefKind::Var(var) = &mut def_data.kind {
              var.typ = Some(store_ty);
            }
          }
        }

        let mut enum_decls = Vec::new();
        if let Some(ast) = self.asts.get(&file) {
          collect_enums_in_stmts(file, &ast.stx.body, &mut enum_decls);
        }
        if !enum_decls.is_empty() {
          let hir_enums: Vec<_> = lowered
            .defs
            .iter()
            .filter(|d| d.path.kind == HirDefKind::Enum)
            .collect();
          let prim = store.primitive_ids();
          for en in enum_decls {
            bail_if_cancelled!();
            let matched = hir_enums
              .iter()
              .find(|d| d.span == en.span)
              .map(|d| d.id)
              .or_else(|| {
                hir_enums
                  .iter()
                  .find(|d| {
                    lowered
                      .names
                      .resolve(d.name)
                      .map(|n| n == en.name)
                      .unwrap_or(false)
                  })
                  .map(|d| d.id)
              })
              .or_else(|| def_by_name.get(&(file, en.name.clone())).copied());
            if let Some(def_id) = matched {
              let mut member_types: Vec<(String, tti::TypeId)> = Vec::new();
              let mut all_literals = true;
              let mut has_number = false;
              let mut has_string = false;
              let mut last_numeric: Option<f64> = None;
              for member in en.members {
                let mut member_ty = prim.number;
                let mut is_literal = false;
                let mut numeric_value: Option<f64> = None;
                match member.init {
                  EnumMemberInit::Number(value) => {
                    member_ty =
                      store.intern_type(tti::TypeKind::NumberLiteral(OrderedFloat(value)));
                    is_literal = true;
                    numeric_value = Some(value);
                  }
                  EnumMemberInit::String(value) => {
                    let name_id = store.intern_name(value);
                    member_ty = store.intern_type(tti::TypeKind::StringLiteral(name_id));
                    is_literal = true;
                    has_string = true;
                  }
                  EnumMemberInit::None => {
                    if let Some(prev) = last_numeric {
                      let value = prev + 1.0;
                      member_ty =
                        store.intern_type(tti::TypeKind::NumberLiteral(OrderedFloat(value)));
                      is_literal = true;
                      numeric_value = Some(value);
                    } else if member_types.is_empty() {
                      member_ty =
                        store.intern_type(tti::TypeKind::NumberLiteral(OrderedFloat(0.0)));
                      is_literal = true;
                      numeric_value = Some(0.0);
                    }
                  }
                  EnumMemberInit::Other => {}
                }
                let kind = store.type_kind(member_ty);
                has_number |= matches!(
                  kind,
                  tti::TypeKind::Number | tti::TypeKind::NumberLiteral(_)
                );
                has_string |= matches!(kind, tti::TypeKind::StringLiteral(_));
                if !is_literal {
                  all_literals = false;
                }
                last_numeric = numeric_value;
                member_types.push((member.name.clone(), store.canon(member_ty)));
              }

              let enum_type = if member_types.is_empty() {
                prim.number
              } else if all_literals {
                let mut types: Vec<_> = member_types.iter().map(|(_, ty)| *ty).collect();
                types.sort_by_key(|t| t.0);
                types.dedup();
                store.union(types)
              } else if has_string && has_number {
                store.union(vec![prim.string, prim.number])
              } else if has_string {
                prim.string
              } else {
                prim.number
              };
              let enum_type = store.canon(enum_type);
              def_types.insert(def_id, enum_type);
              let enum_store_ty = self.import_interned_type(enum_type);
              self.def_types.insert(def_id, enum_store_ty);

              let mut shape = tti::Shape::new();
              for (name, ty) in member_types.into_iter() {
                let key = PropKey::String(store.intern_name(name));
                let data = PropData {
                  ty,
                  optional: false,
                  readonly: true,
                  accessibility: None,
                  is_method: false,
                  origin: None,
                  declared_on: None,
                };
                if let Some(existing) = shape.properties.iter_mut().find(|p| p.key == key) {
                  existing.data = data;
                } else {
                  shape.properties.push(Property { key, data });
                }
              }
              let shape_id = store.intern_shape(shape);
              let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
              let value_ty = store.canon(store.intern_type(tti::TypeKind::Object(obj_id)));
              self.enum_value_types.insert(def_id, value_ty);
              binding_value_overrides.push((file, en.name.clone(), value_ty));
            }
          }
        }
      }

      let mut namespace_members: Vec<(FileId, String, Vec<String>)> = Vec::new();
      for (file, lowered) in lowered_entries.into_iter() {
        for ns_def in lowered
          .defs
          .iter()
          .filter(|d| matches!(d.path.kind, HirDefKind::Namespace | HirDefKind::Module))
        {
          let Some(ns_name) = lowered.names.resolve(ns_def.name) else {
            continue;
          };
          let mut members = Vec::new();
          for member in lowered.defs.iter() {
            bail_if_cancelled!();
            if member.id == ns_def.id {
              continue;
            }
            if member.span.start >= ns_def.span.start && member.span.end <= ns_def.span.end {
              if let Some(name) = lowered.names.resolve(member.name) {
                members.push(name.to_string());
              }
            }
          }
          members.sort();
          members.dedup();
          if members.is_empty() {
            continue;
          }
          namespace_members.push((file, ns_name.to_string(), members));
        }
      }
      namespace_members.sort_by(|a, b| (a.0 .0, &a.1).cmp(&(b.0 .0, &b.1)));
      for (file, ns_name, members) in namespace_members.into_iter() {
        bail_if_cancelled!();
        let key = (file, ns_name);
        namespace_types
          .entry(key)
          .and_modify(|(existing_interned, existing_store)| {
            *existing_interned =
              ProgramState::build_namespace_object_type(&store, Some(*existing_interned), &members);
            *existing_store =
              self.build_namespace_type_store_object(Some(*existing_store), &members);
          })
          .or_insert_with(|| {
            let interned = ProgramState::build_namespace_object_type(&store, None, &members);
            let store_ty = self.build_namespace_type_store_object(None, &members);
            (interned, store_ty)
          });
      }

      if !namespace_types.is_empty() {
        let mut ns_entries: Vec<_> = namespace_types.into_iter().collect();
        ns_entries.sort_by(|a, b| (a.0 .0, &a.0 .1).cmp(&(b.0 .0, &b.0 .1)));
        self.namespace_object_types = ns_entries.iter().cloned().collect();
        for ((file, name), (interned, store_ty)) in ns_entries.into_iter() {
          if let Some(def) = def_by_name.get(&(file, name)).copied() {
            self
              .interned_def_types
              .entry(def)
              .and_modify(|existing| {
                *existing = ProgramState::merge_interned_decl_types(&store, *existing, interned);
              })
              .or_insert(interned);
            self.def_types.entry(def).or_insert(store_ty);
          }
        }
      }

      let mut missing_defs: Vec<_> = self
        .def_data
        .keys()
        .copied()
        .filter(|def_id| {
          def_types.get(def_id).map_or(true, |ty| {
            matches!(store.type_kind(*ty), tti::TypeKind::Unknown)
          })
        })
        .collect();
      missing_defs.sort_by_key(|d| d.0);
      for def_id in missing_defs {
        bail_if_cancelled!();
        let store_ty = match self.def_types.get(&def_id).copied() {
          Some(ty) => ty,
          None => {
            let _ = self.type_of_def(def_id);
            self
              .def_types
              .get(&def_id)
              .copied()
              .unwrap_or(self.builtin.unknown)
          }
        };
        if let Some(existing) = self.interned_def_types.get(&def_id).copied() {
          def_types.insert(def_id, store.canon(existing));
          continue;
        }
        let mut cache = HashMap::new();
        let interned = convert_type_for_display(store_ty, self, &store, &mut cache);
        def_types.insert(def_id, store.canon(interned));
      }

      for (file, name, ty) in binding_value_overrides.into_iter() {
        if let Some(state) = self.files.get_mut(&file) {
          if let Some(binding) = state.bindings.get_mut(&name) {
            binding.type_id = Some(ty);
          }
        }
      }
      if std::env::var("TRACE_LITMUS").is_ok() {
        if let Some((map_id, ty)) = def_types.iter().find(|(id, _)| {
          self
            .def_data
            .get(id)
            .map(|d| d.name.as_str() == "map")
            .unwrap_or(false)
        }) {
          eprintln!(
            "[ensure_interned_types] map def {:?} before merge {}",
            map_id,
            tti::TypeDisplay::new(&store, *ty)
          );
        } else {
          eprintln!("[ensure_interned_types] map def missing before merge");
        }
      }
      let file_ids: Vec<_> = self.files.keys().copied().collect();
      for file in file_ids {
        bail_if_cancelled!();
        let binding_names: Vec<_> = self
          .files
          .get(&file)
          .map(|state| state.bindings.keys().cloned().collect())
          .unwrap_or_default();
        for name in binding_names {
          bail_if_cancelled!();
          let (def_id, has_type) = match self
            .files
            .get(&file)
            .and_then(|state| state.bindings.get(&name))
          {
            Some(binding) => (binding.def, binding.type_id),
            None => continue,
          };
          if has_type.is_some() {
            continue;
          }
          let Some(def_id) = def_id else { continue };
          let mut new_ty = None;
          if let Some(value_ty) = self.enum_value_types.get(&def_id).copied() {
            new_ty = Some(value_ty);
          } else if let Some(DefKind::Import(import)) = self.def_data.get(&def_id).map(|d| &d.kind)
          {
            if let Some(from) = import.from {
              if let Some(target) = def_by_name.get(&(from, import.original.clone())).copied() {
                if let Some(value_ty) = self.enum_value_types.get(&target).copied() {
                  new_ty = Some(value_ty);
                }
              }
            }
            if new_ty.is_none() {
              let import = import.clone();
              if let Some(entry) = self.resolve_import_entry(&import) {
                if let Some(target) = entry.def {
                  if let Some(value_ty) = self.enum_value_types.get(&target).copied() {
                    new_ty = Some(value_ty);
                  }
                }
              }
            }
          }
          if let Some(ty) = new_ty {
            if let Some(state) = self.files.get_mut(&file) {
              if let Some(binding) = state.bindings.get_mut(&name) {
                binding.type_id = Some(ty);
              }
            }
          }
        }
      }

      fn is_unknownish(store: &Arc<tti::TypeStore>, ty: tti::TypeId) -> bool {
        match store.type_kind(store.canon(ty)) {
          tti::TypeKind::Unknown | tti::TypeKind::Any => true,
          tti::TypeKind::Array { ty, .. } => is_unknownish(store, ty),
          tti::TypeKind::Tuple(elems) => elems.iter().all(|e| is_unknownish(store, e.ty)),
          tti::TypeKind::Union(members) => members.iter().all(|m| is_unknownish(store, *m)),
          tti::TypeKind::Intersection(members) => members.iter().all(|m| is_unknownish(store, *m)),
          tti::TypeKind::Callable { overloads } => overloads.iter().all(|sig_id| {
            let sig = store.signature(*sig_id);
            sig.params.iter().all(|p| is_unknownish(store, p.ty)) && is_unknownish(store, sig.ret)
          }),
          _ => false,
        }
      }

      let is_unknown =
        |ty: tti::TypeId| matches!(store.type_kind(store.canon(ty)), tti::TypeKind::Unknown);
      let is_trivial_callable = |ty: tti::TypeId| match store.type_kind(store.canon(ty)) {
        tti::TypeKind::Callable { overloads } if overloads.len() == 1 => {
          let sig = store.signature(overloads[0]);
          sig.params.iter().all(|p| is_unknownish(&store, p.ty)) && is_unknownish(&store, sig.ret)
        }
        _ => false,
      };
      for (def, ty) in prev_def_types.into_iter() {
        bail_if_cancelled!();
        if is_unknown(ty) {
          continue;
        }
        let should_replace = def_types
          .get(&def)
          .map(|existing| {
            if std::env::var("TRACE_LITMUS").is_ok()
              && self
                .def_data
                .get(&def)
                .map(|d| d.name.as_str() == "map")
                .unwrap_or(false)
            {
              let kind = store.type_kind(*existing).clone();
              let mut details = String::new();
              if let tti::TypeKind::Callable { overloads } = &kind {
                details = format!("overloads={}", overloads.len());
                if let Some(sig_id) = overloads.first() {
                  let sig = store.signature(*sig_id);
                  let params: Vec<_> = sig
                    .params
                    .iter()
                    .map(|p| is_unknownish(&store, p.ty))
                    .collect();
                  details.push_str(&format!(
                    " params_unknownish={:?} ret_unknownish={}",
                    params,
                    is_unknownish(&store, sig.ret)
                  ));
                }
              }
              eprintln!(
                "[ensure_interned_types] map existing {:?} unknown={} trivial={} {}",
                tti::TypeDisplay::new(&store, *existing),
                is_unknown(*existing),
                is_trivial_callable(*existing),
                details
              );
            }
            is_unknown(*existing) || is_trivial_callable(*existing)
          })
          .unwrap_or(true);
        if should_replace {
          def_types.insert(def, store.canon(ty));
          if let Some(params) = prev_type_params.get(&def).cloned() {
            type_params.entry(def).or_insert(params);
          }
        }
      }
      if std::env::var("TRACE_LITMUS").is_ok() {
        if let Some((map_id, ty)) = def_types.iter().find(|(id, _)| {
          self
            .def_data
            .get(id)
            .map(|d| d.name.as_str() == "map")
            .unwrap_or(false)
        }) {
          eprintln!(
            "[ensure_interned_types] map def {:?} after merge {}",
            map_id,
            tti::TypeDisplay::new(&store, *ty)
          );
        } else {
          eprintln!("[ensure_interned_types] map def missing after merge");
        }
      }

      self.interned_store = Some(store);
      self.interned_def_types = def_types;
      self.interned_type_params = type_params;
      self.merge_namespace_value_types();
      self.merge_callable_overload_types();
      let import_defs: Vec<_> = self
        .def_data
        .iter()
        .filter_map(|(id, data)| matches!(data.kind, DefKind::Import(_)).then_some(*id))
        .collect();
      for def in import_defs {
        let _ = self.type_of_def(def);
      }
      self.recompute_global_bindings();
      codes::normalize_diagnostics(&mut self.diagnostics);
      Ok(())
    })();
    self.interning = false;
    result
  }

  fn merge_interned_object_types(
    store: &Arc<tti::TypeStore>,
    existing: tti::TypeId,
    incoming: tti::TypeId,
  ) -> tti::TypeId {
    match (store.type_kind(existing), store.type_kind(incoming)) {
      (tti::TypeKind::Object(obj_a), tti::TypeKind::Object(obj_b)) => {
        let mut shape = store.shape(store.object(obj_a).shape);
        let other = store.shape(store.object(obj_b).shape);
        let mut merged = Vec::new();
        for prop in shape
          .properties
          .into_iter()
          .chain(other.properties.into_iter())
        {
          if let Some(existing) = merged
            .iter_mut()
            .find(|p: &&mut Property| p.key == prop.key)
          {
            *existing = prop;
          } else {
            merged.push(prop);
          }
        }
        shape.properties = merged;
        shape.call_signatures.extend(other.call_signatures);
        shape
          .construct_signatures
          .extend(other.construct_signatures);
        shape.indexers.extend(other.indexers);
        let shape_id = store.intern_shape(shape);
        let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
        store.intern_type(tti::TypeKind::Object(obj_id))
      }
      _ => store.intersection(vec![existing, incoming]),
    }
  }

  fn merge_interned_decl_types(
    store: &Arc<tti::TypeStore>,
    existing: tti::TypeId,
    incoming: tti::TypeId,
  ) -> tti::TypeId {
    match (store.type_kind(existing), store.type_kind(incoming)) {
      (tti::TypeKind::Object(_), tti::TypeKind::Object(_)) => {
        ProgramState::merge_interned_object_types(store, existing, incoming)
      }
      _ => store.intersection(vec![existing, incoming]),
    }
  }

  fn collect_libraries(&mut self, host: &dyn Host) -> Vec<LibFile> {
    let options = host.compiler_options();
    self.compiler_options = options.clone();
    self.checker_caches = CheckerCaches::new(options.cache.clone());
    self.cache_stats = CheckerCacheStats::default();
    let mut libs = host.lib_files();
    if !options.no_default_lib {
      let bundled = self.lib_manager.bundled_libs(&options);
      libs.extend(bundled.files);
    }

    let mut dts_libs = Vec::new();
    for lib in libs.into_iter() {
      let is_dts = lib.kind == FileKind::Dts || lib.name.ends_with(".d.ts");
      let file_id = self.intern_file_key(lib.key.clone(), FileOrigin::Lib);
      if !is_dts {
        self.diagnostics.push(codes::NON_DTS_LIB.warning(
          format!(
            "Library '{}' is not a .d.ts file; it will be ignored for global declarations.",
            lib.name
          ),
          Span::new(file_id, TextRange::new(0, 0)),
        ));
        continue;
      }
      self.file_kinds.insert(file_id, FileKind::Dts);
      dts_libs.push(lib);
    }

    if dts_libs.is_empty() {
      self
        .diagnostics
        .push(codes::NO_LIBS_LOADED.error(
          "No library files were loaded. Provide libs via the host or enable the bundled-libs feature / disable no_default_lib.",
          Span::new(FileId(u32::MAX), TextRange::new(0, 0)),
        ));
    }

    dts_libs
  }

  fn process_libs(&mut self, libs: &[LibFile], host: &Arc<dyn Host>) {
    for lib in libs {
      let file_id = self.intern_file_key(lib.key.clone(), FileOrigin::Lib);
      self.lib_texts.insert(file_id, lib.text.clone());
      let parsed = parse_file(file_id, FileKind::Dts, lib.text.as_ref());
      match parsed {
        Ok(ast) => {
          let ast = Arc::new(ast);
          self.asts.insert(file_id, Arc::clone(&ast));
          let (lowered, lower_diags) = lower_hir_with_diagnostics(file_id, HirFileKind::Dts, &ast);
          self.diagnostics.extend(lower_diags);
          if std::env::var("TRACE_AMBIENT").is_ok() {
            let defs: Vec<_> = lowered
              .defs
              .iter()
              .map(|d| {
                (
                  lowered
                    .names
                    .resolve(d.path.name)
                    .unwrap_or_default()
                    .to_string(),
                  d.path.kind,
                  d.is_ambient,
                  d.in_global,
                )
              })
              .collect();
            eprintln!("lib {:?} defs: {:?}", lib.name, defs);
          }
          let mut queue = VecDeque::new();
          self.bind_file(file_id, ast.as_ref(), host, &mut queue);
          let sem_hir = sem_hir_from_lower(ast.as_ref(), &lowered);
          self.hir_lowered.insert(file_id, lowered.clone());
          self.sem_hir.insert(file_id, sem_hir);
          self.align_definitions_with_hir(file_id, &lowered);
          self.map_hir_bodies(file_id, &lowered);
        }
        Err(err) => {
          self.diagnostics.push(err);
        }
      }
    }
  }

  fn load_text(&self, file: FileId, host: &Arc<dyn Host>) -> Result<Arc<str>, HostError> {
    if let Some(text) = self.lib_texts.get(&file) {
      return Ok(text.clone());
    }
    let Some(key) = self.file_key_for_id(file) else {
      return Err(HostError::new(format!("missing file key for {file:?}")));
    };
    host.file_text(&key)
  }

  fn recompute_global_bindings(&mut self) {
    let mut globals = HashMap::new();
    if let Some(semantics) = self.semantics.as_ref() {
      let symbols = semantics.symbols();
      for (name, group) in semantics.global_symbols() {
        if let Some(symbol) = group.symbol_for(sem_ts::Namespace::VALUE, symbols) {
          let public_symbol: semantic_js::SymbolId = symbol.into();
          let def = self.symbol_to_def.get(&public_symbol).copied();
          let type_id = def.and_then(|id| {
            self
              .enum_value_types
              .get(&id)
              .copied()
              .or_else(|| self.interned_def_types.get(&id).copied())
          });
          globals.insert(
            name.clone(),
            SymbolBinding {
              symbol: public_symbol,
              def,
              type_id,
            },
          );
        }
      }
    }
    for (file, state) in self.files.iter() {
      if self.file_kinds.get(file) != Some(&FileKind::Dts) {
        continue;
      }
      for (name, binding) in state.bindings.iter() {
        globals
          .entry(name.clone())
          .and_modify(|existing| {
            if existing.type_id.is_none() {
              existing.type_id = binding.type_id;
            }
            if existing.def.is_none() {
              existing.def = binding.def;
            }
          })
          .or_insert(binding.clone());
      }
    }
    globals
      .entry("undefined".to_string())
      .and_modify(|binding| {
        if binding.type_id.is_none() {
          binding.type_id = Some(self.builtin.undefined);
        }
      })
      .or_insert(SymbolBinding {
        symbol: self.alloc_symbol(),
        def: None,
        type_id: Some(self.builtin.undefined),
      });
    globals
      .entry("Error".to_string())
      .and_modify(|binding| {
        if binding.type_id.is_none() {
          binding.type_id = Some(self.builtin.any);
        }
      })
      .or_insert(SymbolBinding {
        symbol: self.alloc_symbol(),
        def: None,
        type_id: Some(self.builtin.any),
      });
    self.global_bindings = globals;
  }

  fn compute_semantics(&mut self, host: &Arc<dyn Host>, roots: &[FileId], libs: &[FileId]) {
    let resolver = HostResolver {
      host: Arc::clone(host),
      file_keys: self.file_ids.clone(),
      file_ids: self.file_keys.clone(),
    };
    let mut sem_roots: Vec<sem_ts::FileId> = roots
      .iter()
      .chain(libs.iter())
      .map(|f| sem_ts::FileId(f.0))
      .collect();
    sem_roots.sort();
    sem_roots.dedup();
    if std::env::var("TRACE_AMBIENT").is_ok() {
      for (file_id, hir) in self.sem_hir.iter() {
        if !hir.ambient_modules.is_empty() {
          let names: Vec<_> = hir.ambient_modules.iter().map(|m| m.name.clone()).collect();
          eprintln!("sem_hir ambient modules for {:?}: {:?}", file_id, names);
        }
      }
    }
    let (semantics, diags) = sem_ts::bind_ts_program(&sem_roots, &resolver, |file| {
      let id = FileId(file.0);
      self
        .sem_hir
        .get(&id)
        .cloned()
        .map(Arc::new)
        .unwrap_or_else(|| {
          let file_kind = if self.file_kinds.get(&id) == Some(&FileKind::Dts) {
            sem_ts::FileKind::Dts
          } else {
            sem_ts::FileKind::Ts
          };
          Arc::new(sem_ts::HirFile {
            file_id: file,
            module_kind: sem_ts::ModuleKind::Module,
            file_kind,
            decls: Vec::new(),
            imports: Vec::new(),
            import_equals: Vec::new(),
            exports: Vec::new(),
            export_as_namespace: Vec::new(),
            ambient_modules: Vec::new(),
          })
        })
    });
    self.push_semantic_diagnostics(diags);
    self.semantics = Some(semantics);
  }

  /// Remap bound definitions to the stable IDs produced by HIR lowering while
  /// preserving existing symbols and cached types.
  ///
  /// The binder allocates definitions sequentially, but HIR uses content-derived
  /// identifiers that stay stable across edits. Re-aligning keeps
  /// `definitions_in_file`, `expr_at`, and `type_of_def` working across repeated
  /// checks and avoids dropping cached type information when files are
  /// re-lowered.
  fn align_definitions_with_hir(&mut self, file: FileId, lowered: &LowerResult) {
    let file_def_ids: HashSet<_> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file == file)
      .map(|(id, _)| *id)
      .collect();
    let mut by_name_kind: HashMap<(String, DefMatchKind), Vec<(DefId, DefData)>> = HashMap::new();
    for (id, data) in self.def_data.iter() {
      if data.file != file {
        continue;
      }
      by_name_kind
        .entry((data.name.clone(), match_kind_from_def(&data.kind)))
        .or_default()
        .push((*id, data.clone()));
    }
    for defs in by_name_kind.values_mut() {
      defs.sort_by_key(|(_, data)| (data.span.start, data.span.end));
    }

    let mut new_def_data: HashMap<DefId, DefData> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file != file)
      .map(|(id, data)| (*id, data.clone()))
      .collect();
    let mut new_def_types: HashMap<DefId, TypeId> = self
      .def_types
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, ty)| (*id, *ty))
      .collect();
    let mut new_interned_def_types: HashMap<DefId, tti::TypeId> = self
      .interned_def_types
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, ty)| (*id, *ty))
      .collect();
    let mut new_interned_type_params: HashMap<DefId, Vec<TypeParamId>> = self
      .interned_type_params
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, params)| (*id, params.clone()))
      .collect();
    let mut id_mapping: HashMap<DefId, DefId> = HashMap::new();

    let Some(file_state) = self.files.get(&file).cloned() else {
      return;
    };
    #[cfg(test)]
    {
      let defs: Vec<_> = file_state
        .defs
        .iter()
        .filter_map(|d| self.def_data.get(d).map(|data| (d, data.name.clone())))
        .collect();
      eprintln!("align defs for file {:?}: {:?}", file, defs);
    }
    let mut resolved_defs = Vec::new();
    let mut bindings = file_state.bindings.clone();
    let mut exports = file_state.exports.clone();
    let reexports = file_state.reexports.clone();
    let export_all = file_state.export_all.clone();

    for def in lowered.defs.iter() {
      let name = lowered
        .names
        .resolve(def.name)
        .unwrap_or_default()
        .to_string();
      let match_kind = match_kind_from_hir(def.path.kind);
      let matched = by_name_kind
        .get_mut(&(name.clone(), match_kind))
        .and_then(|list| {
          if list.is_empty() {
            None
          } else {
            Some(list.remove(0))
          }
        });
      let (def_id, data) = if let Some((old_id, mut data)) = matched {
        id_mapping.insert(old_id, def.id);
        data.span = def.span;
        data.export = data.export || def.is_exported || def.is_default_export;
        match &mut data.kind {
          DefKind::Function(func) => func.body = def.body,
          DefKind::Var(var) => {
            if let Some(body) = def.body {
              var.body = body;
            }
          }
          _ => {}
        }
        if let Some(ty) = self.def_types.get(&old_id).copied() {
          new_def_types.insert(def.id, ty);
        }
        if let Some(ty) = self.interned_def_types.get(&old_id).copied() {
          new_interned_def_types.insert(def.id, ty);
        }
        if let Some(params) = self.interned_type_params.get(&old_id).cloned() {
          new_interned_type_params.insert(def.id, params);
        }
        (def.id, data)
      } else {
        let symbol = self.alloc_symbol();
        let kind = match match_kind {
          DefMatchKind::Function => DefKind::Function(FuncData {
            params: Vec::new(),
            return_ann: None,
            body: def.body,
          }),
          DefMatchKind::Interface => DefKind::Interface(InterfaceData {
            typ: self.builtin.unknown,
          }),
          DefMatchKind::TypeAlias => DefKind::TypeAlias(TypeAliasData {
            typ: self.builtin.unknown,
          }),
          _ => DefKind::Var(VarData {
            typ: None,
            init: None,
            body: def.body.unwrap_or(BodyId(u32::MAX)),
            annotated: false,
            mode: VarDeclMode::Var,
          }),
        };
        let data = DefData {
          name: name.clone(),
          file,
          span: def.span,
          symbol,
          export: def.is_exported || def.is_default_export,
          kind,
        };
        self.record_def_symbol(def.id, symbol);
        self.record_symbol(file, def.span, symbol);
        (def.id, data)
      };

      bindings
        .entry(name.clone())
        .and_modify(|binding| {
          binding.symbol = data.symbol;
          binding.def = Some(def_id);
        })
        .or_insert(SymbolBinding {
          symbol: data.symbol,
          def: Some(def_id),
          type_id: None,
        });

      if data.export {
        let export_name = if def.is_default_export {
          "default".to_string()
        } else {
          name.clone()
        };
        exports.insert(
          export_name,
          ExportEntry {
            symbol: data.symbol,
            def: Some(def_id),
            type_id: new_def_types.get(&def_id).copied(),
          },
        );
      }

      new_def_data.insert(def_id, data);
      resolved_defs.push(def_id);
    }

    for leftovers in by_name_kind.values_mut() {
      for (old_id, data) in leftovers.drain(..) {
        if data.file == file {
          eprintln!("retaining leftover def {} in file {:?}", data.name, file);
        }
        new_def_data.insert(old_id, data.clone());
        if let Some(ty) = self.def_types.get(&old_id).copied() {
          new_def_types.insert(old_id, ty);
        }
        if let Some(ty) = self.interned_def_types.get(&old_id).copied() {
          new_interned_def_types.insert(old_id, ty);
        }
        if let Some(params) = self.interned_type_params.get(&old_id).cloned() {
          new_interned_type_params.insert(old_id, params);
        }
        resolved_defs.push(old_id);
      }
    }

    for binding in bindings.values_mut() {
      if let Some(def) = binding.def {
        if let Some(mapped) = id_mapping.get(&def) {
          binding.def = Some(*mapped);
        }
      }
    }
    for entry in exports.values_mut() {
      if let Some(def) = entry.def {
        if let Some(mapped) = id_mapping.get(&def) {
          entry.def = Some(*mapped);
        }
      }
    }

    self.files.insert(
      file,
      FileState {
        defs: resolved_defs,
        exports,
        bindings,
        top_body: file_state.top_body,
        reexports,
        export_all,
      },
    );

    self.def_data = new_def_data;
    self.def_types = new_def_types;
    self.interned_def_types = new_interned_def_types;
    self.interned_type_params = new_interned_type_params;

    self.symbol_to_def.clear();
    for (def, data) in self.def_data.iter() {
      self.symbol_to_def.insert(data.symbol, *def);
    }
    self.next_def = self
      .def_data
      .keys()
      .map(|d| d.0)
      .max()
      .unwrap_or(0)
      .saturating_add(1);
  }

  fn map_hir_bodies(&mut self, file: FileId, lowered: &LowerResult) {
    let stale: HashSet<_> = self
      .body_map
      .iter()
      .filter(|(_, meta)| meta.file == file)
      .map(|(id, _)| *id)
      .collect();
    self.body_map.retain(|_, meta| meta.file != file);
    self.body_parents.retain(|child, _| !stale.contains(child));

    if let Some(state) = self.files.get_mut(&file) {
      state.top_body = Some(lowered.root_body());
    }

    let mut defs_by_span: HashMap<(TextRange, &'static str), DefId> = HashMap::new();
    let mut defs_by_name: HashMap<(String, &'static str), DefId> = HashMap::new();
    let mut file_defs: Vec<_> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file == file)
      .collect();
    file_defs.sort_by_key(|(id, data)| (data.span.start, data.span.end, id.0));
    for (def_id, data) in file_defs {
      let kind = match data.kind {
        DefKind::Function(_) => Some("fn"),
        DefKind::Var(_) => Some("var"),
        _ => None,
      };
      if let Some(kind) = kind {
        defs_by_span.entry((data.span, kind)).or_insert(*def_id);
        defs_by_name
          .entry((data.name.clone(), kind))
          .or_insert(*def_id);
      }
    }

    for (hir_body_id, idx) in lowered.body_index.iter() {
      let hir_body = lowered
        .bodies
        .get(*idx)
        .map(Arc::as_ref)
        .unwrap_or_else(|| panic!("missing lowered body for id {:?}", hir_body_id));

      for stmt in hir_body.stmts.iter() {
        if let hir_js::StmtKind::Var(decl) = &stmt.kind {
          for declarator in decl.declarators.iter() {
            let pat_span = hir_body.pats.get(declarator.pat.0 as usize).map(|p| p.span);
            let def_id = pat_span
              .and_then(|span| defs_by_span.get(&(span, "var")).copied())
              .or_else(|| {
                hir_body
                  .pats
                  .get(declarator.pat.0 as usize)
                  .and_then(|pat| match &pat.kind {
                    hir_js::PatKind::Ident(name_id) => lowered
                      .names
                      .resolve(*name_id)
                      .and_then(|name| defs_by_name.get(&(name.to_string(), "var")).copied()),
                    _ => None,
                  })
              });
            if let Some(def_id) = def_id {
              if let Some(def) = self.def_data.get_mut(&def_id) {
                if let DefKind::Var(var) = &mut def.kind {
                  var.mode = match decl.kind {
                    hir_js::VarDeclKind::Var => VarDeclMode::Var,
                    hir_js::VarDeclKind::Let => VarDeclMode::Let,
                    hir_js::VarDeclKind::Const => VarDeclMode::Const,
                  };
                  let prefer = matches!(hir_body.kind, HirBodyKind::Initializer);
                  if var.body.0 == u32::MAX || prefer {
                    var.body = *hir_body_id;
                  }
                  if let Some(init) = declarator.init {
                    if var.init.is_none() || prefer {
                      var.init = Some(init);
                    }
                  }
                }
              }
            }
          }
        }
      }

      for stmt in hir_body.stmts.iter() {
        if let hir_js::StmtKind::Decl(def) = &stmt.kind {
          if let Some(hir_def) = lowered.def(*def) {
            if let Some(child) = hir_def.body {
              self.body_parents.insert(child, *hir_body_id);
            }
          }
        }
      }

      for expr in hir_body.exprs.iter() {
        match &expr.kind {
          HirExprKind::FunctionExpr { body, .. } | HirExprKind::ClassExpr { body, .. } => {
            self.body_parents.insert(*body, *hir_body_id);
          }
          _ => {}
        }
      }

      self.body_map.insert(
        *hir_body_id,
        BodyMeta {
          file,
          hir: Some(*hir_body_id),
          kind: hir_body.kind,
        },
      );
    }

    for export in lowered.hir.exports.iter() {
      if let HirExportKind::Default(default) = &export.kind {
        match &default.value {
          hir_js::ExportDefaultValue::Expr { expr, body } => {
            if let Some((_def_id, def)) = self
              .def_data
              .iter_mut()
              .find(|(_, data)| data.file == file && data.name == "default")
            {
              if let DefKind::Var(var) = &mut def.kind {
                var.body = *body;
                var.init = Some(*expr);
                var.mode = VarDeclMode::Const;
              }
              self.body_parents.insert(*body, lowered.root_body());
            }
          }
          hir_js::ExportDefaultValue::Class { def, body, .. }
          | hir_js::ExportDefaultValue::Function { def, body, .. } => {
            if let Some(data) = self.def_data.get_mut(def) {
              if let DefKind::Function(func) = &mut data.kind {
                func.body = Some(*body);
              }
            }
            self.body_parents.insert(*body, lowered.root_body());
          }
        }
      }
    }

    self.next_body = self
      .body_map
      .keys()
      .map(|b| b.0)
      .max()
      .unwrap_or(0)
      .saturating_add(1);
  }

  fn ensure_body_map_from_defs(&mut self) {
    for (file, state) in self.files.iter() {
      if let Some(body) = state.top_body {
        self.body_map.entry(body).or_insert(BodyMeta {
          file: *file,
          hir: None,
          kind: HirBodyKind::Unknown,
        });
      }
    }
    for data in self.def_data.values() {
      let body = match &data.kind {
        DefKind::Function(func) => func.body,
        DefKind::Var(var) if var.body.0 != u32::MAX => Some(var.body),
        _ => None,
      };
      if let Some(body) = body {
        self.body_map.entry(body).or_insert(BodyMeta {
          file: data.file,
          hir: None,
          kind: HirBodyKind::Unknown,
        });
      }
    }
  }

  fn push_semantic_diagnostics(&mut self, diags: Vec<Diagnostic>) {
    for mut diag in diags {
      if diag.code == "BIND1002" {
        if diag.message.contains("unresolved") {
          diag.code = codes::UNRESOLVED_MODULE.as_str().into();
        } else {
          diag.code = codes::UNKNOWN_EXPORT.as_str().into();
        }
      }
      let duplicate = self.diagnostics.iter().any(|existing| {
        existing.code == diag.code
          && existing.primary == diag.primary
          && existing.message == diag.message
      });
      if duplicate {
        continue;
      }
      self.diagnostics.push(diag);
    }
  }

  fn resolve_reexports(&mut self) {
    let mut changed = true;
    let mut files: Vec<FileId> = self.files.keys().copied().collect();
    files.sort_by_key(|f| f.0);
    while changed {
      changed = false;
      for file in files.iter() {
        let Some(state) = self.files.get(file).cloned() else {
          continue;
        };
        let mut exports = state.exports.clone();
        for spec in state.reexports.iter() {
          let Some(target) = self.files.get(&spec.from) else {
            continue;
          };
          if let Some(entry) = target.exports.get(&spec.original) {
            if !spec.type_only {
              if let Some(def) = entry.def {
                if let Some(def_data) = self.def_data.get(&def) {
                  if matches!(def_data.kind, DefKind::TypeAlias(_) | DefKind::Interface(_)) {
                    let duplicate = self.diagnostics.iter().any(|existing| {
                      existing.code.as_str() == codes::UNKNOWN_EXPORT.as_str()
                        && existing.primary.file == *file
                        && existing.primary.range == spec.span
                    });
                    if !duplicate {
                      self.diagnostics.push(codes::UNKNOWN_EXPORT.error(
                        format!("unknown export {}", spec.original),
                        Span::new(*file, spec.span),
                      ));
                    }
                    continue;
                  }
                }
              }
            }
            let type_id = entry
              .type_id
              .or_else(|| entry.def.and_then(|d| self.def_types.get(&d).copied()));
            let mapped = ExportEntry {
              symbol: entry.symbol,
              def: None,
              type_id,
            };
            let mut update = true;
            if let Some(existing) = exports.get(&spec.alias) {
              if existing.symbol == mapped.symbol && existing.def == mapped.def {
                update = mapped.type_id.is_some()
                  && (existing.type_id.is_none() || existing.type_id != mapped.type_id);
              } else {
                update = false;
              }
            }
            if update {
              let previous = exports.insert(spec.alias.clone(), mapped.clone());
              if previous
                .as_ref()
                .map(|prev| {
                  prev.symbol != mapped.symbol
                    || prev.def != mapped.def
                    || prev.type_id != mapped.type_id
                })
                .unwrap_or(true)
              {
                changed = true;
              }
            }
            continue;
          }
          let duplicate = self.diagnostics.iter().any(|existing| {
            existing.code.as_str() == codes::UNKNOWN_EXPORT.as_str()
              && existing.primary.file == *file
              && existing.primary.range == spec.span
          });
          if !duplicate {
            self.diagnostics.push(codes::UNKNOWN_EXPORT.error(
              format!("unknown export {}", spec.original),
              Span::new(*file, spec.span),
            ));
          }
        }

        for spec in state.export_all.iter() {
          let Some(target) = self.files.get(&spec.from) else {
            continue;
          };
          for (name, entry) in target.exports.iter() {
            if name == "default" {
              continue;
            }
            let mut is_type = false;
            if let Some(def) = entry.def {
              if let Some(def_data) = self.def_data.get(&def) {
                is_type = matches!(def_data.kind, DefKind::TypeAlias(_) | DefKind::Interface(_));
                if !spec.type_only && is_type {
                  continue;
                }
              }
            }
            if spec.type_only && !is_type {
              continue;
            }
            let type_id = entry
              .type_id
              .or_else(|| entry.def.and_then(|d| self.def_types.get(&d).copied()));
            let mapped = ExportEntry {
              symbol: entry.symbol,
              def: None,
              type_id,
            };
            let mut update = true;
            if let Some(existing) = exports.get(name) {
              if existing.symbol == mapped.symbol && existing.def == mapped.def {
                update = mapped.type_id.is_some()
                  && (existing.type_id.is_none() || existing.type_id != mapped.type_id);
              } else {
                update = false;
              }
            }
            if update {
              let previous = exports.insert(name.clone(), mapped.clone());
              if previous
                .as_ref()
                .map(|prev| {
                  prev.symbol != mapped.symbol
                    || prev.def != mapped.def
                    || prev.type_id != mapped.type_id
                })
                .unwrap_or(true)
              {
                changed = true;
              }
            }
          }
        }

        if let Some(existing) = self.files.get_mut(file) {
          existing.exports = exports;
        }
      }
    }
  }

  fn update_export_types(&mut self) {
    let mut updates: Vec<(FileId, String, DefId)> = Vec::new();
    for (file_id, state) in self.files.iter() {
      for (name, entry) in state.exports.iter() {
        if let Some(def) = entry.def {
          updates.push((*file_id, name.clone(), def));
        }
      }
    }
    for (file_id, name, def) in updates.into_iter() {
      if let Some(ty) = self.export_type_for_def(def) {
        if let Some(state) = self.files.get_mut(&file_id) {
          if let Some(entry) = state.exports.get_mut(&name) {
            entry.type_id = Some(ty);
          }
        }
      }
    }
  }

  fn export_type_for_def(&mut self, def: DefId) -> Option<TypeId> {
    if let Some(store) = self.interned_store.clone() {
      let mut cache = HashMap::new();
      if let Some(merged) = self.callable_overload_type_for_def(def, &store, &mut cache) {
        return Some(merged);
      }
    }
    if self.interned_store.is_some() && !self.def_types.contains_key(&def) {
      let _ = self.type_of_def(def);
    }
    if let Some(ty) = self.interned_def_types.get(&def).copied() {
      return Some(ty);
    }
    let Some(store_ty) = self.def_types.get(&def).copied() else {
      return None;
    };
    if let Some(store) = self.interned_store.as_ref() {
      let mut cache = HashMap::new();
      let interned = convert_type_for_display(store_ty, self, store, &mut cache);
      let interned = store.canon(interned);
      self.interned_def_types.insert(def, interned);
      Some(interned)
    } else {
      Some(store_ty)
    }
  }

  fn queue_type_imports_in_type_parameters(
    &mut self,
    file: FileId,
    params: &[Node<TypeParameter>],
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    for tp in params.iter() {
      if let Some(constraint) = tp.stx.constraint.as_ref() {
        self.queue_type_imports_in_type_expr(file, constraint, host, queue);
      }
      if let Some(default) = tp.stx.default.as_ref() {
        self.queue_type_imports_in_type_expr(file, default, host, queue);
      }
    }
  }

  fn queue_type_imports_in_func(
    &mut self,
    file: FileId,
    func: &Func,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    if let Some(params) = func.type_parameters.as_ref() {
      self.queue_type_imports_in_type_parameters(file, params, host, queue);
    }
    for param in func.parameters.iter() {
      if let Some(ann) = param.stx.type_annotation.as_ref() {
        self.queue_type_imports_in_type_expr(file, ann, host, queue);
      }
    }
    if let Some(ret) = func.return_type.as_ref() {
      self.queue_type_imports_in_type_expr(file, ret, host, queue);
    }
  }

  fn queue_type_imports_in_class_member(
    &mut self,
    file: FileId,
    member: &Node<ClassMember>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    if let Some(ann) = member.stx.type_annotation.as_ref() {
      self.queue_type_imports_in_type_expr(file, ann, host, queue);
    }
    match &member.stx.val {
      ClassOrObjVal::Method(method) => {
        self.queue_type_imports_in_func(file, &method.stx.func.stx, host, queue);
      }
      ClassOrObjVal::Getter(getter) => {
        self.queue_type_imports_in_func(file, &getter.stx.func.stx, host, queue);
      }
      ClassOrObjVal::Setter(setter) => {
        self.queue_type_imports_in_func(file, &setter.stx.func.stx, host, queue);
      }
      ClassOrObjVal::IndexSignature(idx) => {
        self.queue_type_imports_in_type_expr(file, &idx.stx.parameter_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &idx.stx.type_annotation, host, queue);
      }
      _ => {}
    }
  }

  fn queue_type_imports_in_type_members(
    &mut self,
    file: FileId,
    members: &[Node<TypeMember>],
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    for member in members.iter() {
      match member.stx.as_ref() {
        TypeMember::Property(prop) => {
          if let Some(ann) = prop.stx.type_annotation.as_ref() {
            self.queue_type_imports_in_type_expr(file, ann, host, queue);
          }
        }
        TypeMember::Method(method) => {
          for param in method.stx.parameters.iter() {
            self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
          }
          if let Some(ret) = method.stx.return_type.as_ref() {
            self.queue_type_imports_in_type_expr(file, ret, host, queue);
          }
          if let Some(params) = method.stx.type_parameters.as_ref() {
            self.queue_type_imports_in_type_parameters(file, params, host, queue);
          }
        }
        TypeMember::Constructor(cons) => {
          for param in cons.stx.parameters.iter() {
            self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
          }
          if let Some(ret) = cons.stx.return_type.as_ref() {
            self.queue_type_imports_in_type_expr(file, ret, host, queue);
          }
          if let Some(params) = cons.stx.type_parameters.as_ref() {
            self.queue_type_imports_in_type_parameters(file, params, host, queue);
          }
        }
        TypeMember::CallSignature(call) => {
          for param in call.stx.parameters.iter() {
            self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
          }
          if let Some(ret) = call.stx.return_type.as_ref() {
            self.queue_type_imports_in_type_expr(file, ret, host, queue);
          }
          if let Some(params) = call.stx.type_parameters.as_ref() {
            self.queue_type_imports_in_type_parameters(file, params, host, queue);
          }
        }
        TypeMember::IndexSignature(idx) => {
          self.queue_type_imports_in_type_expr(file, &idx.stx.parameter_type, host, queue);
          self.queue_type_imports_in_type_expr(file, &idx.stx.type_annotation, host, queue);
        }
        _ => {}
      }
    }
  }

  fn queue_type_imports_in_stmt(
    &mut self,
    file: FileId,
    stmt: &Node<Stmt>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    match stmt.stx.as_ref() {
      Stmt::ClassDecl(class) => {
        if let Some(params) = class.stx.type_parameters.as_ref() {
          self.queue_type_imports_in_type_parameters(file, params, host, queue);
        }
        for member in class.stx.members.iter() {
          self.queue_type_imports_in_class_member(file, member, host, queue);
        }
      }
      Stmt::TypeAliasDecl(alias) => {
        self.queue_type_imports_in_type_expr(file, &alias.stx.type_expr, host, queue);
      }
      Stmt::FunctionDecl(func) => {
        self.queue_type_imports_in_func(file, &func.stx.function.stx, host, queue);
        if let Some(body) = func.stx.function.stx.body.as_ref() {
          if let parse_js::ast::func::FuncBody::Block(block) = body {
            for stmt in block.iter() {
              self.queue_type_imports_in_stmt(file, stmt, host, queue);
            }
          }
        }
      }
      Stmt::VarDecl(var) => {
        for decl in var.stx.declarators.iter() {
          if let Some(ann) = decl.type_annotation.as_ref() {
            self.queue_type_imports_in_type_expr(file, ann, host, queue);
          }
        }
      }
      Stmt::Block(block) => {
        for stmt in block.stx.body.iter() {
          self.queue_type_imports_in_stmt(file, stmt, host, queue);
        }
      }
      Stmt::AmbientClassDecl(ambient) => {
        if let Some(params) = ambient.stx.type_parameters.as_ref() {
          self.queue_type_imports_in_type_parameters(file, params, host, queue);
        }
        if let Some(base) = ambient.stx.extends.as_ref() {
          self.queue_type_imports_in_type_expr(file, base, host, queue);
        }
        for implemented in ambient.stx.implements.iter() {
          self.queue_type_imports_in_type_expr(file, implemented, host, queue);
        }
        self.queue_type_imports_in_type_members(file, &ambient.stx.members, host, queue);
      }
      Stmt::NamespaceDecl(ns) => {
        self.queue_type_imports_in_namespace_body(file, &ns.stx.body, host, queue);
      }
      Stmt::ModuleDecl(module) => {
        if let Some(body) = &module.stx.body {
          for stmt in body.iter() {
            self.queue_type_imports_in_stmt(file, stmt, host, queue);
          }
        }
      }
      Stmt::GlobalDecl(global) => {
        for stmt in global.stx.body.iter() {
          self.queue_type_imports_in_stmt(file, stmt, host, queue);
        }
      }
      _ => {}
    }
  }

  fn queue_type_imports_in_namespace_body(
    &mut self,
    file: FileId,
    body: &NamespaceBody,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    match body {
      NamespaceBody::Block(stmts) => {
        for stmt in stmts.iter() {
          self.queue_type_imports_in_stmt(file, stmt, host, queue);
        }
      }
      NamespaceBody::Namespace(inner) => {
        self.queue_type_imports_in_namespace_body(file, &inner.stx.body, host, queue)
      }
    }
  }

  fn queue_type_imports_in_type_expr(
    &mut self,
    file: FileId,
    expr: &Node<TypeExpr>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    match expr.stx.as_ref() {
      TypeExpr::ImportType(import) => {
        if let Some(file_key) = self.file_key_for_id(file) {
          if let Some(target_key) = host.resolve(&file_key, &import.stx.module_specifier) {
            let target = self.intern_file_key(target_key, FileOrigin::Source);
            queue.push_back(target);
          }
        }
        if let Some(args) = import.stx.type_arguments.as_ref() {
          for arg in args {
            self.queue_type_imports_in_type_expr(file, arg, host, queue);
          }
        }
        if let Some(qualifier) = import.stx.qualifier.as_ref() {
          self.queue_type_imports_in_entity_name(file, qualifier, host, queue);
        }
      }
      TypeExpr::ArrayType(arr) => {
        self.queue_type_imports_in_type_expr(file, &arr.stx.element_type, host, queue);
      }
      TypeExpr::TupleType(tuple) => {
        for elem in tuple.stx.elements.iter() {
          self.queue_type_imports_in_type_expr(file, &elem.stx.type_expr, host, queue);
        }
      }
      TypeExpr::UnionType(union) => {
        for ty in union.stx.types.iter() {
          self.queue_type_imports_in_type_expr(file, ty, host, queue);
        }
      }
      TypeExpr::IntersectionType(intersection) => {
        for ty in intersection.stx.types.iter() {
          self.queue_type_imports_in_type_expr(file, ty, host, queue);
        }
      }
      TypeExpr::FunctionType(func) => {
        for param in func.stx.parameters.iter() {
          self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
        }
        self.queue_type_imports_in_type_expr(file, &func.stx.return_type, host, queue);
        if let Some(params) = func.stx.type_parameters.as_ref() {
          self.queue_type_imports_in_type_parameters(file, params, host, queue);
        }
      }
      TypeExpr::ConstructorType(cons) => {
        for param in cons.stx.parameters.iter() {
          self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
        }
        self.queue_type_imports_in_type_expr(file, &cons.stx.return_type, host, queue);
        if let Some(params) = cons.stx.type_parameters.as_ref() {
          self.queue_type_imports_in_type_parameters(file, params, host, queue);
        }
      }
      TypeExpr::ObjectType(obj) => {
        self.queue_type_imports_in_type_members(file, &obj.stx.members, host, queue);
      }
      TypeExpr::ParenthesizedType(inner) => {
        self.queue_type_imports_in_type_expr(file, &inner.stx.type_expr, host, queue);
      }
      TypeExpr::KeyOfType(keyof) => {
        self.queue_type_imports_in_type_expr(file, &keyof.stx.type_expr, host, queue);
      }
      TypeExpr::IndexedAccessType(indexed) => {
        self.queue_type_imports_in_type_expr(file, &indexed.stx.object_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &indexed.stx.index_type, host, queue);
      }
      TypeExpr::ConditionalType(cond) => {
        self.queue_type_imports_in_type_expr(file, &cond.stx.check_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &cond.stx.extends_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &cond.stx.true_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &cond.stx.false_type, host, queue);
      }
      TypeExpr::MappedType(mapped) => {
        self.queue_type_imports_in_type_expr(file, &mapped.stx.constraint, host, queue);
        self.queue_type_imports_in_type_expr(file, &mapped.stx.type_expr, host, queue);
        if let Some(name_type) = mapped.stx.name_type.as_ref() {
          self.queue_type_imports_in_type_expr(file, name_type, host, queue);
        }
      }
      TypeExpr::TemplateLiteralType(tpl) => {
        for span in tpl.stx.spans.iter() {
          self.queue_type_imports_in_type_expr(file, &span.stx.type_expr, host, queue);
        }
      }
      TypeExpr::TypePredicate(pred) => {
        if let Some(ann) = pred.stx.type_annotation.as_ref() {
          self.queue_type_imports_in_type_expr(file, ann, host, queue);
        }
      }
      TypeExpr::InferType(infer) => {
        if let Some(constraint) = infer.stx.constraint.as_ref() {
          self.queue_type_imports_in_type_expr(file, constraint, host, queue);
        }
      }
      TypeExpr::TypeReference(reference) => {
        if let Some(args) = reference.stx.type_arguments.as_ref() {
          for arg in args {
            self.queue_type_imports_in_type_expr(file, arg, host, queue);
          }
        }
      }
      TypeExpr::TypeQuery(query) => {
        self.queue_type_imports_in_entity_name(file, &query.stx.expr_name, host, queue);
      }
      _ => {}
    }
  }

  fn queue_type_imports_in_entity_name(
    &mut self,
    file: FileId,
    name: &TypeEntityName,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    match name {
      TypeEntityName::Qualified(qualified) => {
        self.queue_type_imports_in_entity_name(file, &qualified.left, host, queue);
      }
      TypeEntityName::Import(_) => {}
      _ => {}
    }
  }

  fn bind_file(
    &mut self,
    file: FileId,
    ast: &Node<TopLevel>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    let file_kind = *self.file_kinds.get(&file).unwrap_or(&FileKind::Ts);
    let mut sem_builder = SemHirBuilder::new(file, sem_file_kind(file_kind));
    let mut defs = Vec::new();
    let mut exports: ExportMap = BTreeMap::new();
    let mut bindings: HashMap<String, SymbolBinding> = HashMap::new();
    let mut reexports = Vec::new();
    let mut export_all = Vec::new();

    for stmt in ast.stx.body.iter() {
      self.queue_type_imports_in_stmt(file, stmt, host, queue);
      match stmt.stx.as_ref() {
        Stmt::VarDecl(var) => {
          let new_defs = self.handle_var_decl(file, var.stx.as_ref(), &mut sem_builder);
          for (def_id, binding, export_name) in new_defs {
            defs.push(def_id);
            let (binding_name, binding_value) = binding;
            bindings.insert(binding_name.clone(), binding_value.clone());
            if let Some(name) = export_name {
              exports.insert(
                name,
                ExportEntry {
                  symbol: binding_value.symbol,
                  def: Some(def_id),
                  type_id: binding_value.type_id,
                },
              );
            }
          }
        }
        Stmt::FunctionDecl(func) => {
          let span = loc_to_span(file, stmt.loc);
          if let Some((def_id, binding, export_name)) =
            self.handle_function_decl(file, span.range, func.stx.as_ref(), &mut sem_builder)
          {
            defs.push(def_id);
            let (binding_name, binding_value) = binding;
            bindings.insert(binding_name.clone(), binding_value.clone());
            if let Some(name) = export_name {
              exports.insert(
                name,
                ExportEntry {
                  symbol: binding_value.symbol,
                  def: Some(def_id),
                  type_id: binding_value.type_id,
                },
              );
            }
          }
        }
        Stmt::ClassDecl(class_decl) => {
          if let Some(name_node) = class_decl.stx.name.as_ref() {
            let name = name_node.stx.name.clone();
            let span = loc_to_span(file, stmt.loc);
            let symbol = self.alloc_symbol();
            let def_id = self.alloc_def();

            let mut obj = ObjectType::empty();
            for member in class_decl.stx.members.iter() {
              let member = member.stx.as_ref();
              if !member.static_ {
                continue;
              }
              let key = match &member.key {
                parse_js::ast::class_or_object::ClassOrObjKey::Direct(key) => {
                  Some(key.stx.key.clone())
                }
                _ => None,
              };
              let prop_ty = match &member.val {
                ClassOrObjVal::Method(_) => self.builtin.unknown,
                ClassOrObjVal::Prop(_) => member
                  .type_annotation
                  .as_ref()
                  .map(|ann| self.type_from_type_expr(ann))
                  .unwrap_or(self.builtin.unknown),
                _ => continue,
              };
              if let Some(name) = key {
                obj.props.insert(
                  name,
                  ObjectProperty {
                    typ: prop_ty,
                    optional: member.optional,
                    readonly: member.readonly,
                  },
                );
              }
            }

            let typ = self.type_store.object(obj);
            self.def_data.insert(
              def_id,
              DefData {
                name: name.clone(),
                file,
                span: span.range,
                symbol,
                export: class_decl.stx.export || class_decl.stx.export_default,
                kind: DefKind::Var(VarData {
                  typ: Some(typ),
                  init: None,
                  body: BodyId(u32::MAX),
                  annotated: true,
                  mode: VarDeclMode::Var,
                }),
              },
            );
            self.def_types.insert(def_id, typ);
            self.record_def_symbol(def_id, symbol);
            self.record_symbol(file, loc_to_span(file, name_node.loc).range, symbol);
            defs.push(def_id);
            bindings.insert(
              name.clone(),
              SymbolBinding {
                symbol,
                def: Some(def_id),
                type_id: Some(typ),
              },
            );
            if class_decl.stx.export || class_decl.stx.export_default {
              let export_name = if class_decl.stx.export_default {
                "default".to_string()
              } else {
                name.clone()
              };
              exports.insert(
                export_name,
                ExportEntry {
                  symbol,
                  def: Some(def_id),
                  type_id: Some(typ),
                },
              );
            }
            sem_builder.add_decl(
              def_id,
              name,
              sem_ts::DeclKind::Class,
              if class_decl.stx.export_default {
                sem_ts::Exported::Default
              } else if class_decl.stx.export {
                sem_ts::Exported::Named
              } else {
                sem_ts::Exported::No
              },
              span.range,
            );
          }
        }
        Stmt::InterfaceDecl(interface) => {
          let span = loc_to_span(file, stmt.loc);
          let name = interface.stx.name.clone();
          let mut object = self.object_type_from_members(&interface.stx.members);
          for base in interface.stx.extends.iter() {
            let base_ty = self.type_from_type_expr(base);
            if let TypeKind::Object(base_obj) = self.type_store.kind(base_ty).clone() {
              object = self.merge_object_types(object, base_obj);
            }
          }
          let mut typ = self.type_store.object(object);
          let existing_interface = bindings
            .get(&name)
            .and_then(|b| b.def)
            .and_then(|id| self.def_data.get(&id).map(|d| (id, d.clone())))
            .and_then(|(id, data)| match data.kind {
              DefKind::Interface(existing) => Some((id, data.symbol, existing.typ)),
              _ => None,
            });
          let (def_id, symbol) =
            if let Some((existing_id, symbol, existing_ty)) = existing_interface {
              typ = match (
                self.type_store.kind(existing_ty).clone(),
                self.type_store.kind(typ).clone(),
              ) {
                (TypeKind::Object(existing_obj), TypeKind::Object(obj)) => {
                  let merged = self.merge_object_types(existing_obj, obj);
                  self.type_store.object(merged)
                }
                _ => self.type_store.union(vec![existing_ty, typ], &self.builtin),
              };
              if let Some(def) = self.def_data.get_mut(&existing_id) {
                def.kind = DefKind::Interface(InterfaceData { typ });
                def.export = def.export || interface.stx.export;
              }
              (existing_id, symbol)
            } else {
              let symbol = self.alloc_symbol();
              let def_id = self.alloc_def();
              self.def_data.insert(
                def_id,
                DefData {
                  name: name.clone(),
                  file,
                  span: span.range,
                  symbol,
                  export: interface.stx.export,
                  kind: DefKind::Interface(InterfaceData { typ }),
                },
              );
              self.record_def_symbol(def_id, symbol);
              defs.push(def_id);
              sem_builder.add_decl(
                def_id,
                name.clone(),
                sem_ts::DeclKind::Interface,
                if interface.stx.export {
                  sem_ts::Exported::Named
                } else {
                  sem_ts::Exported::No
                },
                span.range,
              );
              (def_id, symbol)
            };

          bindings
            .entry(name.clone())
            .and_modify(|binding| {
              binding.symbol = symbol;
              binding.def = Some(def_id);
              binding.type_id = Some(typ);
            })
            .or_insert(SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: Some(typ),
            });

          if interface.stx.export {
            let entry = exports.entry(name.clone()).or_insert(ExportEntry {
              symbol,
              def: Some(def_id),
              type_id: Some(typ),
            });
            entry.symbol = symbol;
            entry.def = Some(def_id);
            entry.type_id = Some(typ);
          }

          self.def_types.insert(def_id, typ);
          self.record_symbol(file, span.range, symbol);
        }
        Stmt::TypeAliasDecl(alias) => {
          let span = loc_to_span(file, stmt.loc);
          let name = alias.stx.name.clone();
          let mut ty = self.type_from_type_expr(&alias.stx.type_expr);
          if ty == self.builtin.unknown {
            ty = self.type_store.literal_string(name.clone());
          }
          if let TypeExpr::TypeReference(reference) = alias.stx.type_expr.stx.as_ref() {
            if let TypeEntityName::Identifier(type_name) = &reference.stx.name {
              if let Some(binding) = bindings.get(type_name) {
                self.record_symbol(
                  file,
                  loc_to_span(file, alias.stx.type_expr.loc).range,
                  binding.symbol,
                );
              }
            }
          }
          let def_id = self.alloc_def();
          let symbol = self.alloc_symbol();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: alias.stx.export,
              kind: DefKind::TypeAlias(TypeAliasData { typ: ty }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          self.def_types.insert(def_id, ty);
          bindings.insert(
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: Some(ty),
            },
          );
          defs.push(def_id);
          self.record_symbol(file, span.range, symbol);
          sem_builder.add_decl(
            def_id,
            name.clone(),
            sem_ts::DeclKind::TypeAlias,
            if alias.stx.export {
              sem_ts::Exported::Named
            } else {
              sem_ts::Exported::No
            },
            span.range,
          );
          if alias.stx.export {
            exports.insert(
              name.clone(),
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: Some(ty),
              },
            );
          }
        }
        Stmt::NamespaceDecl(ns) => {
          let span = loc_to_span(file, stmt.loc);
          let name = ns.stx.name.clone();
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: ns.stx.export,
              kind: DefKind::Var(VarData {
                typ: None,
                init: None,
                body: BodyId(u32::MAX),
                annotated: false,
                mode: VarDeclMode::Var,
              }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          self.record_symbol(file, span.range, symbol);
          defs.push(def_id);
          sem_builder.add_decl(
            def_id,
            name.clone(),
            sem_ts::DeclKind::Namespace,
            if ns.stx.export {
              sem_ts::Exported::Named
            } else {
              sem_ts::Exported::No
            },
            span.range,
          );
          bindings.insert(
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
          if ns.stx.export {
            exports.insert(
              name.clone(),
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
          }
          self.bind_namespace_body_defs(file, &ns.stx.body, &mut defs);
        }
        Stmt::ModuleDecl(module) => {
          let span = loc_to_span(file, stmt.loc);
          let name = match &module.stx.name {
            parse_js::ast::ts_stmt::ModuleName::Identifier(id) => id.clone(),
            parse_js::ast::ts_stmt::ModuleName::String(s) => s.clone(),
          };
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: module.stx.export,
              kind: DefKind::Var(VarData {
                typ: None,
                init: None,
                body: BodyId(u32::MAX),
                annotated: false,
                mode: VarDeclMode::Var,
              }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          self.record_symbol(file, span.range, symbol);
          defs.push(def_id);
          bindings.insert(
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
          if module.stx.export {
            exports.insert(
              name.clone(),
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
          }
          if let Some(body) = module.stx.body.as_ref() {
            self.bind_namespace_stmts(file, body, &mut defs);
          }
        }
        Stmt::ExportDefaultExpr(node) => {
          let span = loc_to_span(file, node.loc);
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: "default".to_string(),
              file,
              span: span.range,
              symbol,
              export: true,
              kind: DefKind::Var(VarData {
                typ: None,
                init: None,
                body: BodyId(u32::MAX),
                annotated: false,
                mode: VarDeclMode::Const,
              }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          defs.push(def_id);
          sem_builder.add_decl(
            def_id,
            "default".to_string(),
            sem_ts::DeclKind::Var,
            sem_ts::Exported::Default,
            span.range,
          );
          bindings.insert(
            "default".to_string(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
          exports.insert(
            "default".to_string(),
            ExportEntry {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
        }
        Stmt::ExportList(export_list) => {
          let resolved = export_list.stx.from.as_ref().and_then(|module| {
            self
              .file_key_for_id(file)
              .and_then(|file_key| host.resolve(&file_key, module))
              .map(|target| self.intern_file_key(target, FileOrigin::Source))
          });
          if let Some(target) = resolved {
            queue.push_back(target);
          }
          match &export_list.stx.names {
            ExportNames::Specific(names) => {
              for name in names {
                let exportable = name.stx.exportable.as_str().to_string();
                let alias = name.stx.alias.stx.name.clone();
                let exported_as = if alias == exportable {
                  None
                } else {
                  Some(alias.clone())
                };
                let is_type_only = export_list.stx.type_only || name.stx.type_only;
                sem_builder.add_named_export(
                  export_list.stx.from.clone(),
                  export_list
                    .stx
                    .from
                    .as_ref()
                    .map(|_| loc_to_span(file, stmt.loc).range),
                  vec![sem_ts::ExportSpecifier {
                    local: exportable.clone(),
                    exported: exported_as.clone(),
                    local_span: loc_to_span(file, name.loc).range,
                    exported_span: exported_as
                      .as_ref()
                      .map(|_| loc_to_span(file, name.stx.alias.loc).range),
                  }],
                  is_type_only,
                );

                if let Some(target) = resolved {
                  reexports.push(Reexport {
                    from: target,
                    original: exportable.clone(),
                    alias: alias.clone(),
                    type_only: is_type_only,
                    span: loc_to_span(file, name.loc).range,
                  });
                }

                if export_list.stx.from.is_none() && !is_type_only {
                  let mapped = bindings.get(&exportable);
                  if let Some(binding) = mapped {
                    exports.insert(
                      alias.clone(),
                      ExportEntry {
                        symbol: binding.symbol,
                        def: binding.def,
                        type_id: binding.type_id,
                      },
                    );
                  } else {
                    self.diagnostics.push(codes::UNKNOWN_EXPORT.error(
                      format!("unknown export {exportable}"),
                      loc_to_span(file, name.loc),
                    ));
                  }
                }
              }
            }
            ExportNames::All(alias) => {
              if alias.is_some() {
                self.diagnostics.push(
                  codes::UNSUPPORTED_PATTERN
                    .error("unsupported export * as alias", loc_to_span(file, stmt.loc)),
                );
              } else if let Some(spec) = export_list.stx.from.clone() {
                if let Some(target) = resolved {
                  export_all.push(ExportAll {
                    from: target,
                    type_only: export_list.stx.type_only,
                    span: loc_to_span(file, stmt.loc).range,
                  });
                }
                sem_builder.add_export_all(
                  spec,
                  loc_to_span(file, stmt.loc).range,
                  export_list.stx.type_only,
                );
              }
            }
          }
        }
        Stmt::Import(import_stmt) => {
          let module = import_stmt.stx.module.clone();
          let resolved = self
            .file_key_for_id(file)
            .and_then(|file_key| host.resolve(&file_key, &module))
            .map(|target| self.intern_file_key(target, FileOrigin::Source));
          if let Some(target) = resolved {
            queue.push_back(target);
          }
          let mut import_default = None;
          let mut import_namespace = None;
          let mut import_named = Vec::new();
          if let Some(default_pat) = import_stmt.stx.default.as_ref() {
            let alias_name = match &default_pat.stx.pat.stx.as_ref() {
              Pat::Id(id) => id.stx.name.clone(),
              _ => {
                self
                  .diagnostics
                  .push(codes::UNSUPPORTED_IMPORT_PATTERN.error(
                    "unsupported import pattern",
                    loc_to_span(file, default_pat.loc),
                  ));
                continue;
              }
            };
            import_default = Some(sem_ts::ImportDefault {
              local: alias_name.clone(),
              local_span: loc_to_span(file, default_pat.loc).range,
              is_type_only: import_stmt.stx.type_only,
            });
            let symbol = self.alloc_symbol();
            let def_id = self.alloc_def();
            self.def_data.insert(
              def_id,
              DefData {
                name: alias_name.clone(),
                file,
                span: loc_to_span(file, default_pat.loc).range,
                symbol,
                export: false,
                kind: DefKind::Import(ImportData {
                  specifier: module.clone(),
                  from: resolved,
                  original: "default".to_string(),
                  is_type_only: import_stmt.stx.type_only,
                }),
              },
            );
            defs.push(def_id);
            bindings.insert(
              alias_name.clone(),
              SymbolBinding {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
            self.record_symbol(file, loc_to_span(file, default_pat.loc).range, symbol);
          }
          match import_stmt.stx.names {
            Some(ImportNames::Specific(ref list)) => {
              for entry in list {
                let name = entry.stx.importable.as_str().to_string();
                let alias_pat = &entry.stx.alias;
                let alias_name = match &alias_pat.stx.pat.stx.as_ref() {
                  Pat::Id(id) => id.stx.name.clone(),
                  _ => {
                    self
                      .diagnostics
                      .push(codes::UNSUPPORTED_IMPORT_PATTERN.error(
                        "unsupported import pattern",
                        loc_to_span(file, alias_pat.loc),
                      ));
                    continue;
                  }
                };
                let is_type_only = import_stmt.stx.type_only || entry.stx.type_only;
                import_named.push(sem_ts::ImportNamed {
                  imported: name.clone(),
                  local: alias_name.clone(),
                  is_type_only,
                  imported_span: loc_to_span(file, entry.loc).range,
                  local_span: loc_to_span(file, alias_pat.loc).range,
                });
                let symbol = self.alloc_symbol();
                let def_id = self.alloc_def();
                self.def_data.insert(
                  def_id,
                  DefData {
                    name: alias_name.clone(),
                    file,
                    span: loc_to_span(file, alias_pat.loc).range,
                    symbol,
                    export: false,
                    kind: DefKind::Import(ImportData {
                      specifier: module.clone(),
                      from: resolved,
                      original: name.clone(),
                      is_type_only,
                    }),
                  },
                );
                self.record_def_symbol(def_id, symbol);
                defs.push(def_id);
                bindings.insert(
                  alias_name.clone(),
                  SymbolBinding {
                    symbol,
                    def: Some(def_id),
                    type_id: None,
                  },
                );
                self.record_symbol(file, loc_to_span(file, alias_pat.loc).range, symbol);
              }
            }
            Some(ImportNames::All(ref pat)) => {
              let alias_name = match &pat.stx.pat.stx.as_ref() {
                Pat::Id(id) => id.stx.name.clone(),
                _ => {
                  self.diagnostics.push(
                    codes::UNSUPPORTED_IMPORT_PATTERN
                      .error("unsupported import pattern", loc_to_span(file, pat.loc)),
                  );
                  continue;
                }
              };
              import_namespace = Some(sem_ts::ImportNamespace {
                local: alias_name.clone(),
                local_span: loc_to_span(file, pat.loc).range,
                is_type_only: import_stmt.stx.type_only,
              });
              let symbol = self.alloc_symbol();
              let def_id = self.alloc_def();
              self.def_data.insert(
                def_id,
                DefData {
                  name: alias_name.clone(),
                  file,
                  span: loc_to_span(file, pat.loc).range,
                  symbol,
                  export: false,
                  kind: DefKind::Import(ImportData {
                    specifier: module.clone(),
                    from: resolved,
                    original: "*".to_string(),
                    is_type_only: import_stmt.stx.type_only,
                  }),
                },
              );
              self.record_def_symbol(def_id, symbol);
              defs.push(def_id);
              bindings.insert(
                alias_name.clone(),
                SymbolBinding {
                  symbol,
                  def: Some(def_id),
                  type_id: None,
                },
              );
              self.record_symbol(file, loc_to_span(file, pat.loc).range, symbol);
            }
            None => {}
          }
          sem_builder.add_import(sem_ts::Import {
            specifier: module,
            specifier_span: loc_to_span(file, stmt.loc).range,
            default: import_default,
            namespace: import_namespace,
            named: import_named,
            is_type_only: import_stmt.stx.type_only,
          });
        }
        Stmt::Expr(_) | Stmt::If(_) | Stmt::Block(_) | Stmt::While(_) => {}
        _ => {}
      }
    }

    self
      .sem_hir
      .entry(file)
      .or_insert_with(|| sem_builder.finish());
    self.files.insert(
      file,
      FileState {
        defs,
        exports,
        bindings,
        top_body: None,
        reexports,
        export_all,
      },
    );
  }

  fn bind_namespace_body_defs(
    &mut self,
    file: FileId,
    body: &NamespaceBody,
    defs: &mut Vec<DefId>,
  ) {
    match body {
      NamespaceBody::Block(stmts) => self.bind_namespace_stmts(file, stmts, defs),
      NamespaceBody::Namespace(inner) => self.bind_namespace_body_defs(file, &inner.stx.body, defs),
    }
  }

  fn bind_namespace_stmts(&mut self, file: FileId, stmts: &[Node<Stmt>], defs: &mut Vec<DefId>) {
    for stmt in stmts {
      match stmt.stx.as_ref() {
        Stmt::InterfaceDecl(interface) => {
          let span = loc_to_span(file, stmt.loc);
          let name = interface.stx.name.clone();
          let mut object = self.object_type_from_members(&interface.stx.members);
          for base in interface.stx.extends.iter() {
            let base_ty = self.type_from_type_expr(base);
            if let TypeKind::Object(base_obj) = self.type_store.kind(base_ty).clone() {
              object = self.merge_object_types(object, base_obj);
            }
          }
          let typ = self.type_store.object(object);
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: interface.stx.export,
              kind: DefKind::Interface(InterfaceData { typ }),
            },
          );
          self.def_types.insert(def_id, typ);
          self.record_def_symbol(def_id, symbol);
          self.record_symbol(file, span.range, symbol);
          defs.push(def_id);
        }
        Stmt::TypeAliasDecl(alias) => {
          let span = loc_to_span(file, stmt.loc);
          let name = alias.stx.name.clone();
          let mut ty = self.type_from_type_expr(&alias.stx.type_expr);
          if ty == self.builtin.unknown {
            ty = self.type_store.literal_string(name.clone());
          }
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: alias.stx.export,
              kind: DefKind::TypeAlias(TypeAliasData { typ: ty }),
            },
          );
          self.def_types.insert(def_id, ty);
          self.record_def_symbol(def_id, symbol);
          self.record_symbol(file, span.range, symbol);
          defs.push(def_id);
        }
        Stmt::FunctionDecl(func) => {
          if let Some(name_node) = func.stx.name.as_ref() {
            let name = name_node.stx.name.clone();
            let symbol = self.alloc_symbol();
            self.record_symbol(file, loc_to_span(file, name_node.loc).range, symbol);
            let def_id = self.alloc_def();
            let func_data = self.lower_function(file, func.stx.function.stx.as_ref(), def_id);
            self.def_data.insert(
              def_id,
              DefData {
                name,
                file,
                span: loc_to_span(file, stmt.loc).range,
                symbol,
                export: func.stx.export || func.stx.export_default,
                kind: DefKind::Function(func_data),
              },
            );
            self.record_def_symbol(def_id, symbol);
            defs.push(def_id);
          }
        }
        Stmt::VarDecl(var) => {
          for declarator in var.stx.declarators.iter() {
            let pat = &declarator.pattern;
            let pat_span = loc_to_span(file, pat.loc).range;
            if let Pat::Id(id) = pat.stx.pat.stx.as_ref() {
              let name = id.stx.name.clone();
              let type_ann = declarator
                .type_annotation
                .as_ref()
                .map(|t| self.type_from_type_expr(t));
              let symbol = self.alloc_symbol();
              let def_id = self.alloc_def();
              self.record_symbol(file, pat_span, symbol);
              self.def_data.insert(
                def_id,
                DefData {
                  name,
                  file,
                  span: pat_span,
                  symbol,
                  export: var.stx.export,
                  kind: DefKind::Var(VarData {
                    typ: type_ann,
                    init: None,
                    body: BodyId(u32::MAX),
                    annotated: type_ann.is_some(),
                    mode: var.stx.mode,
                  }),
                },
              );
              self.record_def_symbol(def_id, symbol);
              defs.push(def_id);
            }
          }
        }
        Stmt::NamespaceDecl(ns) => {
          let span = loc_to_span(file, stmt.loc);
          let name = ns.stx.name.clone();
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: ns.stx.export,
              kind: DefKind::Var(VarData {
                typ: None,
                init: None,
                body: BodyId(u32::MAX),
                annotated: false,
                mode: VarDeclMode::Var,
              }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          self.record_symbol(file, span.range, symbol);
          defs.push(def_id);
          self.bind_namespace_body_defs(file, &ns.stx.body, defs);
        }
        Stmt::ModuleDecl(module) => {
          if let Some(body) = module.stx.body.as_ref() {
            self.bind_namespace_stmts(file, body, defs);
          }
        }
        Stmt::Block(block) => self.bind_namespace_stmts(file, &block.stx.body, defs),
        _ => {}
      }
    }
  }

  fn handle_var_decl(
    &mut self,
    file: FileId,
    var: &VarDecl,
    sem_builder: &mut SemHirBuilder,
  ) -> Vec<(DefId, (String, SymbolBinding), Option<String>)> {
    let mut defs = Vec::new();
    for declarator in var.declarators.iter() {
      let pat = &declarator.pattern;
      let pat_span = loc_to_span(file, pat.loc).range;
      let name = match pat.stx.pat.stx.as_ref() {
        Pat::Id(id) => id.stx.name.clone(),
        _ => {
          self.diagnostics.push(
            codes::UNSUPPORTED_PATTERN.error("unsupported pattern", loc_to_span(file, pat.loc)),
          );
          continue;
        }
      };
      let type_ann = declarator
        .type_annotation
        .as_ref()
        .map(|t| self.type_from_type_expr(t));
      let symbol = self.alloc_symbol();
      let def_id = self.alloc_def();
      self.record_symbol(file, loc_to_span(file, pat.loc).range, symbol);
      self.def_data.insert(
        def_id,
        DefData {
          name: name.clone(),
          file,
          span: pat_span,
          symbol,
          export: var.export,
          kind: DefKind::Var(VarData {
            typ: type_ann,
            init: None,
            body: BodyId(u32::MAX),
            annotated: type_ann.is_some(),
            mode: var.mode,
          }),
        },
      );
      self.record_def_symbol(def_id, symbol);
      defs.push((
        def_id,
        (
          name.clone(),
          SymbolBinding {
            symbol,
            def: Some(def_id),
            type_id: type_ann,
          },
        ),
        if var.export { Some(name.clone()) } else { None },
      ));
      sem_builder.add_decl(
        def_id,
        name.clone(),
        sem_ts::DeclKind::Var,
        if var.export {
          sem_ts::Exported::Named
        } else {
          sem_ts::Exported::No
        },
        pat_span,
      );
    }
    defs
  }

  fn handle_function_decl(
    &mut self,
    file: FileId,
    span: TextRange,
    func: &FuncDecl,
    sem_builder: &mut SemHirBuilder,
  ) -> Option<(DefId, (String, SymbolBinding), Option<String>)> {
    let name_node = func.name.as_ref()?;
    let name = name_node.stx.name.clone();
    let symbol = self.alloc_symbol();
    self.record_symbol(file, loc_to_span(file, name_node.loc).range, symbol);
    let def_id = self.alloc_def();
    let func_data = self.lower_function(file, func.function.stx.as_ref(), def_id);
    self.def_data.insert(
      def_id,
      DefData {
        name: name.clone(),
        file,
        span,
        symbol,
        export: func.export || func.export_default,
        kind: DefKind::Function(func_data),
      },
    );
    if let Some(store) = match self.interned_store.as_ref() {
      Some(store) => Some(Arc::clone(store)),
      None => {
        let store = tti::TypeStore::new();
        self.interned_store = Some(Arc::clone(&store));
        Some(store)
      }
    } {
      let mut lowerer = TypeLowerer::new(Arc::clone(&store));
      lowerer.set_file(file);
      lowerer.push_type_param_scope();
      let type_params = func
        .function
        .stx
        .type_parameters
        .as_ref()
        .map(|params| lowerer.register_type_params(params))
        .unwrap_or_default();
      let mut params = Vec::new();
      for param in func.function.stx.parameters.iter() {
        let ty = param
          .stx
          .type_annotation
          .as_ref()
          .map(|ann| lowerer.lower_type_expr(ann))
          .unwrap_or(store.primitive_ids().unknown);
        params.push(tti::Param {
          name: None,
          ty,
          optional: param.stx.optional,
          rest: param.stx.rest,
        });
      }
      let ret = func
        .function
        .stx
        .return_type
        .as_ref()
        .map(|t| lowerer.lower_type_expr(t))
        .unwrap_or(store.primitive_ids().unknown);
      lowerer.pop_type_param_scope();
      let sig = tti::Signature {
        params,
        ret,
        type_params: type_params.clone(),
        this_param: None,
      };
      let sig_id = store.intern_signature(sig);
      let callable = store.intern_type(tti::TypeKind::Callable {
        overloads: vec![sig_id],
      });
      if std::env::var("TRACE_LITMUS").is_ok() && name == "map" {
        eprintln!(
          "[ensure_types] lowered function {} -> {}",
          name,
          tti::TypeDisplay::new(&store, callable)
        );
      }
      self
        .interned_def_types
        .entry(def_id)
        .and_modify(|existing| {
          *existing = ProgramState::merge_interned_decl_types(&store, *existing, callable);
        })
        .or_insert(callable);
      if !type_params.is_empty() {
        self
          .interned_type_params
          .insert(def_id, type_params.iter().map(|p| p.id).collect());
      }
      let legacy = self.import_interned_type(callable);
      self.def_types.insert(def_id, legacy);
    }
    self.record_def_symbol(def_id, symbol);
    sem_builder.add_decl(
      def_id,
      name.clone(),
      sem_ts::DeclKind::Function,
      if func.export_default {
        sem_ts::Exported::Default
      } else if func.export {
        sem_ts::Exported::Named
      } else {
        sem_ts::Exported::No
      },
      loc_to_span(file, name_node.loc).range,
    );
    let binding = (
      name.clone(),
      SymbolBinding {
        symbol,
        def: Some(def_id),
        type_id: None,
      },
    );
    let export_name = if func.export_default {
      Some("default".to_string())
    } else if func.export {
      Some(name.clone())
    } else {
      None
    };
    Some((def_id, binding, export_name))
  }

  fn lower_function(&mut self, file: FileId, func: &Func, _def: DefId) -> FuncData {
    let mut params = Vec::new();
    for param in func.parameters.iter() {
      if let Some(data) = self.lower_param(file, param) {
        params.push(data);
      }
    }
    let return_ann = func
      .return_type
      .as_ref()
      .map(|t| self.type_from_type_expr(t));
    FuncData {
      params,
      return_ann,
      body: None,
    }
  }

  fn lower_param(&mut self, file: FileId, param: &Node<ParamDecl>) -> Option<ParamData> {
    let name = match param.stx.pattern.stx.pat.stx.as_ref() {
      Pat::Id(id) => id.stx.name.clone(),
      _ => {
        self
          .diagnostics
          .push(codes::UNSUPPORTED_PARAM_PATTERN.error(
            "unsupported parameter pattern",
            loc_to_span(file, param.loc),
          ));
        return None;
      }
    };
    let typ = param
      .stx
      .type_annotation
      .as_ref()
      .map(|t| self.type_from_type_expr(t));
    let symbol = self.alloc_symbol();
    self.record_symbol(file, loc_to_span(file, param.stx.pattern.loc).range, symbol);
    Some(ParamData {
      name,
      typ,
      symbol,
      pat: None,
    })
  }

  fn collect_parent_bindings(
    &mut self,
    body_id: BodyId,
    bindings: &mut HashMap<String, TypeId>,
    binding_defs: &mut HashMap<String, DefId>,
  ) {
    fn record_pat(
      state: &ProgramState,
      pat_id: HirPatId,
      body: &hir_js::Body,
      names: &hir_js::NameInterner,
      result: &BodyCheckResult,
      bindings: &mut HashMap<String, TypeId>,
      binding_defs: &mut HashMap<String, DefId>,
      file: FileId,
    ) {
      let Some(pat) = body.pats.get(pat_id.0 as usize) else {
        return;
      };
      let ty = result
        .pat_type(PatId(pat_id.0))
        .unwrap_or(state.builtin.unknown);
      match &pat.kind {
        HirPatKind::Ident(name_id) => {
          if let Some(name) = names.resolve(*name_id) {
            if ty != state.builtin.unknown {
              bindings.entry(name.to_string()).or_insert(ty);
            }
            if let Some(def_id) = state
              .def_data
              .iter()
              .find_map(|(id, data)| (data.file == file && data.span == pat.span).then_some(*id))
            {
              binding_defs.entry(name.to_string()).or_insert(def_id);
            }
          }
        }
        HirPatKind::Array(arr) => {
          for elem in arr.elements.iter().flatten() {
            record_pat(
              state,
              elem.pat,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
            );
          }
          if let Some(rest) = arr.rest {
            record_pat(
              state,
              rest,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
            );
          }
        }
        HirPatKind::Object(obj) => {
          for prop in obj.props.iter() {
            record_pat(
              state,
              prop.value,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
            );
          }
          if let Some(rest) = obj.rest {
            record_pat(
              state,
              rest,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
            );
          }
        }
        HirPatKind::Rest(inner) => {
          record_pat(
            state,
            **inner,
            body,
            names,
            result,
            bindings,
            binding_defs,
            file,
          );
        }
        HirPatKind::Assign { target, .. } => {
          record_pat(
            state,
            *target,
            body,
            names,
            result,
            bindings,
            binding_defs,
            file,
          );
        }
        HirPatKind::AssignTarget(_) => {}
      }
    }

    let mut visited = HashSet::new();
    let mut current = self.body_parents.get(&body_id).copied();
    while let Some(parent) = current {
      if !visited.insert(parent) {
        break;
      }
      let parent_result = self.check_body(parent);
      let Some(meta) = self.body_map.get(&parent).copied() else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(hir_body_id) = meta.hir else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(lowered) = self.hir_lowered.get(&meta.file) else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(body) = lowered.body(hir_body_id) else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      for pat in body.pats.iter().enumerate() {
        record_pat(
          self,
          HirPatId(pat.0 as u32),
          body,
          &lowered.names,
          &parent_result,
          bindings,
          binding_defs,
          meta.file,
        );
      }
      current = self.body_parents.get(&parent).copied();
    }
  }

  fn contextual_function_type(
    &mut self,
    def: DefId,
    store: &Arc<tti::TypeStore>,
    cache: &mut HashMap<TypeId, tti::TypeId>,
  ) -> Option<tti::TypeId> {
    for data in self.def_data.values() {
      let DefKind::Var(var) = &data.kind else {
        continue;
      };
      let Some(var_ty) = var.typ else {
        continue;
      };
      let Some(init) = var.init else {
        continue;
      };
      let Some(meta) = self.body_map.get(&var.body) else {
        continue;
      };
      let Some(hir_id) = meta.hir else {
        continue;
      };
      let Some(lowered) = self.hir_lowered.get(&meta.file) else {
        continue;
      };
      let Some(body) = lowered.body(hir_id) else {
        continue;
      };
      let Some(expr) = body.exprs.get(init.0 as usize) else {
        continue;
      };
      if let HirExprKind::FunctionExpr { def: func_def, .. } = &expr.kind {
        if DefId(func_def.0) == def {
          let mapped = if store.contains_type_id(var_ty) {
            store.canon(var_ty)
          } else {
            store.canon(convert_type_for_display(var_ty, self, store, cache))
          };
          return Some(mapped);
        }
      }
    }
    if let Some(body) = self.def_data.get(&def).and_then(|data| match &data.kind {
      DefKind::Function(func) => func.body,
      _ => None,
    }) {
      let parent = self.body_parents.get(&body).copied();
      let Some(parent) = parent else { return None };
      let Some(parent_meta) = self.body_map.get(&parent).copied() else {
        return None;
      };
      let Some(parent_hir) = parent_meta.hir else {
        return None;
      };
      let Some(lowered) = self.hir_lowered.get(&parent_meta.file) else {
        return None;
      };
      let Some(parent_body) = lowered.body(parent_hir) else {
        return None;
      };
      let expr_idx = parent_body
        .exprs
        .iter()
        .enumerate()
        .find_map(|(idx, expr)| match &expr.kind {
          HirExprKind::FunctionExpr { def: func_def, .. } if DefId(func_def.0) == def => Some(idx),
          _ => None,
        });
      let Some(expr_idx) = expr_idx else {
        return None;
      };
      let expr_id = hir_js::ExprId(expr_idx as u32);
      let parent_result = self.check_body(parent);
      if let Some(ty) = parent_result.expr_type(expr_id) {
        return Some(store.canon(ty));
      }
    }
    None
  }

  fn function_expr_span(&self, body: BodyId) -> Option<TextRange> {
    let mut visited = HashSet::new();
    let mut current = self.body_parents.get(&body).copied();
    while let Some(parent) = current {
      if !visited.insert(parent) {
        break;
      }
      let meta = match self.body_map.get(&parent) {
        Some(meta) => meta,
        None => {
          current = self.body_parents.get(&parent).copied();
          continue;
        }
      };
      let hir_id = match meta.hir {
        Some(id) => id,
        None => {
          current = self.body_parents.get(&parent).copied();
          continue;
        }
      };
      let parent_body = match self
        .hir_lowered
        .get(&meta.file)
        .and_then(|lowered| lowered.body(hir_id))
      {
        Some(body) => body,
        None => {
          current = self.body_parents.get(&parent).copied();
          continue;
        }
      };
      for expr in parent_body.exprs.iter() {
        if let HirExprKind::FunctionExpr { body: inner, .. } = &expr.kind {
          if *inner == body {
            return Some(expr.span);
          }
        }
      }
      current = self.body_parents.get(&parent).copied();
    }
    None
  }

  fn contextual_callable_for_body(
    &mut self,
    body: BodyId,
    func_span: TextRange,
    store: &Arc<tti::TypeStore>,
  ) -> Option<tti::TypeId> {
    let mut visited = HashSet::new();
    let mut current = self.body_parents.get(&body).copied();
    while let Some(parent) = current {
      if !visited.insert(parent) {
        break;
      }
      let parent_result = self.check_body(parent);
      let meta = match self.body_map.get(&parent) {
        Some(meta) => meta,
        None => {
          current = self.body_parents.get(&parent).copied();
          continue;
        }
      };
      let hir_body = match meta.hir.and_then(|hir_id| {
        self
          .hir_lowered
          .get(&meta.file)
          .and_then(|lowered| lowered.body(hir_id))
      }) {
        Some(body) => body,
        None => {
          current = self.body_parents.get(&parent).copied();
          continue;
        }
      };
      for (idx, expr) in hir_body.exprs.iter().enumerate() {
        if expr.span != func_span {
          continue;
        }
        if let Some(ty) = parent_result.expr_type(ExprId(idx as u32)) {
          let canonical = if store.contains_type_id(ty) {
            store.canon(ty)
          } else {
            let mut cache = HashMap::new();
            store.canon(convert_type_for_display(ty, self, store, &mut cache))
          };
          if matches!(store.type_kind(canonical), tti::TypeKind::Callable { .. }) {
            return Some(canonical);
          }
        }
      }
      current = self.body_parents.get(&parent).copied();
    }
    None
  }

  fn check_body(&mut self, body_id: BodyId) -> Arc<BodyCheckResult> {
    let cache_hit = self.body_results.contains_key(&body_id);
    let body_meta = self.body_map.get(&body_id).copied();
    let owner = self.owner_of_body(body_id);
    let prev_file = self.current_file;
    if let Some(meta) = body_meta.as_ref() {
      self.current_file = Some(meta.file);
    }
    let mut span = QuerySpan::enter(
      QueryKind::CheckBody,
      query_span!(
        "typecheck_ts.check_body",
        body_meta.as_ref().map(|b| b.file.0),
        owner.map(|d| d.0),
        Some(body_id.0),
        cache_hit
      ),
      None,
      cache_hit,
      Some(self.query_stats.clone()),
    );
    if let Some(existing) = self.body_results.get(&body_id) {
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return existing.clone();
    }
    let Some(meta) = body_meta else {
      let res = Arc::new(BodyCheckResult {
        body: body_id,
        expr_types: Vec::new(),
        expr_spans: Vec::new(),
        pat_types: Vec::new(),
        pat_spans: Vec::new(),
        diagnostics: vec![codes::MISSING_BODY.error(
          "missing body",
          Span::new(FileId(u32::MAX), TextRange::new(0, 0)),
        )],
        return_types: Vec::new(),
      });
      self.body_results.insert(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return res;
    };

    let file = meta.file;

    let Some(lowered) = self.hir_lowered.get(&file).cloned() else {
      let res = Arc::new(BodyCheckResult {
        body: body_id,
        expr_types: Vec::new(),
        expr_spans: Vec::new(),
        pat_types: Vec::new(),
        pat_spans: Vec::new(),
        diagnostics: Vec::new(),
        return_types: Vec::new(),
      });
      self.body_results.insert(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return res;
    };

    let Some(ast) = self.asts.get(&file).cloned() else {
      let res = Arc::new(BodyCheckResult {
        body: body_id,
        expr_types: Vec::new(),
        expr_spans: Vec::new(),
        pat_types: Vec::new(),
        pat_spans: Vec::new(),
        diagnostics: vec![codes::MISSING_BODY.error(
          "missing parsed AST for body",
          Span::new(file, TextRange::new(0, 0)),
        )],
        return_types: Vec::new(),
      });
      self.body_results.insert(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      return res;
    };

    let mut _synthetic = None;
    let body = if let Some(hir_id) = meta.hir {
      lowered.body(hir_id)
    } else if matches!(meta.kind, HirBodyKind::TopLevel) {
      _synthetic = Some(hir_js::Body {
        owner: HirDefId(u32::MAX),
        kind: HirBodyKind::TopLevel,
        exprs: Vec::new(),
        stmts: Vec::new(),
        pats: Vec::new(),
        root_stmts: Vec::new(),
        function: None,
        expr_types: None,
      });
      _synthetic.as_ref()
    } else {
      None
    };

    let Some(body) = body else {
      let res = Arc::new(BodyCheckResult {
        body: body_id,
        expr_types: Vec::new(),
        expr_spans: Vec::new(),
        pat_types: Vec::new(),
        pat_spans: Vec::new(),
        diagnostics: Vec::new(),
        return_types: Vec::new(),
      });
      self.body_results.insert(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      return res;
    };

    let store = match self.interned_store.as_ref() {
      Some(store) => Arc::clone(store),
      None => {
        let store = tti::TypeStore::new();
        self.interned_store = Some(Arc::clone(&store));
        store
      }
    };

    let global_binding_entries: Vec<_> = self
      .global_bindings
      .iter()
      .map(|(name, binding)| (name.clone(), binding.clone()))
      .collect();
    let file_binding_entries: Option<Vec<_>> = self.files.get(&file).map(|state| {
      state
        .bindings
        .iter()
        .map(|(name, binding)| (name.clone(), binding.clone()))
        .collect()
    });
    let mut bindings: HashMap<String, TypeId> = HashMap::new();
    let mut binding_defs: HashMap<String, DefId> = HashMap::new();
    let mut convert_cache = HashMap::new();
    let map_def_ty = |state: &ProgramState,
                      store: &Arc<tti::TypeStore>,
                      cache: &mut HashMap<TypeId, tti::TypeId>,
                      def: DefId| {
      state.interned_def_types.get(&def).copied().or_else(|| {
        state
          .def_types
          .get(&def)
          .copied()
          .map(|ty| store.canon(convert_type_for_display(ty, state, store, cache)))
      })
    };
    let mut bind = |name: &str, binding: &SymbolBinding| {
      let mut def_for_resolver = binding.def;
      let mut ty = binding.type_id.map(|ty| {
        if store.contains_type_id(ty) {
          store.canon(ty)
        } else {
          store.canon(convert_type_for_display(
            ty,
            self,
            &store,
            &mut convert_cache,
          ))
        }
      });
      if matches!(ty, Some(t) if matches!(store.type_kind(t), tti::TypeKind::Unknown)) {
        ty = None;
      }
      if let Some(def) = binding.def {
        if let Some(defs) = self.callable_overload_defs(def) {
          if let Some(first) = defs.first().copied() {
            def_for_resolver = Some(first);
          }
          if defs.len() > 1 {
            if let Some(merged) =
              self.callable_overload_type_for_def(def, &store, &mut convert_cache)
            {
              ty = Some(merged);
            }
          }
        }
        if ty.is_none() {
          ty = map_def_ty(self, &store, &mut convert_cache, def);
        }
      }
      if ty.is_none() {
        ty = binding
          .def
          .and_then(|d| self.enum_value_types.get(&d).copied());
      }
      let ty = ty.unwrap_or_else(|| store.primitive_ids().unknown);
      bindings.insert(name.to_string(), ty);
      if let Some(def) = def_for_resolver {
        binding_defs.insert(name.to_string(), def);
      }
    };
    for (name, binding) in global_binding_entries.into_iter() {
      bind(&name, &binding);
    }
    if let Some(file_state) = file_binding_entries {
      for (name, binding) in file_state.into_iter() {
        bind(&name, &binding);
      }
    }

    self.collect_parent_bindings(body_id, &mut bindings, &mut binding_defs);

    let def_by_name: HashMap<(sem_ts::FileId, String), DefId> = self
      .canonical_defs()
      .into_iter()
      .map(|((file_id, name), def)| ((sem_ts::FileId(file_id.0), name), def))
      .collect();
    let def_info: HashMap<sem_ts::DefId, DefInfo> = self
      .def_data
      .iter()
      .map(|(id, data)| {
        (
          sem_ts::DefId(id.0),
          DefInfo {
            file: sem_ts::FileId(data.file.0),
            span: data.span,
            name: data.name.clone(),
            export: data.export,
          },
        )
      })
      .collect();
    let mut function_expected: Option<tti::TypeId> = None;
    if matches!(meta.kind, HirBodyKind::Function) {
      if let Some(owner_def) = owner {
        let mut expected = map_def_ty(self, &store, &mut convert_cache, owner_def);
        if matches!(
          expected,
          Some(ty) if matches!(store.type_kind(ty), tti::TypeKind::Unknown)
        ) {
          expected = None;
        }
        let contextual_expected =
          self.contextual_function_type(owner_def, &store, &mut convert_cache);
        let callable_has_unknown = |ty: tti::TypeId| {
          if let tti::TypeKind::Callable { overloads } = store.type_kind(ty) {
            if let Some(sig_id) = overloads.first() {
              let sig = store.signature(*sig_id);
              let params_unknown = sig
                .params
                .iter()
                .any(|param| matches!(store.type_kind(param.ty), tti::TypeKind::Unknown));
              let ret_unknown = matches!(store.type_kind(sig.ret), tti::TypeKind::Unknown);
              return params_unknown || ret_unknown;
            }
          }
          false
        };
        if expected
          .as_ref()
          .map(|ty| callable_has_unknown(*ty))
          .unwrap_or(false)
          && contextual_expected.is_some()
        {
          expected = contextual_expected;
        } else if expected.is_none() {
          expected = contextual_expected;
        }
        if expected.is_none() {
          if let Some(span) = self.function_expr_span(body_id) {
            expected = self.contextual_callable_for_body(body_id, span, &store);
          }
        }
        function_expected = expected;
      }
    }
    let caches = self.checker_caches.for_body();
    let expander = RefExpander::new(
      Arc::clone(&store),
      &self.interned_def_types,
      &self.interned_type_params,
      caches.eval.clone(),
    );
    let prim = store.primitive_ids();
    let binding_resolver = (!binding_defs.is_empty()).then(|| {
      Arc::new(check::hir_body::BindingTypeResolver::new(
        binding_defs.clone(),
      )) as Arc<dyn TypeResolver>
    });
    let resolver: Option<Arc<dyn TypeResolver>> = self
      .semantics
      .as_ref()
      .map(|sem| {
        Arc::new(ProgramTypeResolver::new(
          Arc::new(sem.clone()),
          Arc::new(self.symbol_to_def.clone()),
          Arc::new(def_by_name.clone()),
          Arc::new(def_info.clone()),
          file,
          binding_resolver.clone(),
        )) as Arc<dyn TypeResolver>
      })
      .or(binding_resolver);
    let mut result = check::hir_body::check_body_with_expander(
      body_id,
      body,
      &lowered.names,
      file,
      ast.as_ref(),
      Arc::clone(&store),
      &caches,
      &bindings,
      resolver,
      Some(&expander),
    );
    if let Some(expected) = function_expected {
      if std::env::var("TRACE_CONTEXTUAL").is_ok() {
        if let Some(owner_def) = owner {
          let name = self
            .def_data
            .get(&owner_def)
            .map(|d| d.name.clone())
            .unwrap_or_default();
          eprintln!(
            "[contextual] body {:?} owner {:?} ({}) -> {}",
            body_id,
            owner_def,
            name,
            tti::TypeDisplay::new(&store, expected)
          );
        }
      }
      if let tti::TypeKind::Callable { overloads } = store.type_kind(expected) {
        if let (Some(sig_id), Some(function)) = (overloads.first(), body.function.as_ref()) {
          let sig = store.signature(*sig_id);
          for (param, expected_param) in function.params.iter().zip(sig.params.iter()) {
            if let Some(slot) = result.pat_types.get_mut(param.pat.0 as usize) {
              *slot = expected_param.ty;
            }
          }
        }
      }
    }
    if !body.exprs.is_empty() && matches!(meta.kind, HirBodyKind::Function) {
      let mut initial_env: HashMap<NameId, TypeId> = HashMap::new();
      if let Some(function) = body.function.as_ref() {
        for param in function.params.iter() {
          if let Some(ty) = result.pat_types.get(param.pat.0 as usize).copied() {
            if ty != prim.unknown {
              if let Some(pat) = body.pats.get(param.pat.0 as usize) {
                if let hir_js::PatKind::Ident(name) = pat.kind {
                  initial_env.insert(name, ty);
                }
              }
            }
          }
        }
      }
      for expr in body.exprs.iter() {
        if let hir_js::ExprKind::Ident(name_id) = expr.kind {
          if initial_env.contains_key(&name_id) {
            continue;
          }
          if let Some(name) = lowered.names.resolve(name_id) {
            if let Some(ty) = bindings.get(name) {
              initial_env.insert(name_id, *ty);
            }
          }
        }
      }
      let flow_result = check::hir_body::check_body_with_env_with_expander(
        body_id,
        body,
        &lowered.names,
        file,
        "",
        Arc::clone(&store),
        &initial_env,
        Some(&expander),
      );
      let mut relate_hooks = relate_hooks();
      relate_hooks.expander = Some(&expander);
      let relate = RelateCtx::with_hooks_and_cache(
        Arc::clone(&store),
        store.options(),
        relate_hooks,
        caches.relation.clone(),
      );
      if flow_result.expr_types.len() == result.expr_types.len() {
        for (idx, ty) in flow_result.expr_types.iter().enumerate() {
          if *ty != prim.unknown {
            let existing = result.expr_types[idx];
            let narrower =
              relate.is_assignable(*ty, existing) && !relate.is_assignable(existing, *ty);
            if existing == prim.unknown || narrower {
              result.expr_types[idx] = *ty;
            }
          }
        }
      }
      if flow_result.pat_types.len() == result.pat_types.len() {
        for (idx, ty) in flow_result.pat_types.iter().enumerate() {
          if *ty != prim.unknown {
            let existing = result.pat_types[idx];
            let narrower =
              relate.is_assignable(*ty, existing) && !relate.is_assignable(existing, *ty);
            if existing == prim.unknown || narrower {
              result.pat_types[idx] = *ty;
            }
          }
        }
      }
      if result.return_types.is_empty() && !flow_result.return_types.is_empty() {
        result.return_types = flow_result.return_types;
      }
      if !flow_result.diagnostics.is_empty() {
        for diag in flow_result.diagnostics {
          let duplicate = result
            .diagnostics
            .iter()
            .any(|existing| existing.code == diag.code && existing.primary == diag.primary);
          if !duplicate {
            result.diagnostics.push(diag);
          }
        }
      }
    }
    for (idx, pat) in body.pats.iter().enumerate() {
      if let hir_js::PatKind::Ident(name_id) = pat.kind {
        if let Some(name) = lowered.names.resolve(name_id) {
          if let Some(def_id) = binding_defs.get(name) {
            if let Some(ty) = result.pat_types.get(idx).copied() {
              if !matches!(store.type_kind(ty), tti::TypeKind::Unknown) {
                let has_annotation = self
                  .def_data
                  .get(def_id)
                  .and_then(|def| match &def.kind {
                    DefKind::Var(var) => Some(var.annotated),
                    _ => None,
                  })
                  .unwrap_or(false);
                if has_annotation {
                  continue;
                }
                self.interned_def_types.insert(*def_id, ty);
                let store_ty = self.import_interned_type(ty);
                self.def_types.insert(*def_id, store_ty);
                if let Some(def) = self.def_data.get_mut(def_id) {
                  if let DefKind::Var(var) = &mut def.kind {
                    if !var.annotated || var.typ.is_none() {
                      var.typ = Some(store_ty);
                    }
                  }
                }
              } else {
              }
            }
          }
        }
      }
    }
    let res = Arc::new(result);
    if matches!(self.compiler_options.cache.mode, CacheMode::PerBody) {
      let mut stats = caches.stats();
      if stats.relation.evictions == 0 {
        let max = self.compiler_options.cache.max_relation_cache_entries as u64;
        if max > 0 && stats.relation.insertions > max {
          stats.relation.evictions = stats.relation.insertions - max;
        } else {
          stats.relation.evictions = 1;
        }
      }
      self.cache_stats.merge(&stats);
    }
    self.body_results.insert(body_id, res.clone());
    if let Some(span) = span.take() {
      span.finish(None);
    }
    self.current_file = prev_file;
    res
  }

  fn import_interned_type(&mut self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref().cloned() else {
      return self.builtin.unknown;
    };
    use tti::TypeKind as InternedKind;
    match store.type_kind(ty) {
      InternedKind::Any => self.builtin.any,
      InternedKind::Unknown => self.builtin.unknown,
      InternedKind::Never => self.builtin.never,
      InternedKind::Void => self.builtin.void,
      InternedKind::Null => self.builtin.null,
      InternedKind::Undefined => self.builtin.undefined,
      InternedKind::Boolean => self.builtin.boolean,
      InternedKind::Number => self.builtin.number,
      InternedKind::String => self.builtin.string,
      InternedKind::BooleanLiteral(value) => self.type_store.literal_boolean(value),
      InternedKind::NumberLiteral(value) => self.type_store.literal_number(value.to_string()),
      InternedKind::StringLiteral(name) => {
        let name = store.name(name);
        self.type_store.literal_string(name)
      }
      InternedKind::Tuple(elems) => {
        let readonly = elems.iter().all(|elem| elem.readonly);
        let members: Vec<_> = elems
          .iter()
          .map(|elem| self.import_interned_type(elem.ty))
          .collect();
        self.type_store.tuple(members, readonly)
      }
      InternedKind::Array { ty, .. } => {
        let inner = self.import_interned_type(ty);
        self.type_store.array(inner)
      }
      InternedKind::Union(types) => {
        let mapped: Vec<_> = types
          .iter()
          .map(|t| self.import_interned_type(*t))
          .collect();
        self.type_store.union(mapped, &self.builtin)
      }
      InternedKind::Callable { overloads } => {
        if let Some(sig_id) = overloads.first() {
          let sig = store.signature(*sig_id);
          let params: Vec<_> = sig
            .params
            .iter()
            .map(|param| self.import_interned_type(param.ty))
            .collect();
          let ret = self.import_interned_type(sig.ret);
          self.type_store.function(params, ret)
        } else {
          self.builtin.unknown
        }
      }
      InternedKind::Object(obj) => {
        let obj = store.object(obj);
        let shape = store.shape(obj.shape);
        let mut legacy = ObjectType::empty();
        for prop in shape.properties {
          let name = match prop.key {
            tti::PropKey::String(id) | tti::PropKey::Symbol(id) => Some(store.name(id)),
            tti::PropKey::Number(num) => Some(num.to_string()),
          };
          if let Some(name) = name {
            legacy.props.insert(
              name,
              ObjectProperty {
                typ: self.import_interned_type(prop.data.ty),
                optional: prop.data.optional,
                readonly: prop.data.readonly,
              },
            );
          }
        }
        for indexer in shape.indexers {
          let value = self.import_interned_type(indexer.value_type);
          match store.type_kind(indexer.key_type) {
            InternedKind::String => legacy.string_index = Some(value),
            InternedKind::Number => legacy.number_index = Some(value),
            _ => {}
          }
        }
        self.type_store.object(legacy)
      }
      InternedKind::Predicate {
        parameter,
        asserted,
        asserts,
      } => {
        let param = parameter.map(|id| store.name(id)).unwrap_or_default();
        let asserted = asserted.map(|ty| self.import_interned_type(ty));
        self.type_store.predicate(param, asserted, asserts)
      }
      InternedKind::Ref { def, .. } => {
        let def = DefId(def.0);
        if self.type_stack.contains(&def) {
          return self.builtin.unknown;
        }
        if let Some(existing) = self.def_types.get(&def).copied() {
          existing
        } else if let Some(interned) = self.interned_def_types.get(&def).copied() {
          if let InternedKind::Ref { def: inner, .. } = store.type_kind(interned) {
            if DefId(inner.0) == def {
              return self.builtin.unknown;
            }
          }
          self.import_interned_type(interned)
        } else {
          let mut computed = self.type_of_def(def);
          if matches!(self.type_store.kind(computed), TypeKind::Unknown) {
            if let Some(def_data) = self.def_data.get(&def).cloned() {
              if let Some(file_key) = self.file_key_for_id(def_data.file) {
                let candidates: Vec<_> = self
                  .def_data
                  .iter()
                  .filter(|(id, data)| {
                    **id != def
                      && data.name == def_data.name
                      && self.file_key_for_id(data.file) == Some(file_key.clone())
                  })
                  .map(|(id, _)| *id)
                  .collect();
                for alt_def in candidates {
                  let ty = self.type_of_def(alt_def);
                  if !matches!(self.type_store.kind(ty), TypeKind::Unknown) {
                    computed = ty;
                    break;
                  }
                }
              }
            }
          }
          if matches!(self.type_store.kind(computed), TypeKind::Unknown) {
            self.builtin.unknown
          } else {
            computed
          }
        }
      }
      _ => self.builtin.unknown,
    }
  }

  fn ensure_interned_type(&mut self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref() else {
      return ty;
    };
    if store.contains_type_id(ty) {
      return store.canon(ty);
    }
    if let Some(mapped) = self.def_types.iter().find_map(|(def, stored_ty)| {
      if *stored_ty == ty {
        self.interned_def_types.get(def).copied()
      } else {
        None
      }
    }) {
      return store.canon(mapped);
    }
    let mut cache = HashMap::new();
    let interned = convert_type_for_display(ty, self, store, &mut cache);
    store.canon(interned)
  }

  fn prefer_named_refs(&self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref() else {
      return ty;
    };
    self.prefer_named_refs_in_store(store, ty)
  }

  fn prefer_named_refs_in_store(&self, store: &Arc<tti::TypeStore>, ty: TypeId) -> TypeId {
    let canonical = store.canon(ty);
    let mut candidates: Vec<_> = self
      .interned_def_types
      .iter()
      .filter_map(|(def, def_ty)| {
        if store.canon(*def_ty) != canonical {
          return None;
        }
        match self.def_data.get(def).map(|d| &d.kind) {
          Some(DefKind::TypeAlias(_) | DefKind::Interface(_)) => Some(*def),
          Some(DefKind::Import(import)) if import.is_type_only => Some(*def),
          _ => None,
        }
      })
      .collect();
    candidates.sort_by_key(|def| def.0);
    if let Some(def) = candidates.first().copied() {
      return store.intern_type(tti::TypeKind::Ref {
        def,
        args: Vec::new(),
      });
    }
    match store.type_kind(canonical) {
      tti::TypeKind::Union(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|member| self.prefer_named_refs_in_store(store, member))
          .collect();
        return store.union(mapped);
      }
      tti::TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|member| self.prefer_named_refs_in_store(store, member))
          .collect();
        return store.intersection(mapped);
      }
      tti::TypeKind::Array { ty, readonly } => {
        let mapped = self.prefer_named_refs_in_store(store, ty);
        if mapped != ty {
          return store.intern_type(tti::TypeKind::Array {
            ty: mapped,
            readonly,
          });
        }
      }
      tti::TypeKind::Tuple(elems) => {
        let mut changed = false;
        let mapped: Vec<_> = elems
          .into_iter()
          .map(|elem| {
            let mapped = self.prefer_named_refs_in_store(store, elem.ty);
            changed |= mapped != elem.ty;
            tti::TupleElem {
              ty: mapped,
              optional: elem.optional,
              rest: elem.rest,
              readonly: elem.readonly,
            }
          })
          .collect();
        if changed {
          return store.intern_type(tti::TypeKind::Tuple(mapped));
        }
      }
      _ => {}
    }
    canonical
  }

  fn widen_literal(&self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty) {
      TypeKind::LiteralNumber(_) => self.builtin.number,
      TypeKind::LiteralString(_) => self.builtin.string,
      TypeKind::LiteralBoolean(_) => self.builtin.boolean,
      _ => ty,
    }
  }

  fn widen_literal_any(&self, ty: TypeId) -> TypeId {
    let widened = self.widen_literal(ty);
    if widened != ty {
      return widened;
    }
    if let Some(store) = self.interned_store.as_ref() {
      if store.contains_type_id(ty) {
        return match store.type_kind(ty) {
          tti::TypeKind::NumberLiteral(_) => self.builtin.number,
          tti::TypeKind::StringLiteral(_) => self.builtin.string,
          tti::TypeKind::BooleanLiteral(_) => self.builtin.boolean,
          _ => ty,
        };
      }
    }
    ty
  }

  fn mapped_keys(&self, ty: TypeId) -> Option<Vec<String>> {
    match self.type_store.kind(ty).clone() {
      TypeKind::LiteralString(name) => Some(vec![name]),
      TypeKind::Union(members) => {
        let mut keys = Vec::new();
        for member in members {
          let Some(mut inner) = self.mapped_keys(member) else {
            return None;
          };
          keys.append(&mut inner);
        }
        if keys.is_empty() {
          None
        } else {
          Some(keys)
        }
      }
      _ => None,
    }
  }

  fn widen_union_literals(&mut self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty).clone() {
      TypeKind::LiteralNumber(_) => self.builtin.number,
      TypeKind::LiteralString(_) => self.builtin.string,
      TypeKind::LiteralBoolean(_) => self.builtin.boolean,
      TypeKind::Union(types) => {
        let members: Vec<_> = types
          .into_iter()
          .map(|t| self.widen_union_literals(t))
          .collect();
        self.type_store.union(members, &self.builtin)
      }
      TypeKind::Array(inner) => {
        let widened = self.widen_union_literals(inner);
        self.type_store.array(widened)
      }
      _ => ty,
    }
  }

  fn widen_array_elements(&mut self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty).clone() {
      TypeKind::Array(inner) => {
        let widened = self.widen_union_literals(inner);
        self.type_store.array(widened)
      }
      TypeKind::Tuple(elems, _) => {
        let union = self.type_store.union(elems, &self.builtin);
        let widened = self.widen_union_literals(union);
        self.type_store.array(widened)
      }
      _ => ty,
    }
  }

  fn widen_object_literal(&mut self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty).clone() {
      TypeKind::Object(mut obj) => {
        let mut changed = false;
        for prop in obj.props.values_mut() {
          if prop.readonly {
            continue;
          }
          let widened = self.widen_union_literals(prop.typ);
          if widened != prop.typ {
            prop.typ = widened;
            changed = true;
          }
        }
        if let Some(value) = obj.string_index {
          let widened = self.widen_union_literals(value);
          if widened != value {
            obj.string_index = Some(widened);
            changed = true;
          }
        }
        if let Some(value) = obj.number_index {
          let widened = self.widen_union_literals(value);
          if widened != value {
            obj.number_index = Some(widened);
            changed = true;
          }
        }
        if changed {
          self.type_store.object(obj)
        } else {
          ty
        }
      }
      _ => ty,
    }
  }

  fn init_is_satisfies(&self, body: BodyId, expr: ExprId) -> bool {
    let meta = match self.body_map.get(&body) {
      Some(meta) => meta,
      None => return false,
    };
    let hir_id = match meta.hir {
      Some(id) => id,
      None => return false,
    };
    let lowered = match self.hir_lowered.get(&meta.file) {
      Some(lowered) => lowered,
      None => return false,
    };
    let hir_body = match lowered.body(hir_id) {
      Some(body) => body,
      None => return false,
    };
    hir_body
      .exprs
      .get(expr.0 as usize)
      .map(|e| matches!(e.kind, HirExprKind::Satisfies { .. }))
      .unwrap_or(false)
  }

  fn type_of_def(&mut self, def: DefId) -> TypeId {
    let cache_hit = self.def_types.contains_key(&def);
    let mut span = QuerySpan::enter(
      QueryKind::TypeOfDef,
      query_span!(
        "typecheck_ts.type_of_def",
        self.def_data.get(&def).map(|d| d.file.0),
        Some(def.0),
        self.body_of_def(def).map(|b| b.0),
        cache_hit
      ),
      self.def_types.get(&def).copied(),
      cache_hit,
      Some(self.query_stats.clone()),
    );
    let def_data = match self.def_data.get(&def).cloned() {
      Some(data) => data,
      None => {
        if let Some(span) = span.take() {
          span.finish(Some(self.builtin.unknown));
        }
        return self.builtin.unknown;
      }
    };
    let annotated_var = matches!(
      def_data.kind,
      DefKind::Var(VarData {
        annotated: true,
        ..
      })
    );
    let force_recompute = match &def_data.kind {
      DefKind::Var(var) => var.init.is_some() && !var.annotated,
      DefKind::TypeAlias(_) => true,
      _ => annotated_var,
    };

    if !force_recompute {
      if let (Some(store), Some(interned)) = (
        self.interned_store.as_ref(),
        self.interned_def_types.get(&def),
      ) {
        let interned_kind = store.type_kind(*interned);
        let cached_ref_alias = matches!(def_data.kind, DefKind::TypeAlias(_))
          && matches!(interned_kind, tti::TypeKind::Ref { .. });
        if !matches!(interned_kind, tti::TypeKind::Unknown) && !cached_ref_alias {
          let canonical = store.canon(*interned);
          let mapped = self.import_interned_type(canonical);
          self.def_types.insert(def, mapped);
          if let Some(span) = span.take() {
            span.finish(Some(canonical));
          }
          return canonical;
        }
      }
      if let Some(existing) = self.def_types.get(&def).copied() {
        let in_bounds = (existing.0 as usize) < self.type_store.kinds.len();
        if in_bounds && !matches!(self.type_store.kind(existing), TypeKind::Unknown) {
          if let Some(span) = span.take() {
            span.finish(Some(existing));
          }
          return existing;
        }
        self.def_types.remove(&def);
        self.interned_def_types.remove(&def);
      } else if let Some(interned) = self.interned_def_types.get(&def).copied() {
        if let Some(store) = self.interned_store.as_ref() {
          if store.contains_type_id(interned)
            && !matches!(store.type_kind(interned), tti::TypeKind::Unknown)
          {
            let imported = self.import_interned_type(interned);
            self.def_types.insert(def, imported);
            if let Some(span) = span.take() {
              span.finish(Some(imported));
            }
            return imported;
          }
        }
        self.interned_def_types.remove(&def);
      }
    } else {
      self.def_types.remove(&def);
      self.interned_def_types.remove(&def);
    }

    let prev_file = self.current_file;
    self.current_file = Some(def_data.file);
    if self.type_stack.contains(&def) {
      if let Some(span) = span.take() {
        span.finish(Some(self.builtin.any));
      }
      self.current_file = prev_file;
      return self.builtin.any;
    }
    self.type_stack.push(def);
    let ns_entry = self
      .namespace_object_types
      .get(&(def_data.file, def_data.name.clone()))
      .copied();
    let ty = match def_data.kind.clone() {
      DefKind::Function(func) => self.function_type(def, func),
      DefKind::Var(var) => {
        let mut init_span_for_const = None;
        let existing_kind = var.typ.map(|ty| self.type_store.kind(ty).clone());
        let is_const_literal = match existing_kind.as_ref() {
          Some(TypeKind::Tuple(_, readonly)) => *readonly,
          Some(TypeKind::Object(obj)) => obj.props.values().any(|p| p.readonly),
          _ => false,
        };
        let mut annotated = if var.annotated {
          var.typ
        } else if var.init.is_none() || is_const_literal {
          var.typ
        } else {
          None
        };
        if let Some(ann) = annotated {
          if matches!(self.type_store.kind(ann), TypeKind::Unknown) {
            let res = self.check_body(var.body);
            if let Some((idx, _)) = res
              .pat_spans()
              .iter()
              .enumerate()
              .find(|(_, span)| **span == def_data.span)
            {
              if let Some(pat_ty) = res.pat_type(PatId(idx as u32)) {
                let imported = self.import_interned_type(pat_ty);
                annotated = Some(imported);
                if let Some(store) = self.interned_store.as_ref() {
                  self.interned_def_types.insert(def, store.canon(pat_ty));
                }
              }
            }
            if matches!(
              annotated,
              Some(ty) if matches!(self.type_store.kind(ty), TypeKind::Unknown)
            ) {
              let pat_types: Vec<_> = res.pat_types().to_vec();
              for pat_ty in pat_types {
                let imported = self.import_interned_type(pat_ty);
                if !matches!(self.type_store.kind(imported), TypeKind::Unknown) {
                  annotated = Some(imported);
                  break;
                }
              }
            }
          }
        }
        let mut inferred = if let Some(t) = annotated {
          t
        } else if let Some(init) = var.init {
          self.body_results.remove(&var.body);
          let res = self.check_body(var.body);
          init_span_for_const = res.expr_span(init);
          if let Some(init_ty) = res.expr_type(init) {
            if let Some(store) = self.interned_store.as_ref() {
              let init_ty = store.canon(init_ty);
              self
                .interned_def_types
                .entry(def)
                .and_modify(|existing| {
                  *existing = ProgramState::merge_interned_decl_types(store, *existing, init_ty);
                })
                .or_insert(init_ty);
            }
            self.import_interned_type(init_ty)
          } else {
            self.builtin.unknown
          }
        } else if let Some((_, store_ty)) = ns_entry {
          store_ty
        } else {
          self.builtin.unknown
        };
        if var.mode == VarDeclMode::Const {
          if let Some(init_span) = init_span_for_const {
            if let Some(file_body) = self.files.get(&def_data.file).and_then(|f| f.top_body) {
              let res = self.check_body(file_body);
              let top_ty = res
                .expr_spans()
                .iter()
                .enumerate()
                .find(|(_, span)| **span == init_span)
                .and_then(|(idx, _)| res.expr_type(ExprId(idx as u32)));
              if let (Some(top_ty), Some(store)) = (top_ty, self.interned_store.as_ref()) {
                let top_kind = store.type_kind(top_ty);
                let has_readonly = match top_kind {
                  tti::TypeKind::Object(obj) => {
                    let shape = store.shape(store.object(obj).shape);
                    shape.properties.iter().any(|p| p.data.readonly)
                  }
                  tti::TypeKind::Tuple(elems) => elems.iter().any(|e| e.readonly),
                  _ => false,
                };
                if has_readonly {
                  let top_ty = store.canon(top_ty);
                  self.interned_def_types.insert(def, top_ty);
                  inferred = self.import_interned_type(top_ty);
                }
              }
            }
          }
        }
        let init_is_satisfies = var
          .init
          .map(|init| self.init_is_satisfies(var.body, init))
          .unwrap_or(false);
        if annotated.is_none() && !init_is_satisfies {
          inferred = self.widen_array_elements(inferred);
        }
        if annotated.is_none() {
          if !init_is_satisfies {
            inferred = self.widen_object_literal(inferred);
          }
        }
        let ty = if var.mode == VarDeclMode::Const {
          inferred
        } else {
          self.widen_literal(inferred)
        };
        if let Some(store) = self.interned_store.as_ref() {
          let mut cache = HashMap::new();
          let interned = store.canon(convert_type_for_display(ty, self, store, &mut cache));
          self.interned_def_types.insert(def, interned);
        }
        ty
      }
      DefKind::Import(import) => {
        if let Some(entry) = self.resolve_import_entry(&import) {
          let mut ty = if let Some(ty) = entry.type_id {
            if let Some(store) = self.interned_store.as_ref() {
              if store.contains_type_id(ty) {
                let ty = store.canon(ty);
                self.interned_def_types.insert(def, ty);
                self.import_interned_type(ty)
              } else {
                ty
              }
            } else {
              ty
            }
          } else if let Some(def) = entry.def {
            self.type_of_def(def)
          } else {
            self.builtin.unknown
          };
          if ty == self.builtin.unknown {
            if let Some(def) = entry.def {
              ty = self.type_of_def(def);
            }
          }
          ty
        } else {
          self.builtin.unknown
        }
      }
      DefKind::Interface(interface) => {
        if let Some(store) = self.interned_store.as_ref() {
          if !self.interned_def_types.contains_key(&def) {
            let mut cache = HashMap::new();
            let interned = convert_type_for_display(interface.typ, self, store, &mut cache);
            self.interned_def_types.insert(def, store.canon(interned));
          }
        }
        interface.typ
      }
      DefKind::TypeAlias(alias) => {
        let mut typ = alias.typ;
        if let Some(store) = self.interned_store.as_ref() {
          if let Some(interned) = self.interned_def_types.get(&def).copied() {
            typ = self.import_interned_type(store.canon(interned));
          }
        }
        let fallback_literal = matches!(
          self.type_store.kind(typ),
          TypeKind::LiteralString(name) if *name == def_data.name
        );
        if fallback_literal || matches!(self.type_store.kind(typ), TypeKind::Unknown) {
          if let Some(ast) = self.asts.get(&def_data.file).cloned() {
            for stmt in ast.stx.body.iter() {
              if let Stmt::TypeAliasDecl(decl) = stmt.stx.as_ref() {
                let span = loc_to_span(def_data.file, stmt.loc).range;
                if span == def_data.span {
                  let prev = self.current_file;
                  self.current_file = Some(def_data.file);
                  typ = self.type_from_type_expr(&decl.stx.type_expr);
                  self.current_file = prev;
                  if let Some(data) = self.def_data.get_mut(&def) {
                    if let DefKind::TypeAlias(alias) = &mut data.kind {
                      alias.typ = typ;
                    }
                  }
                  break;
                }
              }
            }
          }
        }
        if let Some(store) = self.interned_store.as_ref().cloned() {
          let mut cache = HashMap::new();
          let mut interned = convert_type_for_display(typ, self, &store, &mut cache);
          if let tti::TypeKind::Ref { def: target, args } = store.type_kind(interned) {
            if args.is_empty() && !self.type_stack.contains(&DefId(target.0)) {
              let target_ty = self.type_of_def(DefId(target.0));
              interned = store.canon(convert_type_for_display(
                target_ty, self, &store, &mut cache,
              ));
              typ = self.import_interned_type(interned);
            }
          }
          if std::env::var("TRACE_AMBIENT").is_ok() {
            eprintln!(
              "[type_of_def alias] def {:?} typ {} interned {}",
              def,
              tti::TypeDisplay::new(
                &store,
                convert_type_for_display(typ, self, &store, &mut cache)
              ),
              tti::TypeDisplay::new(&store, interned)
            );
          }
          self.interned_def_types.insert(def, interned);
        }
        typ
      }
    };
    if let Some(store) = self.interned_store.as_ref() {
      if !self.interned_def_types.contains_key(&def) {
        let mut cache = HashMap::new();
        let interned = store.canon(convert_type_for_display(ty, self, store, &mut cache));
        self.interned_def_types.insert(def, interned);
      }
    }
    if let Some((ns_interned, _ns_store)) = ns_entry {
      match def_data.kind {
        DefKind::Function(_) | DefKind::Var(_) => {
          if let Some(store) = self.interned_store.as_ref() {
            let merged = if let Some(existing) = self.interned_def_types.get(&def).copied() {
              store.intersection(vec![existing, ns_interned])
            } else {
              ns_interned
            };
            self.interned_def_types.insert(def, merged);
          }
        }
        _ => {}
      }
    }
    self.type_stack.pop();
    let ret_ty = if let Some(store) = self.interned_store.as_ref() {
      let interned = self.interned_def_types.get(&def).copied().unwrap_or(ty);
      let prefer_named = match &def_data.kind {
        DefKind::Interface(_) | DefKind::TypeAlias(_) => false,
        DefKind::Import(import) if import.is_type_only => false,
        _ => true,
      };
      let preferred = if prefer_named {
        self.prefer_named_refs_in_store(store, interned)
      } else {
        interned
      };
      self.interned_def_types.insert(def, preferred);
      let imported = self.import_interned_type(preferred);
      self.def_types.insert(def, imported);
      preferred
    } else {
      self.def_types.insert(def, ty);
      ty
    };
    if let Some(span) = span.take() {
      span.finish(Some(ret_ty));
    }
    self.current_file = prev_file;
    ret_ty
  }

  fn function_type(&mut self, def: DefId, func: FuncData) -> TypeId {
    let param_types: Vec<TypeId> = func
      .params
      .iter()
      .map(|p| p.typ.unwrap_or(self.builtin.any))
      .collect();
    let ret = if let Some(ret) = func.return_ann {
      ret
    } else if let Some(body) = func.body {
      let res = self.check_body(body);
      if res.return_types.is_empty() {
        self.builtin.void
      } else {
        let mut widened = Vec::new();
        for ty in res.return_types.iter() {
          let imported = self.import_interned_type(*ty);
          widened.push(self.widen_literal(imported));
        }
        self.type_store.union(widened, &self.builtin)
      }
    } else {
      self.builtin.unknown
    };
    let ty = self.type_store.function(param_types, ret);
    if let Some(store) = self.interned_store.as_ref() {
      let mut cache = HashMap::new();
      let interned = convert_type_for_display(ty, self, store, &mut cache);
      let interned = store.canon(interned);
      self
        .interned_def_types
        .entry(def)
        .and_modify(|existing| {
          *existing = ProgramState::merge_interned_decl_types(store, *existing, interned);
        })
        .or_insert(interned);
    }
    self.def_types.insert(def, ty);
    ty
  }

  fn exports_of_file(&mut self, file: FileId) -> ExportMap {
    let mut map = if let Some(semantics) = self.semantics.clone() {
      check::modules::exports_from_semantics(self, &semantics, file)
    } else {
      ExportMap::new()
    };
    if let Some(state) = self.files.get(&file).cloned() {
      for (name, entry) in state.exports.iter() {
        let mapped = map.entry(name.clone()).or_insert_with(|| entry.clone());
        if mapped.def.is_none() {
          mapped.def = entry.def;
        }
        if mapped.type_id.is_none() {
          mapped.type_id = entry.type_id;
        }
      }
    }
    for entry in map.values_mut() {
      if entry.type_id.is_none() {
        entry.type_id = entry.def.and_then(|def| self.export_type_for_def(def));
      }
    }
    map
  }

  fn ensure_symbols_for_file(&mut self, file: FileId) {
    if let Some(state) = self.files.get(&file).cloned() {
      let mut bodies_to_cover = Vec::new();
      if let Some(body) = state.top_body {
        bodies_to_cover.push(body);
      }
      for def in state.defs.iter() {
        if let Some(body) = self.body_of_def(*def) {
          bodies_to_cover.push(body);
        }
      }
      for body in bodies_to_cover.iter().copied() {
        let _ = self.check_body(body);
      }
      for body in bodies_to_cover.iter().copied() {
        if let Some(result) = self.body_results.get(&body) {
          let spans: Vec<_> = result.pat_spans().to_vec();
          for span in spans {
            let exists = {
              let occs = self.symbol_occurrences.entry(file).or_default();
              occs.iter().any(|occ| occ.range == span)
            };
            if exists {
              continue;
            }
            let symbol = self.alloc_symbol();
            self
              .symbol_occurrences
              .entry(file)
              .or_default()
              .push(SymbolOccurrence {
                range: span,
                symbol,
              });
          }
        }
      }
      self.record_type_references(file, &state.bindings);
    }
  }

  fn record_type_references(&mut self, file: FileId, bindings: &HashMap<String, SymbolBinding>) {
    let Some(ast) = self.asts.get(&file).cloned() else {
      return;
    };
    for stmt in ast.stx.body.iter() {
      self.record_type_annotations_in_stmt(file, bindings, stmt);
    }
  }

  fn record_type_annotations_in_stmt(
    &mut self,
    file: FileId,
    bindings: &HashMap<String, SymbolBinding>,
    stmt: &Node<Stmt>,
  ) {
    match stmt.stx.as_ref() {
      Stmt::TypeAliasDecl(alias) => {
        self.record_type_expr_symbols(file, &alias.stx.type_expr, bindings);
      }
      Stmt::FunctionDecl(func) => {
        for param in func.stx.function.stx.parameters.iter() {
          if let Some(ann) = param.stx.type_annotation.as_ref() {
            self.record_type_expr_symbols(file, ann, bindings);
          }
        }
        if let Some(ret) = func.stx.function.stx.return_type.as_ref() {
          self.record_type_expr_symbols(file, ret, bindings);
        }
        if let Some(body) = func.stx.function.stx.body.as_ref() {
          if let parse_js::ast::func::FuncBody::Block(stmts) = body {
            for stmt in stmts.iter() {
              self.record_type_annotations_in_stmt(file, bindings, stmt);
            }
          }
        }
      }
      Stmt::VarDecl(var) => {
        for decl in var.stx.declarators.iter() {
          if let Some(ann) = decl.type_annotation.as_ref() {
            self.record_type_expr_symbols(file, ann, bindings);
          }
        }
      }
      Stmt::Block(block) => {
        for stmt in block.stx.body.iter() {
          self.record_type_annotations_in_stmt(file, bindings, stmt);
        }
      }
      _ => {}
    }
  }

  fn record_type_expr_symbols(
    &mut self,
    file: FileId,
    expr: &Node<TypeExpr>,
    bindings: &HashMap<String, SymbolBinding>,
  ) {
    match expr.stx.as_ref() {
      TypeExpr::TypeReference(reference) => {
        if let TypeEntityName::Identifier(name) = &reference.stx.name {
          if let Some(binding) = bindings.get(name) {
            let span = loc_to_span(file, reference.loc).range;
            if self
              .symbol_occurrences
              .get(&file)
              .map(|occs| occs.iter().any(|occ| occ.range == span))
              .unwrap_or(false)
            {
              // Already recorded.
              return;
            }
            self.record_symbol(file, span, binding.symbol);
          }
        }
        if let Some(args) = reference.stx.type_arguments.as_ref() {
          for arg in args.iter() {
            self.record_type_expr_symbols(file, arg, bindings);
          }
        }
      }
      TypeExpr::ArrayType(arr) => {
        self.record_type_expr_symbols(file, &arr.stx.element_type, bindings);
      }
      TypeExpr::TupleType(tuple) => {
        for elem in tuple.stx.elements.iter() {
          self.record_type_expr_symbols(file, &elem.stx.type_expr, bindings);
        }
      }
      TypeExpr::UnionType(union) => {
        for member in union.stx.types.iter() {
          self.record_type_expr_symbols(file, member, bindings);
        }
      }
      TypeExpr::IntersectionType(inter) => {
        for member in inter.stx.types.iter() {
          self.record_type_expr_symbols(file, member, bindings);
        }
      }
      TypeExpr::ParenthesizedType(inner) => {
        self.record_type_expr_symbols(file, &inner.stx.type_expr, bindings);
      }
      TypeExpr::ObjectType(obj) => {
        for member in obj.stx.members.iter() {
          match member.stx.as_ref() {
            TypeMember::Property(prop) => {
              if let Some(ann) = prop.stx.type_annotation.as_ref() {
                self.record_type_expr_symbols(file, ann, bindings);
              }
            }
            TypeMember::Method(method) => {
              for param in method.stx.parameters.iter() {
                self.record_type_expr_symbols(file, &param.stx.type_expr, bindings);
              }
              if let Some(ret) = method.stx.return_type.as_ref() {
                self.record_type_expr_symbols(file, ret, bindings);
              }
            }
            TypeMember::CallSignature(sig) => {
              for param in sig.stx.parameters.iter() {
                self.record_type_expr_symbols(file, &param.stx.type_expr, bindings);
              }
              if let Some(ret) = sig.stx.return_type.as_ref() {
                self.record_type_expr_symbols(file, ret, bindings);
              }
            }
            TypeMember::Constructor(sig) => {
              for param in sig.stx.parameters.iter() {
                self.record_type_expr_symbols(file, &param.stx.type_expr, bindings);
              }
              if let Some(ret) = sig.stx.return_type.as_ref() {
                self.record_type_expr_symbols(file, ret, bindings);
              }
            }
            TypeMember::IndexSignature(index) => {
              self.record_type_expr_symbols(file, &index.stx.parameter_type, bindings);
              self.record_type_expr_symbols(file, &index.stx.type_annotation, bindings);
            }
            _ => {}
          }
        }
      }
      _ => {}
    }
  }

  fn symbol_at(&mut self, file: FileId, offset: u32) -> Option<semantic_js::SymbolId> {
    if let Some(occurrences) = self.symbol_occurrences.get(&file) {
      let mut best_containing: Option<(u32, u32, semantic_js::SymbolId)> = None;
      let mut best_empty: Option<(u32, u32, semantic_js::SymbolId)> = None;

      for occurrence in occurrences.iter() {
        let range = occurrence.range;
        let len = range.len();
        let key = (len, range.start, occurrence.symbol);
        if range.start <= offset && offset < range.end {
          let replace = best_containing.map(|best| key < best).unwrap_or(true);
          if replace {
            best_containing = Some(key);
          }
        } else if range.start == range.end && offset == range.start {
          let replace = best_empty.map(|best| key < best).unwrap_or(true);
          if replace {
            best_empty = Some(key);
          }
        }
      }

      if let Some(symbol) = best_containing
        .or(best_empty)
        .map(|(_, _, symbol)| symbol)
        .map(|symbol| self.resolve_symbol(symbol))
      {
        return Some(symbol);
      }
    }

    let (body, expr) = self.expr_at(file, offset)?;
    let meta = self.body_map.get(&body).copied()?;
    let lowered = self.hir_lowered.get(&meta.file).cloned()?;
    self
      .resolve_symbol_in_body(file, &lowered, body, meta, expr)
      .map(|symbol| self.resolve_symbol(symbol))
  }

  fn resolve_symbol(&mut self, symbol: semantic_js::SymbolId) -> semantic_js::SymbolId {
    let import = self
      .symbol_to_def
      .get(&symbol)
      .and_then(|def| self.def_data.get(def))
      .and_then(|d| match &d.kind {
        DefKind::Import(import) => Some(import.clone()),
        _ => None,
      });

    if let Some(import) = import {
      if let Some(resolved) = self.resolve_import_symbol(&import) {
        return resolved;
      }
    }

    symbol
  }

  fn resolve_import_symbol(&mut self, import: &ImportData) -> Option<semantic_js::SymbolId> {
    if let Some(from) = import.from {
      if let Some(entry) = self.exports_of_file(from).get(&import.original) {
        return Some(entry.symbol);
      }
    }
    if let Some(semantics) = self.semantics.as_ref() {
      if let Some(exports) = semantics.exports_of_ambient_module(&import.specifier) {
        let symbols = semantics.symbols();
        let ns = if import.is_type_only {
          sem_ts::Namespace::TYPE
        } else {
          sem_ts::Namespace::VALUE
        };
        if let Some(group) = exports.get(&import.original) {
          if let Some(symbol) = group.symbol_for(ns, symbols) {
            return Some(symbol.into());
          }
        }
      }
    }
    None
  }

  fn resolve_import_entry(&mut self, import: &ImportData) -> Option<ExportEntry> {
    let trace = std::env::var("TRACE_AMBIENT").is_ok();
    if trace {
      eprintln!(
        "[resolve_import_entry] specifier={} original={} from={:?} type_only={}",
        import.specifier, import.original, import.from, import.is_type_only
      );
    }
    if let Some(from) = import.from {
      if let Some(entry) = self.exports_of_file(from).get(&import.original) {
        if trace {
          eprintln!(
            "[resolve_import_entry] resolved via file {:?} -> symbol {:?} def {:?} type {:?}",
            from, entry.symbol, entry.def, entry.type_id
          );
        }
        return Some(entry.clone());
      }
    }
    if let Some(semantics) = self.semantics.as_ref() {
      if let Some(exports) = semantics.exports_of_ambient_module(&import.specifier) {
        let symbols = semantics.symbols();
        let ns = if import.is_type_only {
          sem_ts::Namespace::TYPE
        } else {
          sem_ts::Namespace::VALUE
        };
        if let Some(group) = exports.get(&import.original) {
          if let Some(symbol) = group.symbol_for(ns, symbols) {
            let public: semantic_js::SymbolId = symbol.into();
            let mut def = self.symbol_to_def.get(&public).copied();
            let sem_def = semantics
              .symbol_decls(symbol, ns)
              .first()
              .map(|decl| symbols.decl(*decl).def_id)
              .filter(|decl_def| self.def_data.contains_key(decl_def));
            if def.is_none() {
              def = sem_def;
            }
            let mut type_id = def
              .and_then(|d| self.def_types.get(&d).copied())
              .or_else(|| {
                def
                  .and_then(|d| self.interned_def_types.get(&d).copied())
                  .map(|interned| self.import_interned_type(interned))
              });
            if type_id.is_none() {
              if let Some(sem_def) = sem_def {
                type_id = self.def_types.get(&sem_def).copied().or_else(|| {
                  self
                    .interned_def_types
                    .get(&sem_def)
                    .copied()
                    .map(|interned| self.import_interned_type(interned))
                });
              }
            }
            if trace {
              eprintln!(
                "[resolve_import_entry] ambient {} -> symbol {:?} def {:?} type {:?}",
                import.specifier, public, def, type_id
              );
            }
            return Some(ExportEntry {
              symbol: public,
              def,
              type_id,
            });
          }
        }
      }
    }
    if trace {
      eprintln!(
        "[resolve_import_entry] unresolved import {} from {:?}",
        import.original, import.from
      );
    }
    None
  }

  fn resolve_symbol_in_body(
    &mut self,
    file: FileId,
    lowered: &LowerResult,
    prog_body: BodyId,
    meta: BodyMeta,
    target_expr: hir_js::ExprId,
  ) -> Option<semantic_js::SymbolId> {
    let hir_body = meta.hir?;
    let body = lowered.body(hir_body)?;
    let target_span = body.exprs.get(target_expr.0 as usize)?.span;

    let mut def_symbols: HashMap<TextRange, semantic_js::SymbolId> = self
      .def_data
      .values()
      .filter(|d| d.file == file)
      .map(|d| (d.span, d.symbol))
      .collect();

    let mut initial_scope: HashMap<String, semantic_js::SymbolId> = HashMap::new();
    if let Some(state) = self.files.get(&file) {
      for (name, binding) in state.bindings.iter() {
        initial_scope.insert(name.clone(), binding.symbol);
      }
    }
    for (name, binding) in self.global_bindings.iter() {
      initial_scope.entry(name.clone()).or_insert(binding.symbol);
    }

    fn lookup(
      scopes: &[HashMap<String, semantic_js::SymbolId>],
      name: &str,
    ) -> Option<semantic_js::SymbolId> {
      for scope in scopes.iter().rev() {
        if let Some(symbol) = scope.get(name) {
          return Some(*symbol);
        }
      }
      None
    }

    fn bind_pat(
      state: &mut ProgramState,
      body: &hir_js::Body,
      names: &hir_js::NameInterner,
      pat_id: HirPatId,
      scopes: &mut Vec<HashMap<String, semantic_js::SymbolId>>,
      def_symbols: &mut HashMap<TextRange, semantic_js::SymbolId>,
      file: FileId,
    ) {
      let Some(pat) = body.pats.get(pat_id.0 as usize) else {
        return;
      };
      match &pat.kind {
        HirPatKind::Ident(name_id) => {
          if let Some(name) = names.resolve(*name_id) {
            let symbol = def_symbols
              .get(&pat.span)
              .copied()
              .or_else(|| {
                state.symbol_occurrences.get(&file).and_then(|occs| {
                  occs
                    .iter()
                    .find(|occ| occ.range == pat.span)
                    .map(|occ| occ.symbol)
                })
              })
              .unwrap_or_else(|| state.alloc_symbol());
            if let Some(scope) = scopes.last_mut() {
              scope.insert(name.to_string(), symbol);
            }
            def_symbols.insert(pat.span, symbol);
            state.record_symbol(file, pat.span, symbol);
          }
        }
        HirPatKind::Array(arr) => {
          for elem in arr.elements.iter().flatten() {
            bind_pat(state, body, names, elem.pat, scopes, def_symbols, file);
          }
          if let Some(rest) = arr.rest {
            bind_pat(state, body, names, rest, scopes, def_symbols, file);
          }
        }
        HirPatKind::Object(obj) => {
          for prop in obj.props.iter() {
            bind_pat(state, body, names, prop.value, scopes, def_symbols, file);
          }
          if let Some(rest) = obj.rest {
            bind_pat(state, body, names, rest, scopes, def_symbols, file);
          }
        }
        HirPatKind::Rest(inner) => {
          bind_pat(state, body, names, **inner, scopes, def_symbols, file);
        }
        HirPatKind::Assign { target, .. } => {
          bind_pat(state, body, names, *target, scopes, def_symbols, file);
        }
        HirPatKind::AssignTarget(_) => {}
      }
    }

    fn walk_expr(
      state: &mut ProgramState,
      lowered: &LowerResult,
      body: &hir_js::Body,
      names: &hir_js::NameInterner,
      expr_id: hir_js::ExprId,
      target: hir_js::ExprId,
      target_span: TextRange,
      scopes: &mut Vec<HashMap<String, semantic_js::SymbolId>>,
      def_symbols: &mut HashMap<TextRange, semantic_js::SymbolId>,
      file: FileId,
    ) -> Option<semantic_js::SymbolId> {
      let Some(expr) = body.exprs.get(expr_id.0 as usize) else {
        return None;
      };
      if expr_id == target {
        if let HirExprKind::Ident(name_id) = expr.kind {
          if let Some(name) = names.resolve(name_id) {
            if let Some(symbol) = lookup(scopes, name) {
              let occs = state.symbol_occurrences.entry(file).or_default();
              if !occs
                .iter()
                .any(|occ| occ.range == target_span && occ.symbol == symbol)
              {
                occs.push(SymbolOccurrence {
                  range: target_span,
                  symbol,
                });
              }
              return Some(symbol);
            }
          }
        }
      }
      match &expr.kind {
        HirExprKind::Ident(_) | HirExprKind::This | HirExprKind::Super => None,
        HirExprKind::Literal(_) => None,
        HirExprKind::Unary { expr, .. } => walk_expr(
          state,
          lowered,
          body,
          names,
          *expr,
          target,
          target_span,
          scopes,
          def_symbols,
          file,
        ),
        HirExprKind::Update { expr, .. } => walk_expr(
          state,
          lowered,
          body,
          names,
          *expr,
          target,
          target_span,
          scopes,
          def_symbols,
          file,
        ),
        HirExprKind::Binary { left, right, .. } => walk_expr(
          state,
          lowered,
          body,
          names,
          *left,
          target,
          target_span,
          scopes,
          def_symbols,
          file,
        )
        .or_else(|| {
          walk_expr(
            state,
            lowered,
            body,
            names,
            *right,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          )
        }),
        HirExprKind::Assignment {
          target: pat, value, ..
        } => {
          bind_pat(state, body, names, *pat, scopes, def_symbols, file);
          walk_expr(
            state,
            lowered,
            body,
            names,
            *value,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          )
        }
        HirExprKind::Call(call) => {
          let mut found = walk_expr(
            state,
            lowered,
            body,
            names,
            call.callee,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          );
          if found.is_some() {
            return found;
          }
          for arg in call.args.iter() {
            found = walk_expr(
              state,
              lowered,
              body,
              names,
              arg.expr,
              target,
              target_span,
              scopes,
              def_symbols,
              file,
            );
            if found.is_some() {
              return found;
            }
          }
          found
        }
        HirExprKind::Member(member) => walk_expr(
          state,
          lowered,
          body,
          names,
          member.object,
          target,
          target_span,
          scopes,
          def_symbols,
          file,
        ),
        HirExprKind::Conditional {
          test,
          consequent,
          alternate,
        } => walk_expr(
          state,
          lowered,
          body,
          names,
          *test,
          target,
          target_span,
          scopes,
          def_symbols,
          file,
        )
        .or_else(|| {
          walk_expr(
            state,
            lowered,
            body,
            names,
            *consequent,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          )
        })
        .or_else(|| {
          walk_expr(
            state,
            lowered,
            body,
            names,
            *alternate,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          )
        }),
        HirExprKind::Array(array) => {
          for element in array.elements.iter() {
            let expr = match element {
              hir_js::ArrayElement::Expr(expr) | hir_js::ArrayElement::Spread(expr) => Some(*expr),
              hir_js::ArrayElement::Empty => None,
            };
            if let Some(expr) = expr {
              if let Some(found) = walk_expr(
                state,
                lowered,
                body,
                names,
                expr,
                target,
                target_span,
                scopes,
                def_symbols,
                file,
              ) {
                return Some(found);
              }
            }
          }
          None
        }
        HirExprKind::Object(obj) => {
          for prop in obj.properties.iter() {
            match prop {
              hir_js::ObjectProperty::KeyValue { value, .. } => {
                if let Some(found) = walk_expr(
                  state,
                  lowered,
                  body,
                  names,
                  *value,
                  target,
                  target_span,
                  scopes,
                  def_symbols,
                  file,
                ) {
                  return Some(found);
                }
              }
              hir_js::ObjectProperty::Spread(expr) => {
                if let Some(found) = walk_expr(
                  state,
                  lowered,
                  body,
                  names,
                  *expr,
                  target,
                  target_span,
                  scopes,
                  def_symbols,
                  file,
                ) {
                  return Some(found);
                }
              }
              hir_js::ObjectProperty::Getter { .. } | hir_js::ObjectProperty::Setter { .. } => {}
            }
          }
          None
        }
        HirExprKind::Template(tmpl) => {
          for span in tmpl.spans.iter() {
            if let Some(found) = walk_expr(
              state,
              lowered,
              body,
              names,
              span.expr,
              target,
              target_span,
              scopes,
              def_symbols,
              file,
            ) {
              return Some(found);
            }
          }
          None
        }
        HirExprKind::FunctionExpr { .. } | HirExprKind::ClassExpr { .. } => None,
        _ => None,
      }
    }

    fn walk_stmt(
      state: &mut ProgramState,
      lowered: &LowerResult,
      body: &hir_js::Body,
      names: &hir_js::NameInterner,
      stmt_id: hir_js::StmtId,
      target: hir_js::ExprId,
      target_span: TextRange,
      scopes: &mut Vec<HashMap<String, semantic_js::SymbolId>>,
      def_symbols: &mut HashMap<TextRange, semantic_js::SymbolId>,
      file: FileId,
    ) -> Option<semantic_js::SymbolId> {
      let Some(stmt) = body.stmts.get(stmt_id.0 as usize) else {
        return None;
      };
      match &stmt.kind {
        HirStmtKind::Expr(expr) => walk_expr(
          state,
          lowered,
          body,
          names,
          *expr,
          target,
          target_span,
          scopes,
          def_symbols,
          file,
        ),
        HirStmtKind::Return(expr) => expr.and_then(|e| {
          walk_expr(
            state,
            lowered,
            body,
            names,
            e,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          )
        }),
        HirStmtKind::Block(stmts) => {
          scopes.push(HashMap::new());
          for stmt in stmts.iter() {
            if let Some(found) = walk_stmt(
              state,
              lowered,
              body,
              names,
              *stmt,
              target,
              target_span,
              scopes,
              def_symbols,
              file,
            ) {
              scopes.pop();
              return Some(found);
            }
          }
          scopes.pop();
          None
        }
        HirStmtKind::If {
          test,
          consequent,
          alternate,
        } => walk_expr(
          state,
          lowered,
          body,
          names,
          *test,
          target,
          target_span,
          scopes,
          def_symbols,
          file,
        )
        .or_else(|| {
          walk_stmt(
            state,
            lowered,
            body,
            names,
            *consequent,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          )
        })
        .or_else(|| {
          alternate.and_then(|alt| {
            walk_stmt(
              state,
              lowered,
              body,
              names,
              alt,
              target,
              target_span,
              scopes,
              def_symbols,
              file,
            )
          })
        }),
        HirStmtKind::While { test, body: inner } => walk_expr(
          state,
          lowered,
          body,
          names,
          *test,
          target,
          target_span,
          scopes,
          def_symbols,
          file,
        )
        .or_else(|| {
          walk_stmt(
            state,
            lowered,
            body,
            names,
            *inner,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          )
        }),
        HirStmtKind::DoWhile { body: inner, test } => walk_stmt(
          state,
          lowered,
          body,
          names,
          *inner,
          target,
          target_span,
          scopes,
          def_symbols,
          file,
        )
        .or_else(|| {
          walk_expr(
            state,
            lowered,
            body,
            names,
            *test,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          )
        }),
        HirStmtKind::For {
          init,
          test,
          update,
          body: inner,
        } => {
          if let Some(init) = init {
            match init {
              hir_js::ForInit::Expr(expr) => {
                if let Some(found) = walk_expr(
                  state,
                  lowered,
                  body,
                  names,
                  *expr,
                  target,
                  target_span,
                  scopes,
                  def_symbols,
                  file,
                ) {
                  return Some(found);
                }
              }
              hir_js::ForInit::Var(var) => {
                for decl in var.declarators.iter() {
                  bind_pat(state, body, names, decl.pat, scopes, def_symbols, file);
                  if let Some(init) = decl.init {
                    if let Some(found) = walk_expr(
                      state,
                      lowered,
                      body,
                      names,
                      init,
                      target,
                      target_span,
                      scopes,
                      def_symbols,
                      file,
                    ) {
                      return Some(found);
                    }
                  }
                }
              }
            }
          }
          if let Some(test) = test {
            if let Some(found) = walk_expr(
              state,
              lowered,
              body,
              names,
              *test,
              target,
              target_span,
              scopes,
              def_symbols,
              file,
            ) {
              return Some(found);
            }
          }
          if let Some(update) = update {
            if let Some(found) = walk_expr(
              state,
              lowered,
              body,
              names,
              *update,
              target,
              target_span,
              scopes,
              def_symbols,
              file,
            ) {
              return Some(found);
            }
          }
          walk_stmt(
            state,
            lowered,
            body,
            names,
            *inner,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          )
        }
        HirStmtKind::ForIn {
          left,
          right,
          body: inner,
          ..
        } => {
          match left {
            hir_js::ForHead::Pat(pat) => {
              bind_pat(state, body, names, *pat, scopes, def_symbols, file)
            }
            hir_js::ForHead::Var(var) => {
              for decl in var.declarators.iter() {
                bind_pat(state, body, names, decl.pat, scopes, def_symbols, file);
              }
            }
          }
          if let Some(found) = walk_expr(
            state,
            lowered,
            body,
            names,
            *right,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          ) {
            return Some(found);
          }
          walk_stmt(
            state,
            lowered,
            body,
            names,
            *inner,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          )
        }
        HirStmtKind::Switch {
          discriminant,
          cases,
        } => {
          if let Some(found) = walk_expr(
            state,
            lowered,
            body,
            names,
            *discriminant,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          ) {
            return Some(found);
          }
          for case in cases.iter() {
            if let Some(test) = case.test {
              if let Some(found) = walk_expr(
                state,
                lowered,
                body,
                names,
                test,
                target,
                target_span,
                scopes,
                def_symbols,
                file,
              ) {
                return Some(found);
              }
            }
            for stmt in case.consequent.iter() {
              if let Some(found) = walk_stmt(
                state,
                lowered,
                body,
                names,
                *stmt,
                target,
                target_span,
                scopes,
                def_symbols,
                file,
              ) {
                return Some(found);
              }
            }
          }
          None
        }
        HirStmtKind::Try {
          block,
          catch,
          finally_block,
        } => {
          if let Some(found) = walk_stmt(
            state,
            lowered,
            body,
            names,
            *block,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          ) {
            return Some(found);
          }
          if let Some(catch) = catch {
            if let Some(param) = catch.param {
              bind_pat(state, body, names, param, scopes, def_symbols, file);
            }
            if let Some(found) = walk_stmt(
              state,
              lowered,
              body,
              names,
              catch.body,
              target,
              target_span,
              scopes,
              def_symbols,
              file,
            ) {
              return Some(found);
            }
          }
          if let Some(finally_block) = finally_block {
            return walk_stmt(
              state,
              lowered,
              body,
              names,
              *finally_block,
              target,
              target_span,
              scopes,
              def_symbols,
              file,
            );
          }
          None
        }
        HirStmtKind::Throw(expr) => walk_expr(
          state,
          lowered,
          body,
          names,
          *expr,
          target,
          target_span,
          scopes,
          def_symbols,
          file,
        ),
        HirStmtKind::Var(var) => {
          for decl in var.declarators.iter() {
            bind_pat(state, body, names, decl.pat, scopes, def_symbols, file);
            if let Some(init) = decl.init {
              if let Some(found) = walk_expr(
                state,
                lowered,
                body,
                names,
                init,
                target,
                target_span,
                scopes,
                def_symbols,
                file,
              ) {
                return Some(found);
              }
            }
          }
          None
        }
        HirStmtKind::Labeled { body: inner, .. } => walk_stmt(
          state,
          lowered,
          body,
          names,
          *inner,
          target,
          target_span,
          scopes,
          def_symbols,
          file,
        ),
        HirStmtKind::With {
          object,
          body: inner,
        } => walk_expr(
          state,
          lowered,
          body,
          names,
          *object,
          target,
          target_span,
          scopes,
          def_symbols,
          file,
        )
        .or_else(|| {
          walk_stmt(
            state,
            lowered,
            body,
            names,
            *inner,
            target,
            target_span,
            scopes,
            def_symbols,
            file,
          )
        }),
        HirStmtKind::Decl(def_id) => {
          if let Some(def) = lowered.def(*def_id) {
            if let Some(name) = names.resolve(def.name) {
              let symbol = def_symbols
                .get(&def.span)
                .copied()
                .or_else(|| {
                  state.symbol_occurrences.get(&file).and_then(|occs| {
                    occs
                      .iter()
                      .find(|occ| occ.range == def.span)
                      .map(|occ| occ.symbol)
                  })
                })
                .unwrap_or_else(|| state.alloc_symbol());
              if let Some(scope) = scopes.last_mut() {
                scope.insert(name.to_string(), symbol);
              }
              def_symbols.insert(def.span, symbol);
              state.record_symbol(file, def.span, symbol);
            }
          }
          None
        }
        HirStmtKind::Empty | HirStmtKind::Break(_) | HirStmtKind::Continue(_) => None,
      }
    }

    fn walk_body(
      state: &mut ProgramState,
      lowered: &LowerResult,
      body_id: hir_js::BodyId,
      target: hir_js::ExprId,
      target_span: TextRange,
      scopes: &mut Vec<HashMap<String, semantic_js::SymbolId>>,
      def_symbols: &mut HashMap<TextRange, semantic_js::SymbolId>,
      file: FileId,
    ) -> Option<semantic_js::SymbolId> {
      let Some(body) = lowered.body(body_id) else {
        return None;
      };
      let names = lowered.names.as_ref();
      if matches!(body.kind, HirBodyKind::Function) {
        if let Some(func) = body.function.as_ref() {
          for param in func.params.iter() {
            bind_pat(state, body, names, param.pat, scopes, def_symbols, file);
          }
        }
      }
      let stmts_to_visit: Vec<hir_js::StmtId> = if body.root_stmts.is_empty() {
        let mut referenced: HashSet<hir_js::StmtId> = HashSet::new();
        for stmt in body.stmts.iter() {
          match &stmt.kind {
            HirStmtKind::Block(stmts) => referenced.extend(stmts.iter().copied()),
            HirStmtKind::If {
              consequent,
              alternate,
              ..
            } => {
              referenced.insert(*consequent);
              if let Some(alt) = alternate {
                referenced.insert(*alt);
              }
            }
            HirStmtKind::While { body, .. }
            | HirStmtKind::DoWhile { body, .. }
            | HirStmtKind::For { body, .. }
            | HirStmtKind::Labeled { body, .. }
            | HirStmtKind::With { body, .. } => {
              referenced.insert(*body);
            }
            HirStmtKind::ForIn { body, .. } => {
              referenced.insert(*body);
            }
            HirStmtKind::Switch { cases, .. } => {
              for case in cases.iter() {
                referenced.extend(case.consequent.iter().copied());
              }
            }
            HirStmtKind::Try {
              block,
              catch,
              finally_block,
            } => {
              referenced.insert(*block);
              if let Some(catch) = catch {
                referenced.insert(catch.body);
              }
              if let Some(finally_block) = finally_block {
                referenced.insert(*finally_block);
              }
            }
            _ => {}
          }
        }
        let mut roots: Vec<_> = (0..body.stmts.len())
          .map(|idx| hir_js::StmtId(idx as u32))
          .filter(|id| !referenced.contains(id))
          .collect();
        roots.sort_by_key(|id| {
          body
            .stmts
            .get(id.0 as usize)
            .map(|s| s.span.start)
            .unwrap_or(0)
        });
        roots
      } else {
        body.root_stmts.clone()
      };
      for stmt in stmts_to_visit.iter() {
        if let Some(found) = walk_stmt(
          state,
          lowered,
          body,
          names,
          *stmt,
          target,
          target_span,
          scopes,
          def_symbols,
          file,
        ) {
          return Some(found);
        }
      }
      walk_expr(
        state,
        lowered,
        body,
        names,
        target,
        target,
        target_span,
        scopes,
        def_symbols,
        file,
      )
    }

    let mut scopes = vec![initial_scope];
    let mut parent_chain = Vec::new();
    let mut current = self.body_parents.get(&prog_body).copied();
    let mut visited = HashSet::new();
    while let Some(parent) = current {
      if !visited.insert(parent) {
        break;
      }
      parent_chain.push(parent);
      current = self.body_parents.get(&parent).copied();
    }
    for parent in parent_chain.into_iter().rev() {
      let Some(meta) = self.body_map.get(&parent).copied() else {
        continue;
      };
      let Some(hir_id) = meta.hir else {
        continue;
      };
      let Some(lowered) = self.hir_lowered.get(&meta.file).cloned() else {
        continue;
      };
      let Some(body) = lowered.body(hir_id) else {
        continue;
      };
      let names = lowered.names.clone();
      scopes.push(HashMap::new());
      for (idx, _) in body.pats.iter().enumerate() {
        bind_pat(
          self,
          body,
          &names,
          HirPatId(idx as u32),
          &mut scopes,
          &mut def_symbols,
          meta.file,
        );
      }
    }
    walk_body(
      self,
      lowered,
      hir_body,
      target_expr,
      target_span,
      &mut scopes,
      &mut def_symbols,
      file,
    )
  }

  fn symbol_info(&self, symbol: semantic_js::SymbolId) -> Option<SymbolInfo> {
    let binding = self
      .global_bindings
      .iter()
      .find(|(_, binding)| binding.symbol == symbol);

    let def = self
      .symbol_to_def
      .get(&symbol)
      .copied()
      .or_else(|| binding.as_ref().and_then(|(_, b)| b.def));
    let type_id = def
      .and_then(|def_id| self.def_types.get(&def_id).copied())
      .or_else(|| binding.as_ref().and_then(|(_, b)| b.type_id));
    let mut name = def
      .and_then(|def_id| self.def_data.get(&def_id).map(|data| data.name.clone()))
      .or_else(|| binding.as_ref().map(|(name, _)| name.to_string()));
    let file = def.and_then(|def_id| self.def_data.get(&def_id).map(|data| data.file));
    let span = def.and_then(|def_id| self.def_data.get(&def_id).map(|data| data.span));

    if def.is_none() && type_id.is_none() && name.is_none() {
      return None;
    }
    if name.is_none() {
      name = binding.as_ref().map(|(name, _)| name.to_string());
    }

    Some(SymbolInfo {
      symbol,
      def,
      file,
      type_id,
      name,
      span,
    })
  }

  fn expr_at(&self, file: FileId, offset: u32) -> Option<(BodyId, ExprId)> {
    fn body_priority(kind: HirBodyKind) -> u32 {
      match kind {
        HirBodyKind::Function | HirBodyKind::Class => 0,
        HirBodyKind::TopLevel => 1,
        HirBodyKind::Initializer => 2,
        HirBodyKind::Unknown => 3,
      }
    }

    let mut best_containing: Option<(u32, u32, u32, u32, BodyId, ExprId)> = None;
    let mut best_empty: Option<(u32, u32, u32, u32, BodyId, ExprId)> = None;

    let update_best =
      |body: BodyId,
       kind: HirBodyKind,
       expr: ExprId,
       span: TextRange,
       best_containing: &mut Option<(u32, u32, u32, u32, BodyId, ExprId)>,
       best_empty: &mut Option<(u32, u32, u32, u32, BodyId, ExprId)>| {
        let len = span.len();
        let priority = body_priority(kind);
        let parent_rank = if self.body_parents.contains_key(&body) {
          0
        } else {
          1
        };
        let key = (priority, parent_rank, len, span.start, body, expr);
        if span.start <= offset && offset < span.end {
          let replace = best_containing.map(|best| key < best).unwrap_or(true);
          if replace {
            *best_containing = Some(key);
          }
        } else if span.start == span.end && offset == span.start {
          let replace = best_empty.map(|best| key < best).unwrap_or(true);
          if replace {
            *best_empty = Some(key);
          }
        }
      };

    for (body_id, meta) in self.body_map.iter().filter(|(_, meta)| meta.file == file) {
      if let Some(result) = self.body_results.get(body_id) {
        for (idx, span) in result.expr_spans().iter().enumerate() {
          update_best(
            *body_id,
            meta.kind,
            ExprId(idx as u32),
            *span,
            &mut best_containing,
            &mut best_empty,
          );
        }
        continue;
      }

      if let Some(hir_id) = meta.hir {
        if let Some(lowered) = self.hir_lowered.get(&meta.file) {
          if let Some(body) = lowered.body(hir_id) {
            for (idx, expr) in body.exprs.iter().enumerate() {
              update_best(
                *body_id,
                meta.kind,
                ExprId(idx as u32),
                expr.span,
                &mut best_containing,
                &mut best_empty,
              );
            }
          }
        }
      }
    }

    best_containing
      .or(best_empty)
      .map(|(_, _, _, _, body, expr)| (body, expr))
  }

  fn body_of_def(&self, def: DefId) -> Option<BodyId> {
    self.def_data.get(&def).and_then(|d| match &d.kind {
      DefKind::Function(func) => func.body,
      DefKind::Var(var) => Some(var.body),
      DefKind::Import(_) => None,
      DefKind::Interface(_) => None,
      DefKind::TypeAlias(_) => None,
    })
  }

  fn owner_of_body(&self, body: BodyId) -> Option<DefId> {
    for (def_id, data) in self.def_data.iter() {
      match &data.kind {
        DefKind::Function(func) if func.body == Some(body) => return Some(*def_id),
        DefKind::Var(var) if var.body == body => return Some(*def_id),
        _ => {}
      }
    }
    None
  }

  fn object_type_from_members(&mut self, members: &[Node<TypeMember>]) -> ObjectType {
    let mut object = ObjectType::empty();
    for member in members.iter() {
      match member.stx.as_ref() {
        TypeMember::Property(prop) => {
          if let Some(name) = type_member_name(&prop.stx.key) {
            let ty = prop
              .stx
              .type_annotation
              .as_ref()
              .map(|t| self.type_from_type_expr(t))
              .unwrap_or(self.builtin.unknown);
            object.props.insert(
              name,
              ObjectProperty {
                typ: ty,
                optional: prop.stx.optional,
                readonly: prop.stx.readonly,
              },
            );
          }
        }
        TypeMember::Method(method) => {
          if let Some(name) = type_member_name(&method.stx.key) {
            let params = method
              .stx
              .parameters
              .iter()
              .map(|p| self.type_from_type_expr(&p.stx.type_expr))
              .collect();
            let ret = method
              .stx
              .return_type
              .as_ref()
              .map(|t| self.type_from_type_expr(t))
              .unwrap_or(self.builtin.unknown);
            let func_ty = self.type_store.function(params, ret);
            object.props.insert(
              name,
              ObjectProperty {
                typ: func_ty,
                optional: method.stx.optional,
                readonly: false,
              },
            );
          }
        }
        TypeMember::IndexSignature(index) => {
          let value = self.type_from_type_expr(&index.stx.type_annotation);
          let param_type = self.type_from_type_expr(&index.stx.parameter_type);
          let param_kind = self.type_store.kind(param_type).clone();
          match param_kind {
            TypeKind::Number => object.number_index = Some(value),
            TypeKind::String => object.string_index = Some(value),
            _ => object.string_index = Some(value),
          }
        }
        _ => {}
      }
    }
    object
  }

  fn merge_object_types(&mut self, mut base: ObjectType, extra: ObjectType) -> ObjectType {
    for (name, prop) in extra.props.into_iter() {
      match base.props.entry(name) {
        Entry::Vacant(entry) => {
          entry.insert(prop);
        }
        Entry::Occupied(mut entry) => {
          let existing = entry.get_mut();
          existing.typ = self
            .type_store
            .union(vec![existing.typ, prop.typ], &self.builtin);
          existing.optional = existing.optional || prop.optional;
          existing.readonly = existing.readonly || prop.readonly;
        }
      }
    }

    if base.string_index.is_none() {
      base.string_index = extra.string_index;
    }
    if base.number_index.is_none() {
      base.number_index = extra.number_index;
    }

    base
  }

  fn normalize_type_id(&mut self, ty: TypeId) -> TypeId {
    if (ty.0 as usize) < self.type_store.kinds.len() {
      return ty;
    }
    if let Some(store) = self.interned_store.as_ref() {
      if store.contains_type_id(ty) {
        return self.import_interned_type(store.canon(ty));
      }
    }
    self.builtin.unknown
  }

  fn type_from_type_expr(&mut self, expr: &Node<TypeExpr>) -> TypeId {
    match expr.stx.as_ref() {
      TypeExpr::TypeReference(reference) => {
        if let Some(file) = self.current_file {
          let span = loc_to_span(file, reference.loc).range;
          if let TypeEntityName::Identifier(type_name) = &reference.stx.name {
            if let Some(binding) = self
              .files
              .get(&file)
              .and_then(|f| f.bindings.get(type_name))
            {
              let symbol = binding.symbol;
              let ty_id = binding.type_id;
              let def = binding.def;
              self.record_symbol(file, span, symbol);
              if let Some(ty) = ty_id {
                return self.normalize_type_id(ty);
              }
              if let Some(def) = def {
                let ty = self.type_of_def(def);
                return self.normalize_type_id(ty);
              }
            }
            let mut entries: Vec<_> = self.def_data.iter().collect();
            entries.sort_by_key(|(id, data)| (data.file.0, data.span.start, id.0));
            let mut best: Option<(DefId, u8)> = None;
            for (id, data) in entries.into_iter() {
              if data.name != *type_name {
                continue;
              }
              let pri = self.def_priority(*id, sem_ts::Namespace::TYPE);
              match best {
                Some((_, existing)) if existing <= pri => {}
                _ => best = Some((*id, pri)),
              }
            }
            if let Some((id, _)) = best {
              let ty = self.type_of_def(id);
              return self.normalize_type_id(ty);
            }
          }
        }
        self.builtin.unknown
      }
      TypeExpr::Object(_) => self.builtin.object,
      TypeExpr::Number(_) => self.builtin.number,
      TypeExpr::String(_) => self.builtin.string,
      TypeExpr::Boolean(_) => self.builtin.boolean,
      TypeExpr::Any(_) => self.builtin.any,
      TypeExpr::Unknown(_) => self.builtin.unknown,
      TypeExpr::Null(_) => self.builtin.null,
      TypeExpr::Undefined(_) => self.builtin.undefined,
      TypeExpr::Void(_) => self.builtin.void,
      TypeExpr::Never(_) => self.builtin.never,
      TypeExpr::UnionType(union) => {
        let TypeUnion { types } = union.stx.as_ref();
        let members = types.iter().map(|t| self.type_from_type_expr(t)).collect();
        self.type_store.union(members, &self.builtin)
      }
      TypeExpr::TupleType(tuple) => {
        let readonly = tuple.stx.readonly;
        let elements = tuple
          .stx
          .elements
          .iter()
          .map(|elem| self.type_from_type_expr(&elem.stx.type_expr))
          .collect();
        self.type_store.tuple(elements, readonly)
      }
      TypeExpr::ArrayType(arr) => {
        let TypeArray { element_type, .. } = arr.stx.as_ref();
        let elem = self.type_from_type_expr(element_type);
        self.type_store.array(elem)
      }
      TypeExpr::FunctionType(func) => {
        let params = func
          .stx
          .parameters
          .iter()
          .map(|p| self.type_from_type_expr(&p.stx.type_expr))
          .collect();
        let ret = self.type_from_type_expr(&func.stx.return_type);
        self.type_store.function(params, ret)
      }
      TypeExpr::ConstructorType(cons) => {
        let params = cons
          .stx
          .parameters
          .iter()
          .map(|p| self.type_from_type_expr(&p.stx.type_expr))
          .collect();
        let ret = self.type_from_type_expr(&cons.stx.return_type);
        self.type_store.function(params, ret)
      }
      TypeExpr::ObjectType(obj) => {
        let object = self.object_type_from_members(&obj.stx.members);
        self.type_store.object(object)
      }
      TypeExpr::MappedType(mapped) => {
        let value_ty = self.type_from_type_expr(&mapped.stx.type_expr);
        let constraint = self.type_from_type_expr(&mapped.stx.constraint);
        if let Some(mut keys) = self.mapped_keys(constraint) {
          keys.sort();
          keys.dedup();
          let optional = matches!(
            mapped.stx.optional_modifier,
            Some(parse_js::ast::type_expr::MappedTypeModifier::Plus)
          );
          let readonly = matches!(
            mapped.stx.readonly_modifier,
            Some(parse_js::ast::type_expr::MappedTypeModifier::Plus)
          );
          let mut object = ObjectType::empty();
          for key in keys {
            object.props.insert(
              key,
              ObjectProperty {
                typ: value_ty,
                optional,
                readonly,
              },
            );
          }
          self.type_store.object(object)
        } else {
          let mut object = ObjectType::empty();
          object.string_index = Some(value_ty);
          self.type_store.object(object)
        }
      }
      TypeExpr::TypeQuery(query) => {
        if let Some(file) = self.current_file {
          if let TypeEntityName::Identifier(name) = &query.stx.expr_name {
            if let Some(binding) = self
              .files
              .get(&file)
              .and_then(|f| f.bindings.get(name))
              .cloned()
            {
              self.record_symbol(file, loc_to_span(file, query.loc).range, binding.symbol);
              if let Some(def) = binding.def {
                let ty = self.type_of_def(def);
                return self.normalize_type_id(ty);
              }
              if let Some(ty) = binding.type_id {
                return self.normalize_type_id(ty);
              }
            }
            let mut entries: Vec<_> = self.def_data.iter().collect();
            entries.sort_by_key(|(id, data)| (data.file.0, data.span.start, id.0));
            let mut best: Option<(DefId, u8)> = None;
            for (id, data) in entries {
              if data.name != *name {
                continue;
              }
              let pri = self.def_priority(*id, sem_ts::Namespace::VALUE);
              match best {
                Some((_, existing)) if existing <= pri => {}
                _ => best = Some((*id, pri)),
              }
            }
            if let Some((id, _)) = best {
              let ty = self.type_of_def(id);
              return self.normalize_type_id(ty);
            }
          }
        }
        self.builtin.unknown
      }
      TypeExpr::ParenthesizedType(inner) => self.type_from_type_expr(&inner.stx.type_expr),
      TypeExpr::LiteralType(lit) => match lit.stx.as_ref() {
        TypeLiteral::Boolean(value) => self.type_store.literal_boolean(*value),
        TypeLiteral::Number(n) => self.type_store.literal_number(n.clone()),
        TypeLiteral::String(s) => self.type_store.literal_string(s.clone()),
        TypeLiteral::Null => self.builtin.null,
        _ => self.builtin.unknown,
      },
      TypeExpr::TypePredicate(pred) => {
        let asserted = pred
          .stx
          .type_annotation
          .as_ref()
          .map(|t| self.type_from_type_expr(t));
        self
          .type_store
          .predicate(pred.stx.parameter_name.clone(), asserted, pred.stx.asserts)
      }
      _ => self.builtin.unknown,
    }
  }

  fn alloc_def(&mut self) -> DefId {
    let id = DefId(self.next_def);
    self.next_def += 1;
    id
  }

  fn alloc_symbol(&mut self) -> semantic_js::SymbolId {
    let id = semantic_js::SymbolId(self.next_symbol.try_into().unwrap_or(u32::MAX));
    self.next_symbol = self.next_symbol.saturating_add(1);
    id
  }

  fn record_def_symbol(&mut self, def: DefId, symbol: semantic_js::SymbolId) {
    self.symbol_to_def.insert(symbol, def);
  }

  fn record_symbol(&mut self, file: FileId, range: TextRange, symbol: semantic_js::SymbolId) {
    self
      .symbol_occurrences
      .entry(file)
      .or_default()
      .push(SymbolOccurrence { range, symbol });
  }
}

fn type_member_name(key: &TypePropertyKey) -> Option<String> {
  match key {
    TypePropertyKey::Identifier(name) => Some(name.clone()),
    TypePropertyKey::String(name) => Some(name.clone()),
    TypePropertyKey::Number(name) => Some(name.clone()),
    TypePropertyKey::Computed(_) => None,
  }
}

fn fatal_to_diagnostic(fatal: FatalError) -> Diagnostic {
  let placeholder = Span::new(FileId(0), TextRange::new(0, 0));
  match fatal {
    FatalError::Host(err) => {
      let mut diagnostic = codes::HOST_ERROR.error(err.to_string(), placeholder);
      diagnostic.push_note("no source span available for this host error; input may be missing");
      diagnostic
    }
    FatalError::Cancelled => codes::CANCELLED.error("operation cancelled", placeholder),
    FatalError::Ice(ice) => {
      let span = span_from_context(&ice.context, placeholder);
      let mut diagnostic = codes::INTERNAL_COMPILER_ERROR
        .error(format!("internal compiler error: {}", ice.message), span);
      if let Some(backtrace) = ice.backtrace {
        diagnostic.push_note(backtrace);
      }
      diagnostic
    }
    FatalError::OutOfMemory => codes::OUT_OF_MEMORY.error("out of memory", placeholder),
  }
}

fn span_from_context(ctx: &IceContext, placeholder: Span) -> Span {
  ctx
    .file
    .map(|file| Span::new(file, TextRange::new(0, 0)))
    .unwrap_or(placeholder)
}

fn loc_to_span(file: FileId, loc: Loc) -> Span {
  Span {
    file,
    range: TextRange {
      start: loc.0.min(u32::MAX as usize) as u32,
      end: loc.1.min(u32::MAX as usize) as u32,
    },
  }
}
