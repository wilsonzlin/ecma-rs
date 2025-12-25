use ahash::{HashMap, HashSet};
use derive_visitor::{DriveMut, VisitorMut};
use parse_js::ast::expr::pat::{ClassOrFuncName, IdPat};
use parse_js::ast::expr::IdExpr;
use parse_js::ast::import_export::{ExportName, ModuleExportImportName};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{ClassDecl, FuncDecl, VarDecl};
use parse_js::ast::stx::TopLevel;
use parse_js::lex::KEYWORDS_MAPPING;
use semantic_js::assoc::js::{declared_symbol, resolved_symbol, scope_id};
use semantic_js::js::{JsSemantics, ScopeId, ScopeKind, SymbolId, TopLevelMode};

#[derive(Clone, Debug, Default)]
pub struct ScopeUsages {
  pub foreign: HashSet<SymbolId>,
  pub unknown: HashSet<String>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct ScopeHazards {
  pub has_direct_eval: bool,
  pub has_with: bool,
}

#[derive(Clone, Copy)]
struct ExportNameSymbol(SymbolId);

#[derive(Clone, Debug)]
pub struct Replacement {
  pub start: usize,
  pub end: usize,
  pub text: String,
}

pub struct UsageData {
  pub top_scope: ScopeId,
  pub exported: HashSet<SymbolId>,
  pub symbol_names: HashMap<SymbolId, String>,
  pub scope_symbol_order: HashMap<ScopeId, Vec<SymbolId>>,
  pub scope_usages: HashMap<ScopeId, ScopeUsages>,
  pub scope_hazards: HashMap<ScopeId, ScopeHazards>,
}

struct SymbolCollector<'a> {
  sem: &'a JsSemantics,
  top_level_mode: TopLevelMode,
  exported: HashSet<SymbolId>,
  export_decl_stack: Vec<bool>,
  ignore_id_pats: usize,
  scope_usages: HashMap<ScopeId, ScopeUsages>,
}

type ClassDeclNode = Node<ClassDecl>;
type ClassOrFuncNameNode = Node<ClassOrFuncName>;
type ExportNameNode = Node<ExportName>;
type FuncDeclNode = Node<FuncDecl>;
type IdExprNode = Node<IdExpr>;
type IdPatNode = Node<IdPat>;
type TopLevelNode = Node<TopLevel>;
type VarDeclNode = Node<VarDecl>;

#[derive(VisitorMut)]
#[visitor(
  ClassDeclNode(enter, exit),
  ClassOrFuncNameNode(enter),
  ExportNameNode(enter, exit),
  FuncDeclNode(enter, exit),
  IdExprNode(enter),
  IdPatNode(enter),
  VarDeclNode(enter, exit)
)]
struct SymbolCollectorVisitor<'a> {
  inner: SymbolCollector<'a>,
}

impl<'a> SymbolCollector<'a> {
  fn new(sem: &'a JsSemantics, top_level_mode: TopLevelMode) -> Self {
    Self {
      sem,
      top_level_mode,
      exported: HashSet::default(),
      export_decl_stack: vec![false],
      ignore_id_pats: 0,
      scope_usages: HashMap::default(),
    }
  }

  fn record_unknown(&mut self, scope: ScopeId, name: &str) {
    let mut current = Some(scope);
    while let Some(scope_id) = current {
      self
        .scope_usages
        .entry(scope_id)
        .or_default()
        .unknown
        .insert(name.to_string());
      current = self.sem.scope(scope_id).parent;
    }
  }

  fn record_symbol_usage(&mut self, scope: ScopeId, sym: SymbolId) {
    let decl_scope = self.sem.symbol(sym).decl_scope;
    let mut current = Some(scope);
    while let Some(scope_id) = current {
      if scope_id == decl_scope {
        break;
      }
      self
        .scope_usages
        .entry(scope_id)
        .or_default()
        .foreign
        .insert(sym);
      current = self.sem.scope(scope_id).parent;
    }
  }

  fn maybe_mark_export(&mut self, scope: ScopeId, sym: SymbolId, mark_export: bool) {
    if mark_export && self.sem.scope(scope).kind == ScopeKind::Module {
      self.exported.insert(sym);
    }
  }

  fn resolve_export_name(&self, scope: ScopeId, name: &str) -> Option<SymbolId> {
    let name_id = self.sem.name_id(name)?;
    let mut current = Some(scope);
    while let Some(scope_id) = current {
      let scope_data = self.sem.scope(scope_id);
      if let Some(sym) = scope_data.get(name_id) {
        return Some(sym);
      }
      current = scope_data.parent;
    }
    None
  }
}

impl SymbolCollectorVisitor<'_> {
  fn enter_class_decl_node(&mut self, node: &mut ClassDeclNode) {
    let export = self.inner.top_level_mode == TopLevelMode::Module && node.stx.export;
    self.inner.export_decl_stack.push(export);
  }

  fn exit_class_decl_node(&mut self, _node: &mut ClassDeclNode) {
    self.inner.export_decl_stack.pop();
  }

  fn enter_func_decl_node(&mut self, node: &mut FuncDeclNode) {
    let export = self.inner.top_level_mode == TopLevelMode::Module && node.stx.export;
    self.inner.export_decl_stack.push(export);
  }

  fn exit_func_decl_node(&mut self, _node: &mut FuncDeclNode) {
    self.inner.export_decl_stack.pop();
  }

  fn enter_var_decl_node(&mut self, node: &mut VarDeclNode) {
    let export = self.inner.top_level_mode == TopLevelMode::Module && node.stx.export;
    self.inner.export_decl_stack.push(export);
  }

  fn exit_var_decl_node(&mut self, _node: &mut VarDeclNode) {
    self.inner.export_decl_stack.pop();
  }

  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    let Some(scope) = scope_id(&node.assoc) else {
      return;
    };
    match resolved_symbol(&node.assoc) {
      Some(sym) => self.inner.record_symbol_usage(scope, sym),
      None => self.inner.record_unknown(scope, &node.stx.name),
    }
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    if self.inner.ignore_id_pats > 0 {
      return;
    }
    let Some(scope) = scope_id(&node.assoc) else {
      return;
    };
    let mark_export = *self.inner.export_decl_stack.last().unwrap_or(&false);
    match resolved_symbol(&node.assoc) {
      Some(sym) => {
        self.inner.maybe_mark_export(scope, sym, mark_export);
        self.inner.record_symbol_usage(scope, sym);
      }
      None => self.inner.record_unknown(scope, &node.stx.name),
    }
  }

  fn enter_class_or_func_name_node(&mut self, node: &mut ClassOrFuncNameNode) {
    let Some(scope) = scope_id(&node.assoc) else {
      return;
    };
    let mark_export = *self.inner.export_decl_stack.last().unwrap_or(&false);
    if let Some(sym) = declared_symbol(&node.assoc) {
      self.inner.maybe_mark_export(scope, sym, mark_export);
      self.inner.record_symbol_usage(scope, sym);
    } else {
      self.inner.record_unknown(scope, &node.stx.name);
    }
  }

  fn enter_export_name_node(&mut self, node: &mut ExportNameNode) {
    let Some(scope) = scope_id(&node.assoc) else {
      return;
    };
    if let ModuleExportImportName::Ident(name) = &node.stx.exportable {
      if let Some(sym) = self.inner.resolve_export_name(scope, name) {
        node.assoc.set(ExportNameSymbol(sym));
        self.inner.record_symbol_usage(scope, sym);
      } else {
        self.inner.record_unknown(scope, name);
      }
    }
    self.inner.ignore_id_pats += 1;
  }

  fn exit_export_name_node(&mut self, _node: &mut ExportNameNode) {
    self.inner.ignore_id_pats -= 1;
  }
}

pub fn collect_usages(
  top: &mut TopLevelNode,
  sem: &JsSemantics,
  top_level_mode: TopLevelMode,
) -> UsageData {
  let mut visitor = SymbolCollectorVisitor {
    inner: SymbolCollector::new(sem, top_level_mode),
  };
  top.drive_mut(&mut visitor);

  let SymbolCollector {
    exported,
    scope_usages,
    ..
  } = visitor.inner;

  let mut symbol_names = HashMap::default();
  let mut scope_symbol_order: HashMap<ScopeId, Vec<SymbolId>> = HashMap::default();
  let mut scope_hazards: HashMap<ScopeId, ScopeHazards> = HashMap::default();
  let mut queue = vec![sem.top_scope()];
  while let Some(scope_id) = queue.pop() {
    let scope_data = sem.scope(scope_id);
    let hazards = ScopeHazards {
      has_direct_eval: scope_data.has_direct_eval,
      has_with: scope_data.is_dynamic && !scope_data.has_direct_eval,
    };
    if hazards.has_direct_eval || hazards.has_with {
      scope_hazards.insert(scope_id, hazards);
    }
    let symbols: Vec<SymbolId> = sem.scope_symbols(scope_id).map(|(_, sym)| sym).collect();
    for sym in symbols.iter().copied() {
      symbol_names
        .entry(sym)
        .or_insert_with(|| sem.name(sem.symbol(sym).name).to_string());
    }
    if !symbols.is_empty() {
      scope_symbol_order.insert(scope_id, symbols);
    }
    queue.extend(scope_data.children.iter().copied());
  }

  UsageData {
    top_scope: sem.top_scope(),
    exported,
    symbol_names,
    scope_symbol_order,
    scope_usages,
    scope_hazards,
  }
}

struct NameGenerator {
  counter: usize,
}

const FIRST_CHARS: &[u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ$_";
const NON_FIRST_CHARS: &[u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ$_0123456789";

impl NameGenerator {
  fn new() -> Self {
    Self { counter: 0 }
  }

  fn encode(mut n: usize) -> String {
    let mut out = String::new();
    let first = FIRST_CHARS[n % FIRST_CHARS.len()] as char;
    out.push(first);
    n /= FIRST_CHARS.len();
    while n > 0 {
      let c = NON_FIRST_CHARS[n % NON_FIRST_CHARS.len()] as char;
      out.push(c);
      n /= NON_FIRST_CHARS.len();
    }
    out
  }

  fn next_name<F: Fn(&str) -> bool>(&mut self, allowed: F) -> String {
    loop {
      let candidate = Self::encode(self.counter);
      self.counter += 1;
      if allowed(&candidate) {
        return candidate;
      }
    }
  }
}

fn reserved_names() -> HashSet<String> {
  KEYWORDS_MAPPING.values().map(|s| s.to_string()).collect()
}

pub fn assign_names(sem: &JsSemantics, usage: &UsageData) -> HashMap<SymbolId, String> {
  let reserved = reserved_names();
  // Dynamic scopes (direct `eval`/`with`) keep their original names; direct
  // `eval` can also reach all lexical ancestors.
  let disabled_scopes = {
    let mut set = HashSet::default();
    for (scope, hazards) in usage.scope_hazards.iter() {
      if hazards.has_with || hazards.has_direct_eval {
        set.insert(*scope);
      }
      if hazards.has_direct_eval {
        let mut current = sem.scope(*scope).parent;
        while let Some(scope_id) = current {
          set.insert(scope_id);
          current = sem.scope(scope_id).parent;
        }
      }
    }
    set
  };
  // Preserve any outer bindings referenced from a `with` scope since property
  // lookups may depend on their names.
  let pinned_symbols: HashSet<SymbolId> = usage
    .scope_hazards
    .iter()
    .filter_map(|(scope, hazards)| {
      if hazards.has_with {
        usage.scope_usages.get(scope)
      } else {
        None
      }
    })
    .flat_map(|usage| usage.foreign.iter().copied())
    .collect();
  let mut renames = HashMap::default();

  fn assign_scope(
    scope: ScopeId,
    sem: &JsSemantics,
    usage: &UsageData,
    reserved: &HashSet<String>,
    disabled_scopes: &HashSet<ScopeId>,
    pinned_symbols: &HashSet<SymbolId>,
    renames: &mut HashMap<SymbolId, String>,
  ) {
    let symbol_order = usage
      .scope_symbol_order
      .get(&scope)
      .cloned()
      .unwrap_or_default();
    let usage_data = usage.scope_usages.get(&scope);
    let children = sem.scope(scope).children.clone();

    if disabled_scopes.contains(&scope) {
      for child in children {
        assign_scope(child, sem, usage, reserved, disabled_scopes, pinned_symbols, renames);
      }
      return;
    }

    let mut disallowed: HashSet<String> = reserved.clone();
    if let Some(u) = usage_data {
      for sym in u.foreign.iter() {
        if let Some(name) = renames.get(sym) {
          disallowed.insert(name.clone());
        } else if let Some(name) = usage.symbol_names.get(sym) {
          disallowed.insert(name.clone());
        }
      }
      for name in u.unknown.iter() {
        disallowed.insert(name.clone());
      }
    }

    let mut generator = NameGenerator::new();
    let mut used = HashSet::default();
    for sym in symbol_order {
      let Some(name) = usage.symbol_names.get(&sym) else {
        continue;
      };
      if usage.exported.contains(&sym) || pinned_symbols.contains(&sym) {
        used.insert(name.clone());
        continue;
      }
      let new_name = generator
        .next_name(|candidate| !disallowed.contains(candidate) && !used.contains(candidate));
      used.insert(new_name.clone());
      renames.insert(sym, new_name);
    }

    for child in children {
      assign_scope(child, sem, usage, reserved, disabled_scopes, pinned_symbols, renames);
    }
  }

  assign_scope(
    usage.top_scope,
    sem,
    usage,
    &reserved,
    &disabled_scopes,
    &pinned_symbols,
    &mut renames,
  );
  renames
}

#[derive(VisitorMut)]
#[visitor(
  ClassOrFuncNameNode(enter),
  ExportNameNode(enter),
  IdExprNode(enter),
  IdPatNode(enter)
)]
struct ApplyVisitor<'a> {
  renames: &'a HashMap<SymbolId, String>,
  replacements: Vec<Replacement>,
}

impl<'a> ApplyVisitor<'a> {
  fn maybe_apply(&mut self, loc: (usize, usize), sym: Option<SymbolId>, name: &mut String) {
    let Some(sym) = sym else { return };
    let Some(new_name) = self.renames.get(&sym) else {
      return;
    };
    if &*name == new_name {
      return;
    }
    let start = loc.0;
    let end = loc.1;
    self.replacements.push(Replacement {
      start,
      end,
      text: new_name.clone(),
    });
    *name = new_name.clone();
  }
}

impl<'a> ApplyVisitor<'a> {
  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    let sym = resolved_symbol(&node.assoc);
    let len = node.stx.name.len();
    let start = node.loc.0.saturating_sub(len);
    let end = start + len;
    self.maybe_apply((start, end), sym, &mut node.stx.name);
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    let sym = resolved_symbol(&node.assoc);
    let len = node.stx.name.len();
    let start = node.loc.0.saturating_sub(len);
    let end = start + len;
    self.maybe_apply((start, end), sym, &mut node.stx.name);
  }

  fn enter_class_or_func_name_node(&mut self, node: &mut ClassOrFuncNameNode) {
    let sym = declared_symbol(&node.assoc);
    let len = node.stx.name.len();
    let start = node.loc.0;
    let end = start + len;
    self.maybe_apply((start, end), sym, &mut node.stx.name);
  }

  fn enter_export_name_node(&mut self, node: &mut ExportNameNode) {
    let Some(sym) = node.assoc.get::<ExportNameSymbol>().map(|s| s.0) else {
      return;
    };
    let Some(new_name) = self.renames.get(&sym) else {
      return;
    };
    let alias = &node.stx.alias.stx.name;
    let replacement = if alias == new_name {
      new_name.clone()
    } else {
      format!("{} as {}", new_name, alias)
    };
    if node.stx.exportable.as_str() != new_name {
      node.stx.exportable = ModuleExportImportName::Ident(new_name.clone());
    }
    self.replacements.push(Replacement {
      start: node.loc.0,
      end: node.loc.1,
      text: replacement,
    });
  }
}

pub fn apply_renames(
  top: &mut TopLevelNode,
  renames: &HashMap<SymbolId, String>,
) -> Vec<Replacement> {
  let mut visitor = ApplyVisitor {
    renames,
    replacements: Vec::new(),
  };
  top.drive_mut(&mut visitor);
  visitor.replacements
}

pub fn rewrite_source(source: &str, replacements: &mut Vec<Replacement>) -> String {
  replacements.sort_by_key(|r| r.start);
  let mut out = String::with_capacity(source.len());
  let mut cur = 0;
  for rep in replacements.iter() {
    assert!(rep.start >= cur && rep.end >= rep.start);
    out.push_str(&source[cur..rep.start]);
    out.push_str(&rep.text);
    cur = rep.end;
  }
  out.push_str(&source[cur..]);
  out
}
