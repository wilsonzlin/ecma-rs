use ahash::{HashMap, HashMapExt, HashSet, HashSetExt};
use derive_visitor::{DriveMut, VisitorMut};
use parse_js::ast::expr::pat::{ClassOrFuncName, IdPat};
use parse_js::ast::expr::IdExpr;
use parse_js::ast::import_export::ExportName;
use parse_js::ast::import_export::ModuleExportImportName;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{ClassDecl, FuncDecl, VarDecl};
use parse_js::ast::stx::TopLevel;
use parse_js::lex::KEYWORDS_MAPPING;
use symbol_js::symbol::{Scope, ScopeType, Symbol};
use symbol_js::TopLevelMode;

#[derive(Clone, Debug, Default)]
pub struct ScopeUsages {
  pub foreign: HashSet<Symbol>,
  pub unknown: HashSet<String>,
}

#[derive(Clone, Copy)]
struct ResolvedSymbol(Symbol);

#[derive(Clone, Copy)]
struct ExportNameSymbol(Symbol);

#[derive(Clone, Debug)]
pub struct Replacement {
  pub start: usize,
  pub end: usize,
  pub text: String,
}

pub struct UsageData {
  pub top_scope: Scope,
  pub exported: HashSet<Symbol>,
  pub symbol_names: HashMap<Symbol, String>,
}

struct SymbolCollector {
  top_level_mode: TopLevelMode,
  exported: HashSet<Symbol>,
  export_decl_stack: Vec<bool>,
  ignore_id_pats: usize,
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
struct SymbolCollectorVisitor {
  inner: SymbolCollector,
}

impl SymbolCollector {
  fn new(top_level_mode: TopLevelMode) -> Self {
    Self {
      top_level_mode,
      exported: HashSet::new(),
      export_decl_stack: vec![false],
      ignore_id_pats: 0,
    }
  }

  fn record_unknown(&mut self, name: &str, scope: &Scope) {
    for anc in scope.self_and_ancestors() {
      anc
        .data_mut()
        .get_or_insert_assoc::<ScopeUsages>()
        .unknown
        .insert(name.to_string());
    }
  }

  fn record_symbol_usage(&mut self, name: &str, sym: Symbol, scope: &Scope) {
    for anc in scope.self_and_ancestors() {
      let defines = {
        let data = anc.data();
        data.get_symbol(name).is_some_and(|s| s == sym)
      };
      if defines {
        break;
      }
      anc
        .data_mut()
        .get_or_insert_assoc::<ScopeUsages>()
        .foreign
        .insert(sym);
    }
  }

  fn attach_symbol(&mut self, name: &str, scope: &Scope, mark_export: bool) -> Option<Symbol> {
    scope.find_symbol(name.to_string()).map(|sym| {
      self.record_symbol_usage(name, sym, scope);
      if mark_export && scope.data().typ() == ScopeType::Module {
        self.exported.insert(sym);
      }
      sym
    })
  }
}

impl SymbolCollectorVisitor {
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
    let scope = node.assoc.get::<Scope>().unwrap();
    match self
      .inner
      .attach_symbol(&node.stx.name, scope, false)
      .map(ResolvedSymbol)
    {
      Some(sym) => node.assoc.set(sym),
      None => self.inner.record_unknown(&node.stx.name, scope),
    }
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    if self.inner.ignore_id_pats > 0 {
      return;
    }
    let mark_export = *self.inner.export_decl_stack.last().unwrap_or(&false);
    let scope = node.assoc.get::<Scope>().unwrap();
    match self
      .inner
      .attach_symbol(&node.stx.name, scope, mark_export)
      .map(ResolvedSymbol)
    {
      Some(sym) => node.assoc.set(sym),
      None => self.inner.record_unknown(&node.stx.name, scope),
    }
  }

  fn enter_class_or_func_name_node(&mut self, node: &mut ClassOrFuncNameNode) {
    let scope = node.assoc.get::<Scope>().unwrap();
    let mark_export = *self.inner.export_decl_stack.last().unwrap_or(&false);
    if let Some(sym) = self
      .inner
      .attach_symbol(&node.stx.name, scope, mark_export)
      .map(ResolvedSymbol)
    {
      node.assoc.set(sym);
    }
  }

  fn enter_export_name_node(&mut self, node: &mut ExportNameNode) {
    let scope = node.assoc.get::<Scope>().unwrap();
    if let ModuleExportImportName::Ident(name) = &node.stx.exportable {
      if let Some(sym) = scope.find_symbol(name.clone()).map(ExportNameSymbol) {
        node.assoc.set(sym);
      }
    }
    // Avoid treating the alias IdPat as a usage/exported binding.
    self.inner.ignore_id_pats += 1;
  }

  fn exit_export_name_node(&mut self, _node: &mut ExportNameNode) {
    self.inner.ignore_id_pats -= 1;
  }
}

pub fn collect_usages(top: &mut TopLevelNode, top_level_mode: TopLevelMode) -> UsageData {
  let mut visitor = SymbolCollectorVisitor {
    inner: SymbolCollector::new(top_level_mode),
  };
  top.drive_mut(&mut visitor);

  let top_scope = top.assoc.get::<Scope>().unwrap().clone();
  let mut symbol_names = HashMap::new();
  let mut queue = vec![top_scope.clone()];
  while let Some(scope) = queue.pop() {
    let data = scope.data();
    for name in data.symbol_names() {
      if let Some(sym) = data.get_symbol(name) {
        symbol_names.insert(sym, name.clone());
      }
    }
    queue.extend(data.children().iter().cloned());
  }

  UsageData {
    top_scope,
    exported: visitor.inner.exported,
    symbol_names,
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

pub fn assign_names(usage: &UsageData) -> HashMap<Symbol, String> {
  let reserved = reserved_names();
  let mut renames = HashMap::new();

  fn assign_scope(
    scope: Scope,
    usage: &UsageData,
    reserved: &HashSet<String>,
    renames: &mut HashMap<Symbol, String>,
  ) {
    let data = scope.data();
    let symbol_order = data.symbol_names().clone();
    let usage_data = data.get_assoc::<ScopeUsages>().cloned();
    let children = data.children().clone();
    drop(data);

    let mut disallowed: HashSet<String> = reserved.clone();
    if let Some(u) = usage_data {
      for sym in u.foreign.iter() {
        if let Some(name) = renames.get(sym) {
          disallowed.insert(name.clone());
        } else if let Some(name) = usage.symbol_names.get(sym) {
          disallowed.insert(name.clone());
        }
      }
      for name in u.unknown {
        disallowed.insert(name);
      }
    }

    let mut generator = NameGenerator::new();
    let mut used = HashSet::new();
    for ident in symbol_order {
      let data = scope.data();
      let Some(sym) = data.get_symbol(&ident) else {
        continue;
      };
      drop(data);
      if usage.exported.contains(&sym) {
        used.insert(ident);
        continue;
      }
      let name = generator
        .next_name(|candidate| !disallowed.contains(candidate) && !used.contains(candidate));
      used.insert(name.clone());
      renames.insert(sym, name);
    }

    for child in children {
      assign_scope(child, usage, reserved, renames);
    }
  }

  assign_scope(usage.top_scope.clone(), usage, &reserved, &mut renames);
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
  renames: &'a HashMap<Symbol, String>,
  replacements: Vec<Replacement>,
}

impl<'a> ApplyVisitor<'a> {
  fn maybe_apply(&mut self, loc: (usize, usize), sym: Option<Symbol>, name: &mut String) {
    let Some(sym) = sym else { return };
    let Some(new_name) = self.renames.get(&sym) else {
      return;
    };
    if &*name == new_name {
      return;
    }
    let identifier_end = loc.0;
    let start = identifier_end.saturating_sub(name.len());
    let end = start + name.len();
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
    let sym = node.assoc.get::<ResolvedSymbol>().map(|s| s.0);
    self.maybe_apply((node.loc.0, node.loc.1), sym, &mut node.stx.name);
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    let sym = node.assoc.get::<ResolvedSymbol>().map(|s| s.0);
    self.maybe_apply((node.loc.0, node.loc.1), sym, &mut node.stx.name);
  }

  fn enter_class_or_func_name_node(&mut self, node: &mut ClassOrFuncNameNode) {
    let sym = node.assoc.get::<ResolvedSymbol>().map(|s| s.0);
    self.maybe_apply((node.loc.0, node.loc.1), sym, &mut node.stx.name);
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
  renames: &HashMap<Symbol, String>,
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
