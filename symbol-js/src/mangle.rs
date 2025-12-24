use ahash::{HashMap, HashSet};
use derive_visitor::{DriveMut, VisitorMut};
use parse_js::ast::expr::pat::{ClassOrFuncName, IdPat};
use parse_js::ast::expr::{CallExpr, Expr, IdExpr};
use parse_js::ast::node::{Node, NodeAssocData};
use parse_js::ast::stmt::WithStmt;
use parse_js::ast::stx::TopLevel;

use crate::compute_symbols;
use crate::symbol::{Scope, Symbol};
use crate::TopLevelMode;

#[derive(Default)]
struct MangleScopeData {
  dynamic: bool,
  foreign: HashSet<Symbol>,
  unknown: HashSet<String>,
}

/// Mangles identifiers in-place, returning the mapping from Symbols to new identifier names.
///
/// All scopes are assumed to already be associated with nodes via `compute_symbols`.
pub fn mangle(
  top_level_node: &mut Node<TopLevel>,
  top_level_scope: &Scope,
) -> HashMap<Symbol, String> {
  mark_dynamic_scopes(top_level_node);
  collect_scope_constraints(top_level_node);
  let original_names = collect_original_names(top_level_scope);

  let mut mapping = HashMap::default();
  assign_names(top_level_scope, &original_names, &mut mapping);
  rename_ast(top_level_node, &mapping);

  mapping
}

/// Convenience wrapper that computes scopes before mangling.
pub fn mangle_with_top_level_mode(
  top_level_node: &mut Node<TopLevel>,
  top_level_mode: TopLevelMode,
) -> HashMap<Symbol, String> {
  let scope = compute_symbols(top_level_node, top_level_mode);
  mangle(top_level_node, &scope)
}

fn mark_dynamic_scopes(top_level_node: &mut Node<TopLevel>) {
  let mut visitor = DynamicScopeVisitor;
  top_level_node.drive_mut(&mut visitor);
}

fn collect_scope_constraints(top_level_node: &mut Node<TopLevel>) {
  let mut visitor = ConstraintVisitor;
  top_level_node.drive_mut(&mut visitor);
}

fn collect_original_names(top_level_scope: &Scope) -> HashMap<Symbol, String> {
  let mut names = HashMap::default();
  let mut queue = vec![top_level_scope.clone()];
  while let Some(scope) = queue.pop() {
    let data = scope.data();
    for name in data.symbol_names() {
      if let Some(sym) = data.get_symbol(name) {
        names.entry(sym).or_insert_with(|| name.clone());
      }
    }
    queue.extend(data.children().iter().cloned());
  }
  names
}

fn assign_names(
  top_level_scope: &Scope,
  original_names: &HashMap<Symbol, String>,
  mapping: &mut HashMap<Symbol, String>,
) {
  let mut scopes = Vec::new();
  scopes.push(top_level_scope.clone());
  scopes.extend(top_level_scope.descendants());

  for scope in scopes {
    assign_scope_names(&scope, original_names, mapping);
  }
}

fn rename_ast(top_level_node: &mut Node<TopLevel>, mapping: &HashMap<Symbol, String>) {
  let mut visitor = RenameVisitor { mapping };
  top_level_node.drive_mut(&mut visitor);
}

fn scope_from_assoc(assoc: &NodeAssocData) -> Scope {
  assoc
    .get::<Scope>()
    .expect("mangle requires compute_symbols to be run first")
    .clone()
}

fn mark_dynamic_chain(scope: &Scope) {
  for scope in scope.self_and_ancestors() {
    scope
      .data_mut()
      .get_or_insert_assoc::<MangleScopeData>()
      .dynamic = true;
  }
}

fn is_direct_eval_call(node: &Node<CallExpr>) -> bool {
  if node.stx.optional_chaining {
    return false;
  }

  let Expr::Id(id_expr) = node.stx.callee.stx.as_ref() else {
    return false;
  };

  if id_expr.stx.name != "eval" {
    return false;
  }

  let scope = scope_from_assoc(&node.assoc);
  scope.find_symbol("eval".to_string()).is_none()
}

fn mark_unknown(scope: &Scope, name: &str) {
  for anc in scope.self_and_ancestors() {
    anc
      .data_mut()
      .get_or_insert_assoc::<MangleScopeData>()
      .unknown
      .insert(name.to_string());
  }
}

fn mark_foreign(scope: &Scope, name: &str, sym: Symbol) {
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
      .get_or_insert_assoc::<MangleScopeData>()
      .foreign
      .insert(sym);
  }
}

fn is_dynamic(scope: &Scope) -> bool {
  scope
    .data()
    .get_assoc::<MangleScopeData>()
    .map(|d| d.dynamic)
    .unwrap_or(false)
}

fn foreign_symbols(scope: &Scope) -> HashSet<Symbol> {
  scope
    .data()
    .get_assoc::<MangleScopeData>()
    .map(|d| d.foreign.clone())
    .unwrap_or_default()
}

fn unknown_names(scope: &Scope) -> HashSet<String> {
  scope
    .data()
    .get_assoc::<MangleScopeData>()
    .map(|d| d.unknown.clone())
    .unwrap_or_default()
}

fn assign_scope_names(
  scope: &Scope,
  original_names: &HashMap<Symbol, String>,
  mapping: &mut HashMap<Symbol, String>,
) {
  if is_dynamic(scope) {
    return;
  }

  let declared_symbols: Vec<Symbol> = {
    let data = scope.data();
    data
      .symbol_names()
      .iter()
      .filter_map(|name| data.get_symbol(name))
      .collect()
  };

  let mut reserved = default_reserved_names();
  reserved.extend(unknown_names(scope).into_iter());
  for sym in foreign_symbols(scope) {
    if let Some(name) = mapping.get(&sym) {
      reserved.insert(name.clone());
    } else if let Some(name) = original_names.get(&sym) {
      reserved.insert(name.clone());
    }
  }

  let mut generator = NameGenerator::default();

  for symbol in declared_symbols {
    let new_name = generator.next_name(&reserved);
    reserved.insert(new_name.clone());
    mapping.insert(symbol, new_name);
  }
}

fn default_reserved_names() -> HashSet<String> {
  [
    "await",
    "break",
    "case",
    "catch",
    "class",
    "const",
    "continue",
    "debugger",
    "default",
    "delete",
    "do",
    "else",
    "enum",
    "export",
    "extends",
    "false",
    "finally",
    "for",
    "function",
    "if",
    "import",
    "in",
    "instanceof",
    "let",
    "new",
    "null",
    "return",
    "static",
    "super",
    "switch",
    "this",
    "throw",
    "true",
    "try",
    "typeof",
    "var",
    "void",
    "while",
    "with",
    "yield",
    // Avoid generating the magic identifiers.
    "eval",
    "arguments",
  ]
  .into_iter()
  .map(|s| s.to_string())
  .collect()
}

#[derive(Default)]
struct NameGenerator {
  counter: usize,
}

impl NameGenerator {
  // First characters cannot be numbers.
  const FIRST_CHARS: &'static [u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ$_";
  const OTHER_CHARS: &'static [u8] =
    b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ$_0123456789";

  fn next_name(&mut self, reserved: &HashSet<String>) -> String {
    loop {
      let name = self.encode(self.counter);
      self.counter += 1;
      if !reserved.contains(&name) {
        return name;
      }
    }
  }

  fn encode(&self, mut n: usize) -> String {
    let mut buf = Vec::new();

    let first_len = Self::FIRST_CHARS.len();
    buf.push(Self::FIRST_CHARS[n % first_len]);
    n /= first_len;

    if n == 0 {
      return String::from_utf8(buf).unwrap();
    }

    let other_len = Self::OTHER_CHARS.len();
    let mut rest = Vec::new();
    while n > 0 {
      rest.push(Self::OTHER_CHARS[n % other_len]);
      n /= other_len;
    }
    rest.reverse();
    buf.extend(rest);

    String::from_utf8(buf).unwrap()
  }
}

type CallExprNode = Node<CallExpr>;
type WithStmtNode = Node<WithStmt>;
type IdExprNode = Node<IdExpr>;
type IdPatNode = Node<IdPat>;
type ClassOrFuncNameNode = Node<ClassOrFuncName>;

#[derive(VisitorMut)]
#[visitor(CallExprNode(enter), WithStmtNode(enter))]
struct DynamicScopeVisitor;

impl DynamicScopeVisitor {
  fn enter_call_expr_node(&mut self, node: &mut CallExprNode) {
    if is_direct_eval_call(node) {
      let scope = scope_from_assoc(&node.assoc);
      mark_dynamic_chain(&scope);
    }
  }

  fn enter_with_stmt_node(&mut self, node: &mut WithStmtNode) {
    let scope = scope_from_assoc(&node.assoc);
    mark_dynamic_chain(&scope);
  }
}

#[derive(VisitorMut)]
#[visitor(IdExprNode(enter))]
struct ConstraintVisitor;

impl ConstraintVisitor {
  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    let scope = scope_from_assoc(&node.assoc);
    if let Some(sym) = scope.find_symbol(node.stx.name.clone()) {
      mark_foreign(&scope, &node.stx.name, sym);
    } else {
      mark_unknown(&scope, &node.stx.name);
    }
  }
}

#[derive(VisitorMut)]
#[visitor(IdPatNode(enter), IdExprNode(enter), ClassOrFuncNameNode(enter))]
struct RenameVisitor<'a> {
  mapping: &'a HashMap<Symbol, String>,
}

impl<'a> RenameVisitor<'a> {
  fn rename(&self, scope: Scope, name: &mut String) {
    if let Some(symbol) = scope.find_symbol(name.clone()) {
      if let Some(new_name) = self.mapping.get(&symbol) {
        *name = new_name.clone();
      }
    }
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    let scope = scope_from_assoc(&node.assoc);
    self.rename(scope, &mut node.stx.name);
  }

  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    let scope = scope_from_assoc(&node.assoc);
    self.rename(scope, &mut node.stx.name);
  }

  fn enter_class_or_func_name_node(&mut self, node: &mut ClassOrFuncNameNode) {
    let scope = scope_from_assoc(&node.assoc);
    self.rename(scope, &mut node.stx.name);
  }
}
