use ahash::{HashMap, HashSet};
use derive_visitor::{DriveMut, VisitorMut};
use parse_js::ast::class_or_object::{
  ClassOrObjKey, ClassOrObjMemberDirectKey, ClassOrObjVal, ObjMember, ObjMemberType,
};
use parse_js::ast::expr::pat::{ArrPat, ClassOrFuncName, IdPat, ObjPat, ObjPatProp, Pat};
use parse_js::ast::expr::{CallExpr, ClassExpr, Expr, FuncExpr, IdExpr};
use parse_js::ast::import_export::{ExportNames, ModuleExportImportName};
use parse_js::ast::node::{Node, NodeAssocData};
use parse_js::ast::stmt::decl::{ClassDecl, FuncDecl, PatDecl};
use parse_js::ast::stmt::{ExportListStmt, Stmt, WithStmt};
use parse_js::ast::stx::TopLevel;
use parse_js::lex::KEYWORDS_MAPPING;
use parse_js::loc::Loc;
use parse_js::token::TT;

use crate::compute_symbols;
use crate::symbol::{Scope, Symbol};
use crate::TopLevelMode;

/// Options controlling how identifier mangling behaves.
#[derive(Clone, Debug)]
pub struct MangleOptions {
  /// Whether to rename bindings in the top-level scope (module scope).
  pub mangle_toplevel: bool,
  /// Whether to rename function names (affects `Function.prototype.name`).
  pub mangle_function_names: bool,
  /// Whether to rename class names (affects `Class.name`).
  pub mangle_class_names: bool,
}

impl Default for MangleOptions {
  fn default() -> Self {
    Self {
      mangle_toplevel: true,
      mangle_function_names: true,
      mangle_class_names: true,
    }
  }
}

/// Mapping of renamed symbols.
#[derive(Default)]
pub struct MangleResult {
  /// Symbols that were renamed mapped to their new names.
  pub renamed: HashMap<Symbol, String>,
}

#[derive(Default)]
struct MangleScopeData {
  dynamic: bool,
  foreign: HashSet<Symbol>,
  unknown: HashSet<String>,
  pinned: HashSet<Symbol>,
}

/// Mangles identifiers in-place, returning the mapping from Symbols to new identifier names.
///
/// All scopes are assumed to already be associated with nodes via `compute_symbols`.
pub fn mangle(
  top_level_node: &mut Node<TopLevel>,
  top_level_scope: &Scope,
) -> HashMap<Symbol, String> {
  let mode = match top_level_scope.data().typ() {
    crate::symbol::ScopeType::Module => TopLevelMode::Module,
    _ => TopLevelMode::Global,
  };
  mangle_with_options(
    top_level_node,
    top_level_scope,
    mode,
    &MangleOptions::default(),
  )
}

/// Perform identifier mangling on the provided AST. This computes symbols internally.
pub fn mangle_identifiers(
  top_level_node: &mut Node<TopLevel>,
  top_level_mode: TopLevelMode,
  opts: &MangleOptions,
) -> MangleResult {
  let scope = compute_symbols(top_level_node, top_level_mode);
  let renamed = mangle_with_options(top_level_node, &scope, top_level_mode, opts);
  MangleResult { renamed }
}

/// Convenience wrapper that computes scopes before mangling.
pub fn mangle_with_top_level_mode(
  top_level_node: &mut Node<TopLevel>,
  top_level_mode: TopLevelMode,
) -> HashMap<Symbol, String> {
  mangle_identifiers(top_level_node, top_level_mode, &MangleOptions::default()).renamed
}

fn mangle_with_options(
  top_level_node: &mut Node<TopLevel>,
  top_level_scope: &Scope,
  top_level_mode: TopLevelMode,
  opts: &MangleOptions,
) -> HashMap<Symbol, String> {
  mark_dynamic_scopes(top_level_node);
  collect_scope_constraints(top_level_node);
  collect_pinned_symbols(top_level_node, top_level_scope, top_level_mode, opts);
  let original_names = collect_original_names(top_level_scope);

  let mut mapping = HashMap::default();
  assign_names(top_level_scope, &original_names, &mut mapping);
  rename_ast(top_level_node, &mapping);
  mapping
}

fn mark_dynamic_scopes(top_level_node: &mut Node<TopLevel>) {
  let mut visitor = DynamicScopeVisitor;
  top_level_node.drive_mut(&mut visitor);
}

fn collect_scope_constraints(top_level_node: &mut Node<TopLevel>) {
  let mut visitor = ConstraintVisitor {
    export_alias_stack: Vec::new(),
  };
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
  let mut visitor = RenameVisitor {
    mapping,
    export_alias_stack: Vec::new(),
  };
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

fn resolve_symbol(scope: &Scope, name: &str) -> Option<(Scope, Symbol)> {
  for sc in scope.self_and_ancestors() {
    let sym = { sc.data().get_symbol(name) };
    if let Some(sym) = sym {
      return Some((sc, sym));
    }
  }
  None
}

fn mark_pinned(scope: &Scope, sym: Symbol) {
  scope
    .data_mut()
    .get_or_insert_assoc::<MangleScopeData>()
    .pinned
    .insert(sym);
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

fn pinned_symbols(scope: &Scope) -> HashSet<Symbol> {
  scope
    .data()
    .get_assoc::<MangleScopeData>()
    .map(|d| d.pinned.clone())
    .unwrap_or_default()
}

fn pin_scope_symbols(scope: &Scope) {
  let symbols: Vec<_> = {
    let data = scope.data();
    data
      .symbol_names()
      .iter()
      .filter_map(|name| data.get_symbol(name))
      .collect()
  };
  for sym in symbols {
    mark_pinned(scope, sym);
  }
}

fn pin_module_exports(top: &Node<TopLevel>) {
  for stmt in top.stx.body.iter() {
    match stmt.stx.as_ref() {
      Stmt::VarDecl(var) if var.stx.export => {
        for declarator in var.stx.declarators.iter() {
          pin_pat_decl(&declarator.pattern, &mut |scope, sym| {
            mark_pinned(scope, sym)
          });
        }
      }
      Stmt::FunctionDecl(func) if func.stx.export && !func.stx.export_default => {
        if let Some(name) = &func.stx.name {
          if let Some(scope) = name.assoc.get::<Scope>() {
            if let Some((decl_scope, sym)) = resolve_symbol(scope, &name.stx.name) {
              mark_pinned(&decl_scope, sym);
            }
          }
        }
      }
      Stmt::ClassDecl(class) if class.stx.export && !class.stx.export_default => {
        if let Some(name) = &class.stx.name {
          if let Some(scope) = name.assoc.get::<Scope>() {
            if let Some((decl_scope, sym)) = resolve_symbol(scope, &name.stx.name) {
              mark_pinned(&decl_scope, sym);
            }
          }
        }
      }
      _ => {}
    }
  }
}

fn collect_pinned_symbols(
  top: &mut Node<TopLevel>,
  top_scope: &Scope,
  mode: TopLevelMode,
  opts: &MangleOptions,
) {
  match mode {
    TopLevelMode::Global => pin_scope_symbols(top_scope),
    TopLevelMode::Module => {
      if !opts.mangle_toplevel {
        pin_scope_symbols(top_scope);
      }
      pin_module_exports(top);
    }
  }

  if !opts.mangle_function_names || !opts.mangle_class_names {
    let mut visitor = NamePinVisitor { opts };
    top.drive_mut(&mut visitor);
  }
}

fn pin_pat_decl(decl: &Node<PatDecl>, pin: &mut impl FnMut(&Scope, Symbol)) {
  pin_pat(&decl.stx.pat, pin);
}

fn pin_pat(pat: &Node<Pat>, pin: &mut impl FnMut(&Scope, Symbol)) {
  match pat.stx.as_ref() {
    Pat::Id(id) => {
      if let Some(scope) = id.assoc.get::<Scope>() {
        if let Some((decl_scope, sym)) = resolve_symbol(scope, &id.stx.name) {
          pin(&decl_scope, sym);
        }
      }
    }
    Pat::Arr(arr) => pin_arr_pat(arr.stx.as_ref(), pin),
    Pat::Obj(obj) => pin_obj_pat(obj.stx.as_ref(), pin),
    Pat::AssignTarget(_) => {}
  }
}

fn pin_arr_pat(arr: &ArrPat, pin: &mut impl FnMut(&Scope, Symbol)) {
  for elem in arr.elements.iter().flatten() {
    pin_pat(&elem.target, pin);
  }
  if let Some(rest) = &arr.rest {
    pin_pat(rest, pin);
  }
}

fn pin_obj_pat(obj: &ObjPat, pin: &mut impl FnMut(&Scope, Symbol)) {
  for prop in obj.properties.iter() {
    pin_pat(&prop.stx.target, pin);
  }
  if let Some(rest) = &obj.rest {
    pin_pat(rest, pin);
  }
}

fn assign_scope_names(
  scope: &Scope,
  original_names: &HashMap<Symbol, String>,
  mapping: &mut HashMap<Symbol, String>,
) {
  if is_dynamic(scope) {
    return;
  }

  let pinned = pinned_symbols(scope);
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
  for sym in pinned.iter() {
    if let Some(name) = original_names.get(sym) {
      reserved.insert(name.clone());
    }
  }
  for sym in foreign_symbols(scope) {
    if let Some(name) = mapping.get(&sym) {
      reserved.insert(name.clone());
    } else if let Some(name) = original_names.get(&sym) {
      reserved.insert(name.clone());
    }
  }

  let mut generator = NameGenerator::default();

  for symbol in declared_symbols {
    if pinned.contains(&symbol) {
      continue;
    }
    let new_name = generator.next_name(&reserved);
    reserved.insert(new_name.clone());
    mapping.insert(symbol, new_name);
  }
}

fn default_reserved_names() -> HashSet<String> {
  let mut set = HashSet::default();
  for keyword in KEYWORDS_MAPPING.values() {
    set.insert((*keyword).to_string());
  }
  set.insert("eval".to_string());
  set.insert("arguments".to_string());
  set
}

fn tt_for_identifier(name: &str) -> TT {
  for (tt, keyword) in KEYWORDS_MAPPING.iter() {
    if *keyword == name {
      return *tt;
    }
  }
  TT::Identifier
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
type ObjMemberNode = Node<ObjMember>;
type ObjPatPropNode = Node<ObjPatProp>;
type ExportListStmtNode = Node<ExportListStmt>;

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
#[visitor(IdExprNode(enter), IdPatNode(enter), ExportListStmtNode(enter, exit))]
struct ConstraintVisitor {
  export_alias_stack: Vec<Vec<Loc>>,
}

impl ConstraintVisitor {
  fn is_export_alias(&self, loc: Loc) -> bool {
    self
      .export_alias_stack
      .iter()
      .any(|frame| frame.iter().any(|l| *l == loc))
  }

  fn record(&self, scope: &Scope, name: &str) {
    if let Some(sym) = scope.find_symbol(name.to_string()) {
      mark_foreign(scope, name, sym);
    } else {
      mark_unknown(scope, name);
    }
  }

  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    let scope = scope_from_assoc(&node.assoc);
    self.record(&scope, &node.stx.name);
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    if self.is_export_alias(node.loc) {
      return;
    }
    let scope = scope_from_assoc(&node.assoc);
    self.record(&scope, &node.stx.name);
  }

  fn enter_export_list_stmt_node(&mut self, node: &mut ExportListStmtNode) {
    let mut alias_locs = Vec::new();
    match &node.stx.names {
      ExportNames::Specific(names) => {
        for export_name in names.iter() {
          alias_locs.push(export_name.stx.alias.loc);
        }
      }
      ExportNames::All(alias) => {
        if let Some(id) = alias {
          alias_locs.push(id.loc);
        }
      }
    }
    self.export_alias_stack.push(alias_locs);

    if node.stx.from.is_some() {
      return;
    }

    let scope = scope_from_assoc(&node.assoc);
    if let ExportNames::Specific(names) = &node.stx.names {
      for export_name in names.iter() {
        if let ModuleExportImportName::Ident(exportable) = &export_name.stx.exportable {
          self.record(&scope, exportable);
        }
      }
    }
  }

  fn exit_export_list_stmt_node(&mut self, _node: &mut ExportListStmtNode) {
    self.export_alias_stack.pop();
  }
}

type FuncDeclNode = Node<FuncDecl>;
type FuncExprNode = Node<FuncExpr>;
type ClassDeclNode = Node<ClassDecl>;
type ClassExprNode = Node<ClassExpr>;

#[derive(VisitorMut)]
#[visitor(
  FuncDeclNode(enter),
  FuncExprNode(enter),
  ClassDeclNode(enter),
  ClassExprNode(enter)
)]
struct NamePinVisitor<'a> {
  opts: &'a MangleOptions,
}

impl NamePinVisitor<'_> {
  fn pin_name(&self, name: &Option<Node<ClassOrFuncName>>, should_pin: bool) {
    if !should_pin {
      return;
    }

    let Some(name) = name else {
      return;
    };

    let Some(scope) = name.assoc.get::<Scope>() else {
      return;
    };

    if let Some((decl_scope, sym)) = resolve_symbol(scope, &name.stx.name) {
      mark_pinned(&decl_scope, sym);
    }
  }

  fn enter_func_decl_node(&mut self, node: &mut FuncDeclNode) {
    self.pin_name(&node.stx.name, !self.opts.mangle_function_names);
  }

  fn enter_func_expr_node(&mut self, node: &mut FuncExprNode) {
    self.pin_name(&node.stx.name, !self.opts.mangle_function_names);
  }

  fn enter_class_decl_node(&mut self, node: &mut ClassDeclNode) {
    self.pin_name(&node.stx.name, !self.opts.mangle_class_names);
  }

  fn enter_class_expr_node(&mut self, node: &mut ClassExprNode) {
    self.pin_name(&node.stx.name, !self.opts.mangle_class_names);
  }
}

#[derive(VisitorMut)]
#[visitor(
  IdExprNode(enter),
  IdPatNode(enter),
  ClassOrFuncNameNode(enter),
  ObjMemberNode(enter),
  ObjPatPropNode(enter),
  ExportListStmtNode(enter, exit)
)]
struct RenameVisitor<'a> {
  mapping: &'a HashMap<Symbol, String>,
  export_alias_stack: Vec<Vec<Loc>>,
}

impl<'a> RenameVisitor<'a> {
  fn is_export_alias(&self, loc: Loc) -> bool {
    self
      .export_alias_stack
      .iter()
      .any(|frame| frame.iter().any(|l| *l == loc))
  }

  fn rename(&self, scope: Scope, name: &mut String) {
    if let Some(symbol) = scope.find_symbol(name.clone()) {
      if let Some(new_name) = self.mapping.get(&symbol) {
        *name = new_name.clone();
      }
    }
  }

  fn maybe_expand_obj_shorthand(&self, node: &mut ObjMemberNode) {
    let ObjMember { typ } = node.stx.as_mut();
    let ObjMemberType::Shorthand { id } = typ else {
      return;
    };

    let Some(scope) = id.assoc.get::<Scope>() else {
      return;
    };
    let Some(symbol) = scope.find_symbol(id.stx.name.clone()) else {
      return;
    };
    let Some(new_name) = self.mapping.get(&symbol) else {
      return;
    };

    let old_name = id.stx.name.clone();
    if &old_name == new_name {
      return;
    }

    id.stx.name = new_name.clone();
    let assoc = std::mem::take(&mut id.assoc);
    let value_id = Node {
      loc: id.loc,
      stx: Box::new(IdExpr {
        name: new_name.clone(),
      }),
      assoc,
    };
    let value_expr = value_id.into_wrapped::<Expr>();
    let key_node = Node::new(
      id.loc,
      ClassOrObjMemberDirectKey {
        key: old_name.clone(),
        tt: tt_for_identifier(&old_name),
      },
    );
    *typ = ObjMemberType::Valued {
      key: ClassOrObjKey::Direct(key_node),
      val: ClassOrObjVal::Prop(Some(value_expr)),
    };
  }

  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    let scope = scope_from_assoc(&node.assoc);
    self.rename(scope, &mut node.stx.name);
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    if self.is_export_alias(node.loc) {
      return;
    }
    let scope = scope_from_assoc(&node.assoc);
    self.rename(scope, &mut node.stx.name);
  }

  fn enter_class_or_func_name_node(&mut self, node: &mut ClassOrFuncNameNode) {
    let scope = scope_from_assoc(&node.assoc);
    self.rename(scope, &mut node.stx.name);
  }

  fn enter_obj_member_node(&mut self, node: &mut ObjMemberNode) {
    self.maybe_expand_obj_shorthand(node);
  }

  fn enter_obj_pat_prop_node(&mut self, node: &mut ObjPatPropNode) {
    if !node.stx.shorthand {
      return;
    }

    if let Pat::Id(id) = node.stx.target.stx.as_ref() {
      let Some(scope) = id.assoc.get::<Scope>() else {
        return;
      };
      let Some(symbol) = scope.find_symbol(id.stx.name.clone()) else {
        return;
      };
      if self
        .mapping
        .get(&symbol)
        .is_some_and(|new_name| new_name != &id.stx.name)
      {
        node.stx.shorthand = false;
      }
    }
  }

  fn enter_export_list_stmt_node(&mut self, node: &mut ExportListStmtNode) {
    let mut alias_locs = Vec::new();
    match &mut node.stx.names {
      ExportNames::Specific(entries) => {
        for entry in entries.iter_mut() {
          alias_locs.push(entry.stx.alias.loc);
          if node.stx.from.is_none() {
            if let ModuleExportImportName::Ident(exportable) = &entry.stx.exportable {
              let scope = scope_from_assoc(&node.assoc);
              if let Some(symbol) = scope.find_symbol(exportable.clone()) {
                if let Some(new_name) = self.mapping.get(&symbol) {
                  entry.stx.exportable = ModuleExportImportName::Ident(new_name.clone());
                }
              }
            }
          }
        }
      }
      ExportNames::All(alias) => {
        if let Some(id) = alias {
          alias_locs.push(id.loc);
        }
      }
    }
    self.export_alias_stack.push(alias_locs);
  }

  fn exit_export_list_stmt_node(&mut self, _node: &mut ExportListStmtNode) {
    self.export_alias_stack.pop();
  }
}
