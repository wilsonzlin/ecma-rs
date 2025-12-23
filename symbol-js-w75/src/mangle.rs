use crate::compute_symbols;
use crate::symbol::Scope;
use crate::symbol::Symbol;
use crate::TopLevelMode;
use ahash::HashMap;
use ahash::HashMapExt;
use ahash::HashSet;
use ahash::HashSetExt;
use derive_visitor::Drive;
use derive_visitor::DriveMut;
use derive_visitor::Visitor;
use derive_visitor::VisitorMut;
use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::class_or_object::ClassOrObjMemberDirectKey;
use parse_js::ast::class_or_object::ClassOrObjVal;
use parse_js::ast::class_or_object::ObjMember;
use parse_js::ast::class_or_object::ObjMemberType;
use parse_js::ast::expr::pat::ArrPat;
use parse_js::ast::expr::pat::ClassOrFuncName;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::pat::ObjPat;
use parse_js::ast::expr::pat::ObjPatProp;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::ClassExpr;
use parse_js::ast::expr::FuncExpr;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::import_export::ExportNames;
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::stmt::decl::ClassDecl;
use parse_js::ast::stmt::decl::FuncDecl;
use parse_js::ast::stmt::decl::PatDecl;
use parse_js::ast::stmt::ExportListStmt;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::lex::KEYWORDS_MAPPING;
use parse_js::loc::Loc;
use parse_js::token::TT;
use std::iter::FromIterator;

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
struct ScopeConstraints {
  /// Identifier names that must not be used in this scope or any descendant.
  unknown: HashSet<String>,
  /// Symbols from ancestor scopes that are referenced within this scope or its descendants.
  foreign: HashSet<Symbol>,
  /// Symbols declared in this scope that must retain their original names.
  pinned: HashSet<Symbol>,
}

fn reserved_words() -> HashSet<String> {
  let mut set = HashSet::new();
  for keyword in KEYWORDS_MAPPING.values() {
    set.insert((*keyword).to_string());
  }
  set.insert("eval".to_string());
  set.insert("arguments".to_string());
  set
}

fn resolve_symbol(scope: &Scope, name: &str) -> Option<(Scope, Symbol)> {
  for sc in scope.self_and_ancestors() {
    let sym = sc.data().get_symbol(name);
    if let Some(sym) = sym {
      return Some((sc, sym));
    }
  }
  None
}

fn mark_pinned(constraints: &mut HashMap<Scope, ScopeConstraints>, scope: &Scope, symbol: Symbol) {
  constraints
    .entry(scope.clone())
    .or_default()
    .pinned
    .insert(symbol);
}

fn collect_scope_symbols(
  scope: &Scope,
  per_scope: &mut HashMap<Scope, Vec<(String, Symbol)>>,
  original_names: &mut HashMap<Symbol, String>,
) {
  let data = scope.data();
  let mut symbols = Vec::new();
  for name in data.symbol_names().iter() {
    if let Some(sym) = data.get_symbol(name) {
      original_names.entry(sym).or_insert_with(|| name.clone());
      symbols.push((name.clone(), sym));
    }
  }
  per_scope.insert(scope.clone(), symbols);
  for child in data.children() {
    collect_scope_symbols(child, per_scope, original_names);
  }
}

fn base54_name(mut n: usize) -> String {
  const LEADING: &[u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ$_";
  const OTHERS: &[u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ$_0123456789";
  let mut ret = String::new();
  let mut base = 54;
  n += 1;
  loop {
    n -= 1;
    let idx = n % base;
    let ch = if base == 54 {
      LEADING[idx]
    } else {
      OTHERS[idx]
    } as char;
    ret.push(ch);
    n /= base;
    base = 64;
    if n == 0 {
      break;
    }
  }
  ret
}

fn tt_for_identifier(name: &str) -> TT {
  for (tt, keyword) in KEYWORDS_MAPPING.iter() {
    if *keyword == name {
      return *tt;
    }
  }
  TT::Identifier
}

fn pin_scope_symbols(scope: &Scope, constraints: &mut HashMap<Scope, ScopeConstraints>) {
  let data = scope.data();
  for name in data.symbol_names().iter() {
    if let Some(sym) = data.get_symbol(name) {
      mark_pinned(constraints, scope, sym);
    }
  }
}

fn pin_pat_decl(decl: &PatDecl, constraints: &mut HashMap<Scope, ScopeConstraints>) {
  pin_pat(&decl.pat, constraints);
}

fn pin_pat(pat: &Node<Pat>, constraints: &mut HashMap<Scope, ScopeConstraints>) {
  match pat.stx.as_ref() {
    Pat::Id(id) => {
      if let Some(scope) = id.assoc.get::<Scope>() {
        if let Some((decl_scope, sym)) = resolve_symbol(scope, &id.stx.name) {
          mark_pinned(constraints, &decl_scope, sym);
        }
      }
    }
    Pat::Arr(arr) => pin_arr_pat(arr.stx.as_ref(), constraints),
    Pat::Obj(obj) => pin_obj_pat(obj.stx.as_ref(), constraints),
    Pat::AssignTarget(_) => {}
  }
}

fn pin_arr_pat(arr: &ArrPat, constraints: &mut HashMap<Scope, ScopeConstraints>) {
  for elem in arr.elements.iter().flatten() {
    pin_pat(&elem.target, constraints);
  }
  if let Some(rest) = &arr.rest {
    pin_pat(rest, constraints);
  }
}

fn pin_obj_pat(obj: &ObjPat, constraints: &mut HashMap<Scope, ScopeConstraints>) {
  for prop in obj.properties.iter() {
    pin_pat(&prop.stx.target, constraints);
  }
  if let Some(rest) = &obj.rest {
    pin_pat(rest, constraints);
  }
}

fn pin_module_exports(
  top: &Node<TopLevel>,
  constraints: &mut HashMap<Scope, ScopeConstraints>,
  mode: TopLevelMode,
) {
  if mode != TopLevelMode::Module {
    return;
  }
  for stmt in top.stx.body.iter() {
    match stmt.stx.as_ref() {
      Stmt::VarDecl(var) if var.stx.export => {
        for declarator in var.stx.declarators.iter() {
          pin_pat_decl(&declarator.pattern.stx, constraints);
        }
      }
      Stmt::FunctionDecl(func) if func.stx.export && !func.stx.export_default => {
        if let Some(name) = &func.stx.name {
          if let Some(scope) = name.assoc.get::<Scope>() {
            if let Some((decl_scope, sym)) = resolve_symbol(scope, &name.stx.name) {
              mark_pinned(constraints, &decl_scope, sym);
            }
          }
        }
      }
      Stmt::ClassDecl(class) if class.stx.export && !class.stx.export_default => {
        if let Some(name) = &class.stx.name {
          if let Some(scope) = name.assoc.get::<Scope>() {
            if let Some((decl_scope, sym)) = resolve_symbol(scope, &name.stx.name) {
              mark_pinned(constraints, &decl_scope, sym);
            }
          }
        }
      }
      _ => {}
    }
  }
}

#[derive(Visitor)]
#[visitor(IdExprNode(enter), IdPatNode(enter), ExportListStmtNode(enter, exit))]
struct ConstraintCollector<'a> {
  constraints: &'a mut HashMap<Scope, ScopeConstraints>,
  export_alias_stack: Vec<Vec<Loc>>,
}

type IdExprNode = Node<IdExpr>;
type IdPatNode = Node<IdPat>;
type ExportListStmtNode = Node<ExportListStmt>;

impl<'a> ConstraintCollector<'a> {
  fn record_unknown(&mut self, scope: &Scope, name: &str) {
    for sc in scope.self_and_ancestors() {
      self
        .constraints
        .entry(sc.clone())
        .or_default()
        .unknown
        .insert(name.to_string());
    }
  }

  fn record_foreign(&mut self, usage_scope: &Scope, decl_scope: &Scope, sym: Symbol) {
    let mut cur = usage_scope.clone();
    while cur != *decl_scope {
      self
        .constraints
        .entry(cur.clone())
        .or_default()
        .foreign
        .insert(sym);
      let parent = { cur.data().parent().cloned() };
      if let Some(parent) = parent {
        cur = parent;
      } else {
        break;
      }
    }
  }

  fn handle_usage(&mut self, scope: &Scope, name: &str) {
    match resolve_symbol(scope, name) {
      Some((decl_scope, sym)) => {
        if &decl_scope != scope {
          self.record_foreign(scope, &decl_scope, sym);
        }
      }
      None => self.record_unknown(scope, name),
    }
  }

  fn enter_id_expr_node(&mut self, node: &IdExprNode) {
    if let Some(scope) = node.assoc.get::<Scope>() {
      self.handle_usage(scope, &node.stx.name);
    }
  }

  fn enter_id_pat_node(&mut self, node: &IdPatNode) {
    if self
      .export_alias_stack
      .iter()
      .any(|frame| frame.iter().any(|l| *l == node.loc))
    {
      return;
    }
    if let Some(scope) = node.assoc.get::<Scope>() {
      self.handle_usage(scope, &node.stx.name);
    }
  }

  fn enter_export_list_stmt_node(&mut self, node: &ExportListStmtNode) {
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
    if let Some(scope) = node.assoc.get::<Scope>() {
      match &node.stx.names {
        ExportNames::Specific(names) => {
          for export_name in names.iter() {
            self.handle_usage(scope, &export_name.stx.exportable);
          }
        }
        ExportNames::All(_) => {}
      }
    }
  }

  fn exit_export_list_stmt_node(&mut self, _node: &ExportListStmtNode) {
    self.export_alias_stack.pop();
  }
}

#[derive(Visitor)]
#[visitor(
  FuncDeclNode(enter),
  FuncExprNode(enter),
  ClassDeclNode(enter),
  ClassExprNode(enter)
)]
struct NamePinCollector<'a> {
  opts: &'a MangleOptions,
  constraints: &'a mut HashMap<Scope, ScopeConstraints>,
}

type FuncDeclNode = Node<FuncDecl>;
type FuncExprNode = Node<FuncExpr>;
type ClassDeclNode = Node<ClassDecl>;
type ClassExprNode = Node<ClassExpr>;

impl<'a> NamePinCollector<'a> {
  fn pin_name(&mut self, name: &Option<Node<ClassOrFuncName>>, should_pin: bool) {
    if !should_pin {
      return;
    }
    if let Some(name) = name {
      if let Some(scope) = name.assoc.get::<Scope>() {
        if let Some((decl_scope, sym)) = resolve_symbol(scope, &name.stx.name) {
          mark_pinned(self.constraints, &decl_scope, sym);
        }
      }
    }
  }

  fn enter_func_decl_node(&mut self, node: &FuncDeclNode) {
    self.pin_name(&node.stx.name, !self.opts.mangle_function_names);
  }

  fn enter_func_expr_node(&mut self, node: &FuncExprNode) {
    self.pin_name(&node.stx.name, !self.opts.mangle_function_names);
  }

  fn enter_class_decl_node(&mut self, node: &ClassDeclNode) {
    self.pin_name(&node.stx.name, !self.opts.mangle_class_names);
  }

  fn enter_class_expr_node(&mut self, node: &ClassExprNode) {
    self.pin_name(&node.stx.name, !self.opts.mangle_class_names);
  }
}

fn assign_scope_names(
  scope: &Scope,
  scope_symbols: &HashMap<Scope, Vec<(String, Symbol)>>,
  constraints: &HashMap<Scope, ScopeConstraints>,
  reserved: &HashSet<String>,
  renamed: &mut HashMap<Symbol, String>,
  assigned: &mut HashMap<Symbol, String>,
  original_names: &HashMap<Symbol, String>,
) {
  let info = constraints.get(scope);
  let mut used: HashSet<String> = HashSet::from_iter(reserved.iter().cloned());
  if let Some(info) = info {
    used.extend(info.unknown.iter().cloned());
    for sym in info.foreign.iter() {
      if let Some(name) = assigned.get(sym) {
        used.insert(name.clone());
      }
    }
    for sym in info.pinned.iter() {
      if let Some(name) = original_names.get(sym) {
        used.insert(name.clone());
        assigned.entry(*sym).or_insert_with(|| name.clone());
      }
    }
  }

  let mut counter = 0usize;
  if let Some(symbols) = scope_symbols.get(scope) {
    for (original, sym) in symbols.iter() {
      let is_pinned = info.map_or(false, |c| c.pinned.contains(sym));
      let orig_name = original_names
        .get(sym)
        .cloned()
        .unwrap_or_else(|| original.clone());
      if is_pinned {
        assigned.entry(*sym).or_insert_with(|| orig_name.clone());
        used.insert(orig_name);
        continue;
      }

      let mut candidate;
      loop {
        candidate = base54_name(counter);
        counter += 1;
        if used.contains(&candidate) {
          continue;
        }
        break;
      }
      used.insert(candidate.clone());
      if candidate != orig_name {
        renamed.insert(*sym, candidate.clone());
      }
      assigned.insert(*sym, candidate);
    }
  }

  for child in scope.data().children().iter() {
    assign_scope_names(
      child,
      scope_symbols,
      constraints,
      reserved,
      renamed,
      assigned,
      original_names,
    );
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
  renamed: &'a HashMap<Symbol, String>,
  export_alias_stack: Vec<Vec<Loc>>,
}

type ClassOrFuncNameNode = Node<ClassOrFuncName>;
type ObjMemberNode = Node<ObjMember>;
type ObjPatPropNode = Node<ObjPatProp>;

impl<'a> RenameVisitor<'a> {
  fn rename_identifier(&self, assoc: &NodeAssocData, name: &mut String) {
    if let Some(scope) = assoc.get::<Scope>() {
      if let Some((_decl_scope, sym)) = resolve_symbol(scope, name) {
        if let Some(new) = self.renamed.get(&sym) {
          *name = new.clone();
        }
      }
    }
  }

  fn is_export_alias(&self, loc: Loc) -> bool {
    self
      .export_alias_stack
      .iter()
      .any(|frame| frame.iter().any(|l| *l == loc))
  }

  fn maybe_expand_obj_shorthand(&self, node: &mut ObjMemberNode) {
    let ObjMember { typ } = node.stx.as_mut();
    let ObjMemberType::Shorthand { id } = typ else {
      return;
    };
    let Some(scope) = id.assoc.get::<Scope>() else {
      return;
    };
    let Some((_decl_scope, sym)) = resolve_symbol(scope, &id.stx.name) else {
      return;
    };
    let Some(new_name) = self.renamed.get(&sym) else {
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
    let value_expr = value_id.into_wrapped::<parse_js::ast::expr::Expr>();
    let key_node = Node::new(id.loc, ClassOrObjMemberDirectKey {
      key: old_name.clone(),
      tt: tt_for_identifier(&old_name),
    });
    *typ = ObjMemberType::Valued {
      key: ClassOrObjKey::Direct(key_node),
      val: ClassOrObjVal::Prop(Some(value_expr)),
    };
  }
}

impl<'a> RenameVisitor<'a> {
  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    self.rename_identifier(&node.assoc, &mut node.stx.name);
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    if self.is_export_alias(node.loc) {
      return;
    }
    self.rename_identifier(&node.assoc, &mut node.stx.name);
  }

  fn enter_class_or_func_name_node(&mut self, node: &mut ClassOrFuncNameNode) {
    self.rename_identifier(&node.assoc, &mut node.stx.name);
  }

  fn enter_obj_member_node(&mut self, node: &mut ObjMemberNode) {
    self.maybe_expand_obj_shorthand(node);
  }

  fn enter_obj_pat_prop_node(&mut self, node: &mut ObjPatPropNode) {
    if !node.stx.shorthand {
      return;
    }
    if let Pat::Id(id) = node.stx.target.stx.as_ref() {
      if let Some(scope) = id.assoc.get::<Scope>() {
        if let Some((_decl_scope, sym)) = resolve_symbol(scope, &id.stx.name) {
          if self
            .renamed
            .get(&sym)
            .is_some_and(|new_name| new_name != &id.stx.name)
          {
            node.stx.shorthand = false;
          }
        }
      }
    }
  }

  fn enter_export_list_stmt_node(&mut self, node: &mut ExportListStmtNode) {
    let mut alias_locs = Vec::new();
    match &mut node.stx.names {
      ExportNames::Specific(names) => {
        for export_name in names.iter_mut() {
          alias_locs.push(export_name.stx.alias.loc);
          if node.stx.from.is_none() {
            if let Some(scope) = node.assoc.get::<Scope>() {
              if let Some((_, sym)) = resolve_symbol(scope, &export_name.stx.exportable) {
                if let Some(new) = self.renamed.get(&sym) {
                  export_name.stx.exportable = new.clone();
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

/// Perform identifier mangling on the provided AST. This computes symbols internally.
pub fn mangle_identifiers(
  top: &mut Node<TopLevel>,
  mode: TopLevelMode,
  opts: &MangleOptions,
) -> MangleResult {
  let top_scope = compute_symbols(top, mode);
  let mut constraints: HashMap<Scope, ScopeConstraints> = HashMap::new();
  let mut scope_symbols: HashMap<Scope, Vec<(String, Symbol)>> = HashMap::new();
  let mut original_names: HashMap<Symbol, String> = HashMap::new();
  collect_scope_symbols(&top_scope, &mut scope_symbols, &mut original_names);

  if mode == TopLevelMode::Global {
    pin_scope_symbols(&top_scope, &mut constraints);
  } else if !opts.mangle_toplevel {
    pin_scope_symbols(&top_scope, &mut constraints);
  }

  pin_module_exports(top, &mut constraints, mode);

  {
    let mut pin_collector = NamePinCollector {
      opts,
      constraints: &mut constraints,
    };
    top.drive(&mut pin_collector);
  }

  {
    let mut collector = ConstraintCollector {
      constraints: &mut constraints,
      export_alias_stack: Vec::new(),
    };
    top.drive(&mut collector);
  }

  let reserved = reserved_words();
  let mut renamed: HashMap<Symbol, String> = HashMap::new();
  let mut assigned: HashMap<Symbol, String> = HashMap::new();
  assign_scope_names(
    &top_scope,
    &scope_symbols,
    &constraints,
    &reserved,
    &mut renamed,
    &mut assigned,
    &original_names,
  );

  {
    let mut renamer = RenameVisitor {
      renamed: &renamed,
      export_alias_stack: Vec::new(),
    };
    top.drive_mut(&mut renamer);
  }

  MangleResult { renamed }
}
