use ahash::{HashMap, HashSet};
use derive_visitor::{DriveMut, VisitorMut};
use parse_js::ast::class_or_object::{
  ClassOrObjKey, ClassOrObjMemberDirectKey, ClassOrObjVal, ObjMember, ObjMemberType,
};
use parse_js::ast::expr::lit::{LitNullExpr, LitStrExpr};
use parse_js::ast::expr::pat::{ClassOrFuncName, IdPat, ObjPatProp, Pat};
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::import_export::{ExportName, ModuleExportImportName};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{ClassDecl, FuncDecl, VarDecl};
use parse_js::ast::stmt::ExportListStmt;
use parse_js::ast::stx::TopLevel;
use parse_js::lex::KEYWORDS_MAPPING;
use parse_js::lex::{lex_next, LexMode, Lexer};
use parse_js::loc::Loc;
use parse_js::parse::expr::pat::{is_valid_pattern_identifier, ParsePatternRules};
use parse_js::token::{keyword_from_str, TT};
use parse_js::Dialect;
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
pub(crate) struct ExportNameSymbol(pub(crate) SymbolId);

#[cfg_attr(feature = "emit-minify", allow(dead_code))]
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
  export_list_from_stack: Vec<bool>,
  ignore_id_pats: usize,
  scope_usages: HashMap<ScopeId, ScopeUsages>,
}

type ClassDeclNode = Node<ClassDecl>;
type ClassOrFuncNameNode = Node<ClassOrFuncName>;
type ExportNameNode = Node<ExportName>;
type ExportListStmtNode = Node<ExportListStmt>;
type FuncDeclNode = Node<FuncDecl>;
type IdExprNode = Node<IdExpr>;
type IdPatNode = Node<IdPat>;
type ObjMemberNode = Node<ObjMember>;
type ObjPatPropNode = Node<ObjPatProp>;
type TopLevelNode = Node<TopLevel>;
type VarDeclNode = Node<VarDecl>;

#[derive(VisitorMut)]
#[visitor(
  ClassDeclNode(enter, exit),
  ClassOrFuncNameNode(enter),
  ExportListStmtNode(enter, exit),
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
      export_list_from_stack: Vec::new(),
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
  fn enter_export_list_stmt_node(&mut self, node: &mut ExportListStmtNode) {
    self
      .inner
      .export_list_from_stack
      .push(node.stx.from.is_some());
  }

  fn exit_export_list_stmt_node(&mut self, _node: &mut ExportListStmtNode) {
    self.inner.export_list_from_stack.pop();
  }

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
    let is_reexport = self
      .inner
      .export_list_from_stack
      .last()
      .copied()
      .unwrap_or(false);
    if !is_reexport {
      if let Some(scope) = scope_id(&node.assoc) {
        let exportable = node.stx.exportable.as_str();
        if let Some(sym) = self.inner.resolve_export_name(scope, exportable) {
          node.assoc.set(ExportNameSymbol(sym));
          self.inner.record_symbol_usage(scope, sym);
        } else {
          self.inner.record_unknown(scope, exportable);
        }
      }
    }
    self.inner.ignore_id_pats += 1;
  }

  fn exit_export_name_node(&mut self, _node: &mut ExportNameNode) {
    if self.inner.ignore_id_pats > 0 {
      self.inner.ignore_id_pats -= 1;
    }
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
  let mut names: HashSet<String> = KEYWORDS_MAPPING.values().map(|s| s.to_string()).collect();
  // These are reserved words in JavaScript and cannot be used as binding identifiers.
  names.insert("true".to_string());
  names.insert("false".to_string());
  names.insert("null".to_string());
  // Strict-mode reserved word (but lexed as an identifier).
  names.insert("package".to_string());
  // Strict-mode restricted identifiers.
  names.insert("eval".to_string());
  names.insert("arguments".to_string());
  names
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

  let mut annex_b_block_to_var = HashMap::default();
  let mut annex_b_var_to_blocks: HashMap<SymbolId, Vec<SymbolId>> = HashMap::default();
  for (block, var_sym) in sem.annex_b_function_decls.iter() {
    annex_b_block_to_var.insert(*block, *var_sym);
    annex_b_var_to_blocks
      .entry(*var_sym)
      .or_default()
      .push(*block);
  }
  for blocks in annex_b_var_to_blocks.values_mut() {
    blocks.sort_by_key(|sym| sym.raw());
  }

  fn assign_scope(
    scope: ScopeId,
    sem: &JsSemantics,
    usage: &UsageData,
    reserved: &HashSet<String>,
    disabled_scopes: &HashSet<ScopeId>,
    pinned_symbols: &HashSet<SymbolId>,
    annex_b_block_to_var: &HashMap<SymbolId, SymbolId>,
    annex_b_var_to_blocks: &HashMap<SymbolId, Vec<SymbolId>>,
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
        assign_scope(
          child,
          sem,
          usage,
          reserved,
          disabled_scopes,
          pinned_symbols,
          annex_b_block_to_var,
          annex_b_var_to_blocks,
          renames,
        );
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

    // Reserve any pinned bindings before generating new names so we never
    // accidentally rename another symbol to the same identifier.
    for sym in symbol_order.iter() {
      let Some(name) = usage.symbol_names.get(sym) else {
        continue;
      };
      if usage.exported.contains(sym) || pinned_symbols.contains(sym) {
        used.insert(name.clone());
      }
    }

    // Annex B block functions (sloppy scripts) introduce two linked bindings
    // (block + hoisted var). The function name token is shared, so all linked
    // symbols must receive the same rename. Reserve the final group name in the
    // block scope up-front so later renames cannot collide.
    for sym in symbol_order.iter() {
      let Some(rep) = annex_b_block_to_var.get(sym).copied() else {
        continue;
      };
      let mut group_name = renames
        .get(&rep)
        .cloned()
        .or_else(|| usage.symbol_names.get(&rep).cloned());
      if group_name.is_none() {
        group_name = usage.symbol_names.get(sym).cloned();
      }
      if let Some(name) = group_name {
        used.insert(name);
      }
      if let Some(name) = renames.get(&rep).cloned() {
        renames.insert(*sym, name);
      }
    }

    for sym in symbol_order {
      if annex_b_block_to_var.contains_key(&sym) {
        continue;
      }

      let Some(name) = usage.symbol_names.get(&sym) else {
        continue;
      };

      if let Some(blocks) = annex_b_var_to_blocks.get(&sym) {
        let mut pinned = usage.exported.contains(&sym) || pinned_symbols.contains(&sym);
        for block in blocks.iter() {
          let block_scope = sem.symbol(*block).decl_scope;
          if disabled_scopes.contains(&block_scope) {
            pinned = true;
            break;
          }
        }
        if pinned {
          used.insert(name.clone());
          continue;
        }

        let mut group_disallowed: HashSet<String> = HashSet::default();
        for block in blocks.iter() {
          let block_scope = sem.symbol(*block).decl_scope;
          group_disallowed.extend(reserved.iter().cloned());
          if let Some(u) = usage.scope_usages.get(&block_scope) {
            for foreign in u.foreign.iter() {
              if let Some(foreign_name) = renames.get(foreign) {
                group_disallowed.insert(foreign_name.clone());
              } else if let Some(foreign_name) = usage.symbol_names.get(foreign) {
                group_disallowed.insert(foreign_name.clone());
              }
            }
            for unknown in u.unknown.iter() {
              group_disallowed.insert(unknown.clone());
            }
          }

          if let Some(order) = usage.scope_symbol_order.get(&block_scope) {
            for local_sym in order.iter() {
              if usage.exported.contains(local_sym) || pinned_symbols.contains(local_sym) {
                if let Some(local_name) = usage.symbol_names.get(local_sym) {
                  group_disallowed.insert(local_name.clone());
                }
              }
            }
          }
        }

        let new_name = generator.next_name(|candidate| {
          !disallowed.contains(candidate)
            && !used.contains(candidate)
            && !group_disallowed.contains(candidate)
        });
        used.insert(new_name.clone());
        renames.insert(sym, new_name.clone());
        for block in blocks.iter().copied() {
          renames.insert(block, new_name.clone());
        }
        continue;
      }

      if usage.exported.contains(&sym) || pinned_symbols.contains(&sym) {
        // Already reserved above.
        continue;
      }
      let new_name = generator
        .next_name(|candidate| !disallowed.contains(candidate) && !used.contains(candidate));
      used.insert(new_name.clone());
      renames.insert(sym, new_name);
    }

    for child in children {
      assign_scope(
        child,
        sem,
        usage,
        reserved,
        disabled_scopes,
        pinned_symbols,
        annex_b_block_to_var,
        annex_b_var_to_blocks,
        renames,
      );
    }
  }

  assign_scope(
    usage.top_scope,
    sem,
    usage,
    &reserved,
    &disabled_scopes,
    &pinned_symbols,
    &annex_b_block_to_var,
    &annex_b_var_to_blocks,
    &mut renames,
  );
  renames
}

#[derive(VisitorMut)]
#[visitor(
  ClassOrFuncNameNode(enter),
  ExportListStmtNode(enter, exit),
  ExportNameNode(enter),
  IdExprNode(enter),
  IdPatNode(enter),
  ObjMemberNode(enter),
  ObjPatPropNode(enter)
)]
struct ApplyVisitor<'a> {
  renames: &'a HashMap<SymbolId, String>,
  replacements: Vec<Replacement>,
  in_export_list: usize,
}

impl<'a> ApplyVisitor<'a> {
  fn enter_obj_member_node(&mut self, node: &mut ObjMemberNode) {
    let ObjMemberType::Shorthand { id } = &node.stx.typ else {
      return;
    };
    let Some(sym) = resolved_symbol(&id.assoc) else {
      return;
    };
    let Some(new_name) = self.renames.get(&sym) else {
      return;
    };
    if &id.stx.name == new_name {
      return;
    }

    let dummy = ObjMemberType::Rest {
      val: Node::new(
        Loc(0, 0),
        Expr::LitNull(Node::new(Loc(0, 0), LitNullExpr {})),
      ),
    };
    let typ = std::mem::replace(&mut node.stx.typ, dummy);
    let ObjMemberType::Shorthand { mut id } = typ else {
      node.stx.typ = typ;
      return;
    };

    let old_name = id.stx.name.clone();
    let key_end = id.loc.0 + old_name.len();
    if old_name == "__proto__" {
      self.replacements.push(Replacement {
        start: id.loc.0,
        end: key_end,
        text: r#"["__proto__"]"#.to_string(),
      });
    }
    self.replacements.push(Replacement {
      start: key_end,
      end: key_end,
      text: format!(":{new_name}"),
    });

    id.stx.name = new_name.clone();

    let key = if old_name == "__proto__" {
      ClassOrObjKey::Computed(Node::new(
        id.loc,
        Expr::LitStr(Node::new(
          id.loc,
          LitStrExpr {
            value: old_name.clone(),
          },
        )),
      ))
    } else {
      let tt = keyword_from_str(&old_name).unwrap_or(TT::Identifier);
      ClassOrObjKey::Direct(Node::new(
        id.loc,
        ClassOrObjMemberDirectKey {
          key: old_name.clone(),
          tt,
        },
      ))
    };

    node.stx.typ = ObjMemberType::Valued {
      key,
      val: ClassOrObjVal::Prop(Some(Node::new(id.loc, Expr::Id(id)))),
    };
  }

  fn enter_obj_pat_prop_node(&mut self, node: &mut ObjPatPropNode) {
    if !node.stx.shorthand {
      return;
    }
    let Pat::Id(id) = node.stx.target.stx.as_mut() else {
      return;
    };
    let Some(sym) = resolved_symbol(&id.assoc) else {
      return;
    };
    let Some(new_name) = self.renames.get(&sym) else {
      return;
    };
    if &id.stx.name == new_name {
      return;
    }

    let old_name = id.stx.name.clone();
    let insert_pos = id.loc.0 + old_name.len();
    self.replacements.push(Replacement {
      start: insert_pos,
      end: insert_pos,
      text: format!(":{new_name}"),
    });
    id.stx.name = new_name.clone();
    node.stx.shorthand = false;
  }

  fn enter_export_list_stmt_node(&mut self, _node: &mut ExportListStmtNode) {
    self.in_export_list += 1;
  }

  fn exit_export_list_stmt_node(&mut self, _node: &mut ExportListStmtNode) {
    if self.in_export_list > 0 {
      self.in_export_list -= 1;
    }
  }

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
    let start = node.loc.0;
    let end = start + node.stx.name.len();
    self.maybe_apply((start, end), sym, &mut node.stx.name);
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    if self.in_export_list > 0 {
      return;
    }
    let sym = resolved_symbol(&node.assoc);
    let start = node.loc.0;
    let end = start + node.stx.name.len();
    self.maybe_apply((start, end), sym, &mut node.stx.name);
  }

  fn enter_class_or_func_name_node(&mut self, node: &mut ClassOrFuncNameNode) {
    let sym = declared_symbol(&node.assoc);
    let start = node.loc.0;
    let end = start + node.stx.name.len();
    self.maybe_apply((start, end), sym, &mut node.stx.name);
  }

  fn enter_export_name_node(&mut self, node: &mut ExportNameNode) {
    let Some(sym) = node.assoc.get::<ExportNameSymbol>().map(|s| s.0) else {
      return;
    };
    let Some(new_name) = self.renames.get(&sym) else {
      return;
    };
    let alias_raw = &node.stx.alias.stx.name;
    let alias = if alias_raw == "default" || is_module_binding_identifier_token(alias_raw) {
      alias_raw.clone()
    } else {
      js_string_literal(alias_raw)
    };
    let replacement = if alias_raw == new_name {
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
    in_export_list: 0,
  };
  top.drive_mut(&mut visitor);
  visitor.replacements
}

#[cfg_attr(feature = "emit-minify", allow(dead_code))]
pub fn rewrite_source(source: &str, replacements: &mut Vec<Replacement>) -> String {
  // `Node::loc.end` can include lookahead tokens because the parser buffers
  // lexed tokens; `apply_renames` therefore computes identifier replacement
  // ranges as `loc.start + name.len()`.
  //
  // When we rewrite the original source (the non-emit backend), ensure
  // replacements that begin at a quote cover the entire string literal token.
  // Only extend ranges that are too short; never shrink, as some replacements
  // (e.g. export specifier rewrites) intentionally span more than the first
  // string token.
  for rep in replacements.iter_mut() {
    let Some(quote) = source.as_bytes().get(rep.start).copied() else {
      continue;
    };
    let quote_char = match quote {
      b'"' => '"',
      b'\'' => '\'',
      _ => continue,
    };
    let mut escaped = false;
    for (offset, ch) in source[rep.start + 1..].char_indices() {
      if escaped {
        escaped = false;
        continue;
      }
      if ch == '\\' {
        escaped = true;
        continue;
      }
      if ch == quote_char {
        let literal_end = rep.start + 1 + offset + ch.len_utf8();
        if rep.end < literal_end {
          rep.end = literal_end;
        }
        break;
      }
    }
  }

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

fn js_string_literal(value: &str) -> String {
  let mut out = String::with_capacity(value.len() + 2);
  out.push('"');
  for ch in value.chars() {
    match ch {
      '"' => out.push_str("\\\""),
      '\\' => out.push_str("\\\\"),
      '\n' => out.push_str("\\n"),
      '\r' => out.push_str("\\r"),
      '\t' => out.push_str("\\t"),
      '\u{0008}' => out.push_str("\\b"),
      '\u{000C}' => out.push_str("\\f"),
      // Line separators must be escaped in string literals.
      '\u{2028}' => out.push_str("\\u2028"),
      '\u{2029}' => out.push_str("\\u2029"),
      c if c.is_control() => {
        use std::fmt::Write;
        let _ = write!(out, "\\x{:02x}", c as u32);
      }
      c => out.push(c),
    }
  }
  out.push('"');
  out
}

fn is_module_binding_identifier_token(name: &str) -> bool {
  let mut lexer = Lexer::new(name);
  let token = lex_next(&mut lexer, LexMode::Standard, Dialect::Ts);
  if token.loc.0 != 0 || token.loc.1 != name.len() {
    return false;
  }
  is_valid_pattern_identifier(
    token.typ,
    ParsePatternRules {
      await_allowed: false,
      yield_allowed: false,
      await_expr_allowed: true,
      yield_expr_allowed: false,
    },
  )
}

#[cfg(test)]
mod tests {
  use super::*;
  use diagnostics::FileId;
  use parse_js::{parse_with_options, ParseOptions, SourceType};
  use semantic_js::js::bind_js;

  #[test]
  fn reserved_names_excludes_boolean_and_null_literals() {
    let names = reserved_names();
    assert!(names.contains("true"));
    assert!(names.contains("false"));
    assert!(names.contains("null"));
    assert!(names.contains("package"));
    assert!(names.contains("eval"));
    assert!(names.contains("arguments"));
  }

  #[test]
  fn rewrite_source_uses_node_locs_for_identifier_replacements() {
    let source = "const foo=1;";
    let mut ast = parse_with_options(
      source,
      ParseOptions {
        dialect: Dialect::Js,
        source_type: SourceType::Module,
      },
    )
    .expect("parse");
    let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(0));
    assert!(diagnostics.is_empty());
    let usage = collect_usages(&mut ast, &sem, TopLevelMode::Module);
    let renames = assign_names(&sem, &usage);

    let mut replacements = apply_renames(&mut ast, &renames);
    let rewritten = rewrite_source(source, &mut replacements);
    assert_eq!(rewritten, "const a=1;");
  }

  #[test]
  fn annex_b_block_function_symbols_share_a_rename() {
    let source = "function outer(){ if(true){ function foo(){} foo; } foo; }";
    let mut ast = parse_with_options(
      source,
      ParseOptions {
        dialect: Dialect::Js,
        source_type: SourceType::Script,
      },
    )
    .expect("parse");
    let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(0));
    assert!(diagnostics.is_empty());

    let (&block_sym, &var_sym) = sem
      .annex_b_function_decls
      .iter()
      .next()
      .expect("expected annex b linkage");

    let usage = collect_usages(&mut ast, &sem, TopLevelMode::Global);
    let renames = assign_names(&sem, &usage);

    let block_name = renames.get(&block_sym).expect("block rename");
    let var_name = renames.get(&var_sym).expect("var rename");
    assert_eq!(block_name, var_name);
  }

  #[test]
  fn annex_b_block_function_in_global_script_is_not_renamed() {
    let source = "if(true){function a(){}let x=1;x;a}";
    let mut ast = parse_with_options(
      source,
      ParseOptions {
        dialect: Dialect::Js,
        source_type: SourceType::Script,
      },
    )
    .expect("parse");
    let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Global, FileId(0));
    assert!(diagnostics.is_empty());

    let (&block_sym, &var_sym) = sem
      .annex_b_function_decls
      .iter()
      .next()
      .expect("expected annex b linkage");

    let x_name = sem.name_id("x").expect("x name id");
    let x_sym = sem
      .scopes
      .iter()
      .find_map(|(_, scope)| scope.symbols.get(&x_name).copied())
      .expect("x symbol");

    let usage = collect_usages(&mut ast, &sem, TopLevelMode::Global);
    let renames = assign_names(&sem, &usage);

    // The hoisted `var` binding is global and not renameable in `global` mode,
    // so the block binding must retain its original identifier.
    assert!(!renames.contains_key(&block_sym));
    assert!(!renames.contains_key(&var_sym));

    let x_name = renames.get(&x_sym).expect("x rename");
    assert_eq!(x_name, "b");
  }

  #[test]
  fn rewrite_source_expands_string_literal_replacement_ranges() {
    let source = r#""a-b""#;
    let mut replacements = vec![Replacement {
      start: 0,
      end: 3,
      text: "x".to_string(),
    }];
    let rewritten = rewrite_source(source, &mut replacements);
    assert_eq!(rewritten, "x");
  }
}
