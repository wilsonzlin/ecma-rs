use super::side_effects::{is_side_effect_free_class_decl, is_side_effect_free_expr};
use super::traverse::apply_to_function_like_bodies;
use super::{OptCtx, Pass};
use crate::rename::ExportNameSymbol;
use ahash::HashSet;
use derive_visitor::{Drive, Visitor};
use parse_js::ast::expr::lit::LitNumExpr;
use parse_js::ast::expr::pat::{IdPat, Pat};
use parse_js::ast::expr::IdExpr;
use parse_js::ast::expr::{BinaryExpr, Expr, UnaryExpr};
use parse_js::ast::import_export::ExportName;
use parse_js::ast::import_export::ImportNames;
use parse_js::ast::node::{Node, NodeAssocData};
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::ExprStmt;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stmt::{BlockStmt, ExportListStmt, ForBody, SwitchBranch, TryStmt};
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;
use semantic_js::assoc::js::{declared_symbol, resolved_symbol};
use semantic_js::js::{ScopeKind, SymbolId};

pub(super) struct DcePass;

impl Pass for DcePass {
  fn name(&self) -> &'static str {
    "dce"
  }

  fn run(&mut self, cx: &mut OptCtx, top: &mut Node<TopLevel>) -> bool {
    // Removing unused declarations can enable additional DCE by erasing initializer
    // expressions that were the only remaining "uses" of other symbols (e.g.
    // `let a=1,b=()=>a,c=()=>b;` when `c` is unused).
    //
    // Iterate a few rounds to reach a local fixpoint without requiring extra
    // full post-bind pipeline iterations/rebinding.
    let mut any_changed = false;
    for _ in 0..8 {
      let mut used = collect_used_symbols(top);
      // Exported symbols are always considered used.
      used.extend(cx.usage().exported.iter().copied());
      propagate_annex_b_liveness(cx, &mut used);

      let changed =
        apply_to_function_like_bodies(top, |stmts, changed| dce_stmts(stmts, cx, &used, changed));
      any_changed |= changed;
      if !changed {
        break;
      }
    }
    any_changed
  }
}

fn new_node<T>(loc: Loc, assoc: NodeAssocData, stx: T) -> Node<T>
where
  T: derive_visitor::Drive + derive_visitor::DriveMut,
{
  Node {
    loc,
    assoc,
    stx: Box::new(stx),
  }
}

fn propagate_annex_b_liveness(cx: &OptCtx, used: &mut HashSet<SymbolId>) {
  let sem = cx.sem();
  if sem.annex_b_function_decls.is_empty() {
    return;
  }

  // Annex B block function declarations introduce two linked bindings: a block
  // binding and a hoisted `var` binding. Treat the pair as a single liveness
  // group so DCE doesn't drop the declaration when only one side is referenced.
  for (block_sym, var_sym) in sem.annex_b_function_decls.iter() {
    if used.contains(block_sym) {
      used.insert(*var_sym);
    }
  }
  for (block_sym, var_sym) in sem.annex_b_function_decls.iter() {
    if used.contains(var_sym) {
      used.insert(*block_sym);
    }
  }
}

fn collect_used_symbols(top: &Node<TopLevel>) -> HashSet<SymbolId> {
  type IdExprNode = Node<IdExpr>;
  type IdPatNode = Node<IdPat>;
  type ExportNameNode = Node<ExportName>;
  type ExportListStmtNode = Node<ExportListStmt>;

  #[derive(Default, Visitor)]
  #[visitor(
    ExportListStmtNode(enter, exit),
    ExportNameNode(enter),
    IdExprNode(enter),
    IdPatNode(enter)
  )]
  struct UseCollector {
    used: HashSet<SymbolId>,
    in_export_list: usize,
  }

  impl UseCollector {
    fn enter_export_list_stmt_node(&mut self, _node: &ExportListStmtNode) {
      self.in_export_list += 1;
    }

    fn exit_export_list_stmt_node(&mut self, _node: &ExportListStmtNode) {
      if self.in_export_list > 0 {
        self.in_export_list -= 1;
      }
    }

    fn enter_export_name_node(&mut self, node: &ExportNameNode) {
      if let Some(sym) = node.assoc.get::<ExportNameSymbol>().map(|s| s.0) {
        self.used.insert(sym);
      }
    }

    fn enter_id_expr_node(&mut self, node: &IdExprNode) {
      if let Some(sym) = resolved_symbol(&node.assoc) {
        self.used.insert(sym);
      }
    }

    fn enter_id_pat_node(&mut self, node: &IdPatNode) {
      if self.in_export_list > 0 {
        return;
      }
      if declared_symbol(&node.assoc).is_some() {
        return;
      }
      if let Some(sym) = resolved_symbol(&node.assoc) {
        self.used.insert(sym);
      }
    }
  }

  let mut collector = UseCollector::default();
  top.drive(&mut collector);
  collector.used
}

fn dce_stmts(
  stmts: Vec<Node<Stmt>>,
  cx: &OptCtx,
  used: &HashSet<SymbolId>,
  changed: &mut bool,
) -> Vec<Node<Stmt>> {
  let mut out = Vec::with_capacity(stmts.len());
  for stmt in stmts {
    out.extend(dce_stmt_in_list(stmt, cx, used, changed));
  }
  out
}

fn dce_stmt_in_list(
  stmt: Node<Stmt>,
  cx: &OptCtx,
  used: &HashSet<SymbolId>,
  changed: &mut bool,
) -> Vec<Node<Stmt>> {
  let Node { loc, assoc, stx } = stmt;
  match *stx {
    Stmt::Import(mut import_stmt) => {
      // Pruning unused import bindings assumes the module graph is valid.
      //
      // Dropping an unused specifier can change module-linking errors (e.g. a
      // missing export that previously caused a link-time failure). We assume
      // users only care about preserving runtime semantics for valid programs.
      if let Some(default) = import_stmt.stx.default.take() {
        let remove_default = match default.stx.pat.stx.as_ref() {
          Pat::Id(id) => should_prune_import_binding(id, cx, used),
          _ => false,
        };
        if remove_default {
          *changed = true;
        } else {
          import_stmt.stx.default = Some(default);
        }
      }

      if let Some(names) = import_stmt.stx.names.take() {
        match names {
          ImportNames::All(alias) => {
            let remove_ns = match alias.stx.pat.stx.as_ref() {
              Pat::Id(id) => should_prune_import_binding(id, cx, used),
              _ => false,
            };
            if remove_ns {
              *changed = true;
            } else {
              import_stmt.stx.names = Some(ImportNames::All(alias));
            }
          }
          ImportNames::Specific(entries) => {
            let mut kept = Vec::with_capacity(entries.len());
            for entry in entries {
              let remove_entry = match entry.stx.alias.stx.pat.stx.as_ref() {
                Pat::Id(id) => should_prune_import_binding(id, cx, used),
                _ => false,
              };
              if remove_entry {
                *changed = true;
              } else {
                kept.push(entry);
              }
            }
            if !kept.is_empty() {
              import_stmt.stx.names = Some(ImportNames::Specific(kept));
            } else {
              // Keep the statement as a side-effect import.
              import_stmt.stx.names = None;
            }
          }
        }
      }

      // If both `default` and `names` are now `None`, this is a side-effect-only
      // import (`import "mod";`). Keep it so module evaluation still happens.
      vec![new_node(loc, assoc, Stmt::Import(import_stmt))]
    }
    Stmt::Block(mut block) => {
      let body = std::mem::take(&mut block.stx.body);
      block.stx.body = dce_stmts(body, cx, used, changed);
      vec![new_node(loc, assoc, Stmt::Block(block))]
    }
    Stmt::If(mut if_stmt) => {
      if_stmt.stx.consequent = dce_single_stmt(if_stmt.stx.consequent, cx, used, changed);
      if let Some(alt) = if_stmt.stx.alternate.take() {
        if_stmt.stx.alternate = Some(dce_single_stmt(alt, cx, used, changed));
      }
      vec![new_node(loc, assoc, Stmt::If(if_stmt))]
    }
    Stmt::While(mut while_stmt) => {
      while_stmt.stx.body = dce_single_stmt(while_stmt.stx.body, cx, used, changed);
      vec![new_node(loc, assoc, Stmt::While(while_stmt))]
    }
    Stmt::DoWhile(mut do_stmt) => {
      do_stmt.stx.body = dce_single_stmt(do_stmt.stx.body, cx, used, changed);
      vec![new_node(loc, assoc, Stmt::DoWhile(do_stmt))]
    }
    Stmt::ForTriple(mut for_stmt) => {
      for_stmt.stx.body = dce_for_body(for_stmt.stx.body, cx, used, changed);
      vec![new_node(loc, assoc, Stmt::ForTriple(for_stmt))]
    }
    Stmt::ForIn(mut for_stmt) => {
      for_stmt.stx.body = dce_for_body(for_stmt.stx.body, cx, used, changed);
      vec![new_node(loc, assoc, Stmt::ForIn(for_stmt))]
    }
    Stmt::ForOf(mut for_stmt) => {
      for_stmt.stx.body = dce_for_body(for_stmt.stx.body, cx, used, changed);
      vec![new_node(loc, assoc, Stmt::ForOf(for_stmt))]
    }
    Stmt::Switch(mut switch_stmt) => {
      let branches = std::mem::take(&mut switch_stmt.stx.branches);
      switch_stmt.stx.branches = branches
        .into_iter()
        .map(|branch| dce_switch_branch(branch, cx, used, changed))
        .collect();
      vec![new_node(loc, assoc, Stmt::Switch(switch_stmt))]
    }
    Stmt::Try(mut try_stmt) => {
      dce_try_stmt(&mut try_stmt, cx, used, changed);
      vec![new_node(loc, assoc, Stmt::Try(try_stmt))]
    }
    Stmt::With(mut with_stmt) => {
      with_stmt.stx.body = dce_single_stmt(with_stmt.stx.body, cx, used, changed);
      vec![new_node(loc, assoc, Stmt::With(with_stmt))]
    }
    Stmt::Label(mut label_stmt) => {
      label_stmt.stx.statement = dce_single_stmt(label_stmt.stx.statement, cx, used, changed);
      vec![new_node(loc, assoc, Stmt::Label(label_stmt))]
    }
    Stmt::FunctionDecl(decl) => dce_func_decl_stmt(loc, assoc, decl, cx, used, changed),
    Stmt::ClassDecl(decl) => dce_class_decl_stmt(loc, assoc, decl, cx, used, changed),
    Stmt::VarDecl(mut decl) => {
      if decl.stx.export || matches!(decl.stx.mode, VarDeclMode::Using | VarDeclMode::AwaitUsing) {
        return vec![new_node(loc, assoc, Stmt::VarDecl(decl))];
      }
      let mode = decl.stx.mode;
      let mut kept = Vec::with_capacity(decl.stx.declarators.len());
      let mut pending_effects = Vec::new();
      for declarator in decl.stx.declarators.into_iter() {
        if can_remove_declarator(&declarator.pattern.stx.pat, cx, used) {
          match declarator.initializer {
            None => {
              *changed = true;
            }
            Some(init) => {
              if is_side_effect_free_expr(&init) {
                *changed = true;
              } else {
                pending_effects.push(init);
                *changed = true;
              }
            }
          }
          continue;
        }

        let mut declarator = declarator;

        if !pending_effects.is_empty() {
          let apply_before_this = match mode {
            VarDeclMode::Var => declarator.initializer.is_some(),
            VarDeclMode::Let | VarDeclMode::Const => true,
            VarDeclMode::Using | VarDeclMode::AwaitUsing => unreachable!(),
          };
          if apply_before_this {
            let last = declarator.initializer.take().unwrap_or_else(undefined_expr);
            declarator.initializer = Some(comma_sequence(pending_effects, last));
            pending_effects = Vec::new();
          }
        }

        kept.push(declarator);
      }

      let trailing_effects = pending_effects;

      let mut out = Vec::new();
      if !kept.is_empty() {
        decl.stx.declarators = kept;
        out.push(new_node(loc, assoc, Stmt::VarDecl(decl)));
      }

      out.extend(trailing_effects.into_iter().map(expr_stmt));
      out
    }
    other => vec![new_node(loc, assoc, other)],
  }
}

fn dce_func_decl_stmt(
  loc: Loc,
  assoc: NodeAssocData,
  decl: Node<parse_js::ast::stmt::decl::FuncDecl>,
  cx: &OptCtx,
  used: &HashSet<SymbolId>,
  changed: &mut bool,
) -> Vec<Node<Stmt>> {
  if decl.stx.export {
    return vec![new_node(loc, assoc, Stmt::FunctionDecl(decl))];
  }
  let Some(name) = decl.stx.name.as_ref() else {
    // `export default function() {}` has no declared symbol; keep it.
    return vec![new_node(loc, assoc, Stmt::FunctionDecl(decl))];
  };
  let Some(sym) = declared_symbol(&name.assoc) else {
    // In `TopLevelMode::Global`, globals are intentionally not surfaced as
    // symbols, so treat missing symbols as pinned.
    return vec![new_node(loc, assoc, Stmt::FunctionDecl(decl))];
  };

  let sem = cx.sem();
  let mut effective_syms = vec![sym];
  if let Some(var_sym) = sem.annex_b_function_decls.get(&sym).copied() {
    // In `TopLevelMode::Global`, the hoisted `var` binding can be synthetic and
    // not referenced by resolution. Never remove such declarations since global
    // uses are not tracked.
    let var_scope = sem.symbol(var_sym).decl_scope;
    if sem.scope(var_scope).kind == ScopeKind::Global {
      return vec![new_node(loc, assoc, Stmt::FunctionDecl(decl))];
    }
    effective_syms.push(var_sym);
  }

  if effective_syms.iter().any(|sym| used.contains(sym)) {
    return vec![new_node(loc, assoc, Stmt::FunctionDecl(decl))];
  }
  if effective_syms
    .iter()
    .any(|sym| cx.disabled_scopes.contains(&sem.symbol(*sym).decl_scope))
  {
    return vec![new_node(loc, assoc, Stmt::FunctionDecl(decl))];
  }

  *changed = true;
  Vec::new()
}

fn dce_class_decl_stmt(
  loc: Loc,
  assoc: NodeAssocData,
  decl: Node<parse_js::ast::stmt::decl::ClassDecl>,
  cx: &OptCtx,
  used: &HashSet<SymbolId>,
  changed: &mut bool,
) -> Vec<Node<Stmt>> {
  if decl.stx.export || decl.stx.export_default {
    return vec![new_node(loc, assoc, Stmt::ClassDecl(decl))];
  }
  let Some(name) = decl.stx.name.as_ref() else {
    return vec![new_node(loc, assoc, Stmt::ClassDecl(decl))];
  };
  let Some(sym) = declared_symbol(&name.assoc) else {
    return vec![new_node(loc, assoc, Stmt::ClassDecl(decl))];
  };
  let sem = cx.sem();
  if used.contains(&sym) {
    return vec![new_node(loc, assoc, Stmt::ClassDecl(decl))];
  }
  if cx.disabled_scopes.contains(&sem.symbol(sym).decl_scope) {
    return vec![new_node(loc, assoc, Stmt::ClassDecl(decl))];
  }
  if !is_side_effect_free_class_decl(&decl) {
    return vec![new_node(loc, assoc, Stmt::ClassDecl(decl))];
  }

  *changed = true;
  Vec::new()
}

fn dce_single_stmt(
  stmt: Node<Stmt>,
  cx: &OptCtx,
  used: &HashSet<SymbolId>,
  changed: &mut bool,
) -> Node<Stmt> {
  let mut stmts = dce_stmt_in_list(stmt, cx, used, changed);
  match stmts.len() {
    0 => empty_stmt(),
    1 => stmts.pop().unwrap(),
    _ => wrap_in_block(stmts),
  }
}

fn can_remove_declarator(pat: &Node<Pat>, cx: &OptCtx, used: &HashSet<SymbolId>) -> bool {
  let Pat::Id(id) = pat.stx.as_ref() else {
    return false;
  };
  let Some(sym) = declared_symbol(&id.assoc) else {
    return false;
  };
  if used.contains(&sym) {
    return false;
  }
  if cx
    .disabled_scopes
    .contains(&cx.sem().symbol(sym).decl_scope)
  {
    return false;
  }
  true
}

fn comma_sequence(effects: Vec<Node<Expr>>, tail: Node<Expr>) -> Node<Expr> {
  let mut it = effects.into_iter();
  let Some(first) = it.next() else {
    return tail;
  };
  let mut expr = first;
  for next in it {
    expr = Node::new(
      Loc(0, 0),
      BinaryExpr {
        operator: OperatorName::Comma,
        left: expr,
        right: next,
      },
    )
    .into_wrapped();
  }
  Node::new(
    Loc(0, 0),
    BinaryExpr {
      operator: OperatorName::Comma,
      left: expr,
      right: tail,
    },
  )
  .into_wrapped()
}

fn undefined_expr() -> Node<Expr> {
  Node::new(
    Loc(0, 0),
    UnaryExpr {
      operator: OperatorName::Void,
      argument: Node::new(
        Loc(0, 0),
        LitNumExpr {
          value: JsNumber(0.0),
        },
      )
      .into_wrapped(),
    },
  )
  .into_wrapped()
}

fn expr_stmt(expr: Node<Expr>) -> Node<Stmt> {
  Node::new(
    Loc(0, 0),
    Stmt::Expr(Node::new(Loc(0, 0), ExprStmt { expr })),
  )
}

fn wrap_in_block(body: Vec<Node<Stmt>>) -> Node<Stmt> {
  Node::new(
    Loc(0, 0),
    Stmt::Block(Node::new(Loc(0, 0), BlockStmt { body })),
  )
}

fn empty_stmt() -> Node<Stmt> {
  Node::new(
    Loc(0, 0),
    Stmt::Empty(Node::new(Loc(0, 0), parse_js::ast::stmt::EmptyStmt {})),
  )
}

fn should_prune_import_binding(id: &Node<IdPat>, cx: &OptCtx, used: &HashSet<SymbolId>) -> bool {
  let Some(sym) = declared_symbol(&id.assoc) else {
    return false;
  };
  if used.contains(&sym) {
    return false;
  }
  if cx
    .disabled_scopes
    .contains(&cx.sem().symbol(sym).decl_scope)
  {
    return false;
  }
  true
}

fn dce_for_body(
  mut body: Node<ForBody>,
  cx: &OptCtx,
  used: &HashSet<SymbolId>,
  changed: &mut bool,
) -> Node<ForBody> {
  let stmts = std::mem::take(&mut body.stx.body);
  body.stx.body = dce_stmts(stmts, cx, used, changed);
  body
}

fn dce_switch_branch(
  mut branch: Node<SwitchBranch>,
  cx: &OptCtx,
  used: &HashSet<SymbolId>,
  changed: &mut bool,
) -> Node<SwitchBranch> {
  let stmts = std::mem::take(&mut branch.stx.body);
  branch.stx.body = dce_stmts(stmts, cx, used, changed);
  branch
}

fn dce_try_stmt(
  try_stmt: &mut Node<TryStmt>,
  cx: &OptCtx,
  used: &HashSet<SymbolId>,
  changed: &mut bool,
) {
  let wrapped = std::mem::take(&mut try_stmt.stx.wrapped.stx.body);
  try_stmt.stx.wrapped.stx.body = dce_stmts(wrapped, cx, used, changed);

  if let Some(catch) = try_stmt.stx.catch.as_mut() {
    let body = std::mem::take(&mut catch.stx.body);
    catch.stx.body = dce_stmts(body, cx, used, changed);
  }

  if let Some(finally) = try_stmt.stx.finally.as_mut() {
    let body = std::mem::take(&mut finally.stx.body);
    finally.stx.body = dce_stmts(body, cx, used, changed);
  }
}
