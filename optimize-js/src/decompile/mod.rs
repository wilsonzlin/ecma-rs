pub mod foreign;
pub mod il;
pub mod names;
pub mod regalloc;
pub mod structurer;
pub mod top_level;

mod options;

use crate::il::inst::{Arg, BinOp, Const};
use crate::{Program, ProgramFunction};
use parse_js::ast::expr::lit::{LitBoolExpr, LitNullExpr, LitNumExpr};
use parse_js::ast::expr::pat::{IdPat, Pat};
use parse_js::ast::expr::{BinaryExpr, Expr, IdExpr};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{PatDecl, VarDecl, VarDeclMode, VarDeclarator};
use parse_js::ast::stmt::{
  BlockStmt, BreakStmt, ContinueStmt, ExprStmt, IfStmt, LabelStmt, Stmt, WhileStmt,
};
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

pub use foreign::{collect_foreign_bindings, ForeignBinding, ForeignBindings};
pub use il::{
  lower_function, lower_program, LoweredArg, LoweredBlock, LoweredFunction, LoweredInst,
  LoweredProgram,
};
pub use names::{collect_reserved_from_cfg, collect_reserved_from_insts, NameMangler};
pub use options::{DecompileOptions, ResolvedTempDeclStyle, TempDeclScope, TempDeclStyle};
pub use structurer::{structure_cfg, BreakTarget, ControlTree, LoopLabel};
pub use top_level::{build_top_level, foreign_var_decl, prepend_foreign_decls};

use self::il::{
  lower_arg, lower_bin_expr, lower_call_inst, lower_prop_assign_inst, node, FnEmitter, VarInit,
  VarNamer,
};

#[derive(Debug)]
pub enum ProgramToJsError {
  Decompile(il::DecompileError),
  Emit(emit_js::EmitError),
}

impl From<il::DecompileError> for ProgramToJsError {
  fn from(value: il::DecompileError) -> Self {
    ProgramToJsError::Decompile(value)
  }
}

impl From<emit_js::EmitError> for ProgramToJsError {
  fn from(value: emit_js::EmitError) -> Self {
    ProgramToJsError::Emit(value)
  }
}

/// Converts an optimized [`Program`] into a `parse-js` [`TopLevel`] AST.
///
/// This sets up a deterministic, public API surface for downstream consumers. The actual
/// control-flow structurization is delegated to dedicated helpers; this function wires
/// together the pieces so callers have a stable entry point today.
pub fn program_to_ast(
  program: &Program,
  opts: &DecompileOptions,
) -> il::DecompileResult<Node<TopLevel>> {
  let lowered = lower_program(program);
  let control = structure_cfg(&program.top_level.body);
  let labeled_loops = collect_labeled_loops(&control);

  let mut decompiler = FunctionDecompiler::new(
    &program.top_level,
    &lowered.foreign_bindings,
    opts,
    TempDeclScope::TopLevel(program.top_level_mode),
    labeled_loops,
  );

  let temps: Vec<u32> = collect_temps(&program.top_level);
  let mut body = Vec::new();
  if let Some(decl) = decompiler.prepare_temp_decls(&temps) {
    body.push(decl);
  }
  body.extend(decompiler.lower_tree(&control)?);

  let top = if opts.emit_foreign_bindings {
    build_top_level(body, &lowered.foreign_bindings)
  } else {
    Node::new(Loc(0, 0), TopLevel { body })
  };

  Ok(top)
}

/// Converts the optimized [`Program`] into emitted JS bytes using `emit-js`.
pub fn program_to_js(
  program: &Program,
  decompile: &DecompileOptions,
  emit: emit_js::EmitOptions,
) -> Result<Vec<u8>, ProgramToJsError> {
  let ast = program_to_ast(program, decompile)?;
  let mut emitter = emit_js::Emitter::new(emit);
  emit_js::emit_top_level_stmt(&mut emitter, ast.stx.as_ref()).map_err(ProgramToJsError::Emit)?;
  Ok(emitter.into_bytes())
}

fn collect_temps(func: &ProgramFunction) -> Vec<u32> {
  let mut temps = Vec::new();
  for (_, insts) in func.body.bblocks.all() {
    for inst in insts {
      temps.extend(inst.tgts.iter().copied());
      for arg in &inst.args {
        if let Arg::Var(var) = arg {
          temps.push(*var);
        }
      }
    }
  }
  temps.sort_unstable();
  temps.dedup();
  temps
}

fn format_temp_decls(temps: &[u32], style: ResolvedTempDeclStyle) -> Option<String> {
  if temps.is_empty() {
    return None;
  }

  let mut out = String::new();
  match style {
    ResolvedTempDeclStyle::Var => out.push_str("var "),
    ResolvedTempDeclStyle::LetWithVoidInit => out.push_str("let "),
  }

  for (idx, temp) in temps.iter().enumerate() {
    if idx > 0 {
      out.push_str(", ");
    }
    out.push('r');
    out.push_str(&temp.to_string());
    if matches!(style, ResolvedTempDeclStyle::LetWithVoidInit) {
      out.push_str("=void 0");
    }
  }
  out.push(';');
  Some(out)
}

/// Emits a declaration statement for the temporaries used inside `func`.
///
/// The declaration style is resolved using the provided `scope`; callers should
/// pass [`TempDeclScope::TopLevel`] for program-level code so `Auto` can take
/// [`crate::TopLevelMode`] into account.
pub fn temp_decls_for_function(
  func: &ProgramFunction,
  scope: TempDeclScope,
  options: &DecompileOptions,
) -> Option<String> {
  let temps = collect_temps(func);
  let style = options.resolve_temp_decl_style(scope);
  format_temp_decls(&temps, style)
}

/// Convenience wrapper for the program top-level that uses [`Program::top_level_mode`]
/// when resolving the declaration style.
pub fn temp_decls_for_top_level(program: &Program, options: &DecompileOptions) -> Option<String> {
  temp_decls_for_function(
    &program.top_level,
    TempDeclScope::TopLevel(program.top_level_mode),
    options,
  )
}

/// Emits a `var`-style declaration for nested functions unless overridden by
/// options.
pub fn temp_decls_for_nested_function(
  func: &ProgramFunction,
  options: &DecompileOptions,
) -> Option<String> {
  temp_decls_for_function(func, TempDeclScope::Function, options)
}

fn bool_expr(value: bool) -> Node<Expr> {
  node(Expr::LitBool(node(LitBoolExpr { value })))
}

fn void_0_expr() -> Node<Expr> {
  identifier("undefined".to_string())
}

fn num_expr(value: u32) -> Node<Expr> {
  node(Expr::LitNum(node(LitNumExpr {
    value: JsNumber(value as f64),
  })))
}

fn block_stmt(stmts: Vec<Node<Stmt>>) -> Node<Stmt> {
  node(Stmt::Block(node(BlockStmt { body: stmts })))
}

fn break_stmt(label: Option<String>) -> Node<Stmt> {
  node(Stmt::Break(node(BreakStmt { label })))
}

fn continue_stmt(label: Option<String>) -> Node<Stmt> {
  node(Stmt::Continue(node(ContinueStmt { label })))
}

fn label_stmt(name: String, stmt: Node<Stmt>) -> Node<Stmt> {
  node(Stmt::Label(node(LabelStmt {
    name,
    statement: stmt,
  })))
}

fn identifier(name: String) -> Node<Expr> {
  node(Expr::Id(node(IdExpr { name })))
}

struct FunctionDecompiler<'a> {
  options: &'a DecompileOptions,
  bindings: &'a ForeignBindings,
  mangler: RefCell<NameMangler>,
  declared: HashSet<u32>,
  resolved_style: ResolvedTempDeclStyle,
  decl_mode: VarDeclMode,
  predeclared: bool,
  loop_labels: HashMap<LoopLabel, String>,
}

impl<'a> FunctionDecompiler<'a> {
  fn new(
    func: &ProgramFunction,
    bindings: &'a ForeignBindings,
    options: &'a DecompileOptions,
    scope: TempDeclScope,
    labeled_loops: HashSet<LoopLabel>,
  ) -> Self {
    let mut reserved = collect_reserved_from_cfg(&func.body);
    reserved.extend(bindings.iter().map(|binding| binding.ident.clone()));
    let mut mangler = NameMangler::new(reserved);

    let mut loop_labels = HashMap::new();
    let mut labeled_loops: Vec<_> = labeled_loops.into_iter().collect();
    labeled_loops.sort_unstable();
    for label in labeled_loops {
      let name = mangler.fresh("loop");
      loop_labels.insert(label, name);
    }

    let resolved_style = options.resolve_temp_decl_style(scope);
    let decl_mode = match resolved_style {
      ResolvedTempDeclStyle::Var => VarDeclMode::Var,
      ResolvedTempDeclStyle::LetWithVoidInit => VarDeclMode::Let,
    };

    Self {
      options,
      bindings,
      mangler: RefCell::new(mangler),
      declared: HashSet::new(),
      resolved_style,
      decl_mode,
      predeclared: false,
      loop_labels,
    }
  }

  fn temp_decl_stmt(&self, temps: &[u32]) -> Option<Node<Stmt>> {
    if temps.is_empty() {
      return None;
    }

    let declarators = temps
      .iter()
      .map(|temp| VarDeclarator {
        pattern: node(PatDecl {
          pat: node(Pat::Id(node(IdPat {
            name: self.name_var(*temp),
          }))),
        }),
        definite_assignment: false,
        type_annotation: None,
        initializer: match self.resolved_style {
          ResolvedTempDeclStyle::Var => None,
          ResolvedTempDeclStyle::LetWithVoidInit => Some(void_0_expr()),
        },
      })
      .collect();

    Some(node(Stmt::VarDecl(node(VarDecl {
      export: false,
      mode: self.decl_mode,
      declarators,
    }))))
  }

  fn prepare_temp_decls(&mut self, temps: &[u32]) -> Option<Node<Stmt>> {
    if !self.options.declare_registers {
      return None;
    }
    for temp in temps {
      self.declared.insert(*temp);
      self.name_var(*temp);
    }
    self.predeclared = true;
    self.temp_decl_stmt(temps)
  }

  fn ensure_supported_arg(&self, arg: &Arg) -> il::DecompileResult<()> {
    if let Arg::Fn(id) = arg {
      return Err(il::DecompileError::Unsupported(format!(
        "function literals not supported (fn{id})"
      )));
    }
    Ok(())
  }

  fn ensure_supported_args<'b>(
    &self,
    args: impl IntoIterator<Item = &'b Arg>,
  ) -> il::DecompileResult<()> {
    for arg in args {
      self.ensure_supported_arg(arg)?;
    }
    Ok(())
  }

  fn target_init_for(&mut self, tgt: u32) -> VarInit {
    if self.predeclared || self.declared.contains(&tgt) {
      VarInit::Assign
    } else {
      self.declared.insert(tgt);
      VarInit::Declare(self.decl_mode)
    }
  }

  fn binding_stmt(&self, tgt: u32, value: Node<Expr>, init: VarInit) -> Node<Stmt> {
    let name = self.name_var(tgt);
    match init {
      VarInit::Assign => node(Stmt::Expr(node(ExprStmt {
        expr: node(Expr::Binary(node(BinaryExpr {
          operator: OperatorName::Assignment,
          left: identifier(name),
          right: value,
        }))),
      }))),
      VarInit::Declare(mode) => node(Stmt::VarDecl(node(VarDecl {
        export: false,
        mode,
        declarators: vec![VarDeclarator {
          pattern: node(PatDecl {
            pat: node(Pat::Id(node(IdPat { name }))),
          }),
          definite_assignment: false,
          type_annotation: None,
          initializer: Some(value),
        }],
      }))),
    }
  }

  fn assign_named(&self, name: &str, value: Node<Expr>) -> Node<Stmt> {
    node(Stmt::Expr(node(ExprStmt {
      expr: node(Expr::Binary(node(BinaryExpr {
        operator: OperatorName::Assignment,
        left: identifier(name.to_string()),
        right: value,
      }))),
    })))
  }

  fn lower_nullish_equality(
    &self,
    op: BinOp,
    left: &Arg,
    right: &Arg,
  ) -> il::DecompileResult<Node<Expr>> {
    let target = if matches!(right, Arg::Const(Const::Null)) {
      left
    } else if matches!(left, Arg::Const(Const::Null)) {
      right
    } else {
      return Ok(lower_bin_expr(self, self, op, left, right));
    };

    let is_equal = matches!(op, BinOp::LooseEq);
    let comparison = if is_equal {
      OperatorName::StrictEquality
    } else {
      OperatorName::StrictInequality
    };
    let null_check = node(Expr::Binary(node(BinaryExpr {
      operator: comparison,
      left: self.lower_arg(target)?,
      right: node(Expr::LitNull(node(LitNullExpr {}))),
    })));
    let undefined_check = node(Expr::Binary(node(BinaryExpr {
      operator: comparison,
      left: self.lower_arg(target)?,
      right: void_0_expr(),
    })));
    let logical = if is_equal {
      OperatorName::LogicalOr
    } else {
      OperatorName::LogicalAnd
    };
    Ok(node(Expr::Binary(node(BinaryExpr {
      operator: logical,
      left: null_check,
      right: undefined_check,
    }))))
  }

  fn lower_state_machine(
    &mut self,
    entry: u32,
    blocks: &[structurer::StateBlock],
  ) -> il::DecompileResult<Vec<Node<Stmt>>> {
    let state_name = self.mangler.borrow_mut().fresh("state");

    let state_decl = node(Stmt::VarDecl(node(VarDecl {
      export: false,
      mode: self.decl_mode,
      declarators: vec![VarDeclarator {
        pattern: node(PatDecl {
          pat: node(Pat::Id(node(IdPat {
            name: state_name.clone(),
          }))),
        }),
        definite_assignment: false,
        type_annotation: None,
        initializer: Some(num_expr(entry)),
      }],
    })));

    let mut sorted_blocks = blocks.to_vec();
    sorted_blocks.sort_by_key(|b| b.label);

    let mut branches = Vec::with_capacity(sorted_blocks.len());
    for block in sorted_blocks {
      let mut body = self.lower_insts(&block.insts)?;
      match block.term {
        structurer::Terminator::Goto(label) => {
          body.push(self.assign_named(&state_name, num_expr(label)));
        }
        structurer::Terminator::CondGoto { cond, t, f } => {
          let cond_expr = self.lower_arg(&cond)?;
          let then_body = vec![self.assign_named(&state_name, num_expr(t))];
          let else_body = vec![self.assign_named(&state_name, num_expr(f))];
          body.push(node(Stmt::If(node(IfStmt {
            test: cond_expr,
            consequent: block_stmt(then_body),
            alternate: Some(block_stmt(else_body)),
          }))));
        }
        structurer::Terminator::Stop => {
          body.push(break_stmt(None));
        }
      }
      let test = node(Expr::Binary(node(BinaryExpr {
        operator: OperatorName::StrictEquality,
        left: identifier(state_name.clone()),
        right: num_expr(block.label),
      })));
      branches.push((test, body));
    }

    let mut chain: Option<Node<Stmt>> = Some(block_stmt(vec![break_stmt(None)]));
    for (test, body) in branches.into_iter().rev() {
      let cons = block_stmt(body);
      let stmt = node(Stmt::If(node(IfStmt {
        test,
        consequent: cons,
        alternate: chain,
      })));
      chain = Some(stmt);
    }

    let while_stmt = node(Stmt::While(node(WhileStmt {
      condition: bool_expr(true),
      body: chain.expect("state machine should have at least one branch"),
    })));

    Ok(vec![state_decl, while_stmt])
  }

  fn lower_inst(
    &mut self,
    inst: &crate::il::inst::Inst,
  ) -> il::DecompileResult<Option<Node<Stmt>>> {
    use crate::il::inst::InstTyp;

    match inst.t {
      InstTyp::Bin => {
        self.ensure_supported_args(inst.args.iter())?;
        let (tgt, left, op, right) = inst.as_bin();
        let expr = match op {
          BinOp::LooseEq | BinOp::NotLooseEq => self.lower_nullish_equality(op, left, right)?,
          _ => lower_bin_expr(self, self, op, left, right),
        };
        let init = self.target_init_for(tgt);
        Ok(Some(self.binding_stmt(tgt, expr, init)))
      }
      InstTyp::Un | InstTyp::ForeignLoad | InstTyp::UnknownLoad => {
        self.ensure_supported_args(inst.args.iter())?;
        let Some(value) = il::lower_value_inst(self, self, inst) else {
          return Ok(None);
        };
        let Some(&tgt) = inst.tgts.get(0) else {
          return Ok(None);
        };
        let init = self.target_init_for(tgt);
        Ok(Some(self.binding_stmt(tgt, value, init)))
      }
      InstTyp::VarAssign => {
        self.ensure_supported_args(inst.args.iter())?;
        let (tgt, arg) = inst.as_var_assign();
        let expr = self.lower_arg(arg)?;
        let init = self.target_init_for(tgt);
        Ok(Some(self.binding_stmt(tgt, expr, init)))
      }
      InstTyp::Call => {
        self.ensure_supported_args(inst.args.iter())?;
        let (tgt, _, _, _, _) = inst.as_call();
        let init = tgt
          .map(|t| self.target_init_for(t))
          .unwrap_or(VarInit::Assign);
        let stmt = lower_call_inst(self, self, inst, None, None, None, init)
          .expect("call inst should lower");
        Ok(Some(stmt))
      }
      InstTyp::PropAssign => {
        self.ensure_supported_args(inst.args.iter())?;
        Ok(lower_prop_assign_inst(self, self, inst))
      }
      InstTyp::ForeignStore => {
        self.ensure_supported_args(inst.args.iter())?;
        Ok(il::lower_foreign_store_inst(self, self, inst))
      }
      InstTyp::UnknownStore => {
        self.ensure_supported_args(inst.args.iter())?;
        Ok(il::lower_unknown_store_inst(self, self, inst))
      }
      InstTyp::Phi => Err(il::DecompileError::Unsupported(
        "phi instructions are not supported in decompiler output".into(),
      )),
      InstTyp::CondGoto | InstTyp::_Goto | InstTyp::_Label | InstTyp::_Dummy => Ok(None),
    }
  }

  fn lower_insts(
    &mut self,
    insts: &[crate::il::inst::Inst],
  ) -> il::DecompileResult<Vec<Node<Stmt>>> {
    let mut out = Vec::new();
    for inst in insts {
      if let Some(stmt) = self.lower_inst(inst)? {
        out.push(stmt);
      }
    }
    Ok(out)
  }

  fn lower_arg(&self, arg: &Arg) -> il::DecompileResult<Node<Expr>> {
    self.ensure_supported_arg(arg)?;
    if matches!(arg, Arg::Const(Const::Undefined)) {
      return Ok(void_0_expr());
    }
    Ok(lower_arg(self, self, arg))
  }

  fn lower_tree(&mut self, tree: &ControlTree) -> il::DecompileResult<Vec<Node<Stmt>>> {
    let mut loop_stack = Vec::new();
    self.lower_tree_with_stack(tree, &mut loop_stack)
  }

  fn lower_tree_with_stack(
    &mut self,
    tree: &ControlTree,
    loop_stack: &mut Vec<LoopLabel>,
  ) -> il::DecompileResult<Vec<Node<Stmt>>> {
    match tree {
      ControlTree::Seq(nodes) => {
        let mut out = Vec::new();
        for node in nodes {
          out.extend(self.lower_tree_with_stack(node, loop_stack)?);
        }
        Ok(out)
      }
      ControlTree::Block { insts, .. } => self.lower_insts(insts),
      ControlTree::If {
        insts,
        cond,
        then_t,
        else_t,
        ..
      } => {
        let mut out = self.lower_insts(insts)?;
        let test = self.lower_arg(cond)?;
        let consequent = block_stmt(self.lower_tree_with_stack(then_t, loop_stack)?);
        let alt_stmts = self.lower_tree_with_stack(else_t, loop_stack)?;
        let alternate = (!alt_stmts.is_empty()).then(|| block_stmt(alt_stmts));
        out.push(node(Stmt::If(node(IfStmt {
          test,
          consequent,
          alternate,
        }))));
        Ok(out)
      }
      ControlTree::Loop {
        body, loop_label, ..
      } => {
        loop_stack.push(*loop_label);
        let body = block_stmt(self.lower_tree_with_stack(body, loop_stack)?);
        loop_stack.pop();

        let stmt = node(Stmt::While(node(WhileStmt {
          condition: bool_expr(true),
          body,
        })));
        if let Some(label) = self.loop_labels.get(loop_label) {
          Ok(vec![label_stmt(label.clone(), stmt)])
        } else {
          Ok(vec![stmt])
        }
      }
      ControlTree::Break { target } => match target {
        BreakTarget::Loop(label) => Ok(vec![break_stmt(self.loop_labels.get(label).cloned())]),
        BreakTarget::Label(label) => Err(il::DecompileError::Unsupported(format!(
          "break to label {label} is not supported"
        ))),
      },
      ControlTree::Continue { target } => {
        Ok(vec![continue_stmt(self.loop_labels.get(target).cloned())])
      }
      ControlTree::StateMachine { entry, blocks } => self.lower_state_machine(*entry, blocks),
    }
  }
}

impl VarNamer for FunctionDecompiler<'_> {
  fn name_var(&self, var: u32) -> String {
    self.mangler.borrow_mut().name_for_reg(var)
  }

  fn name_foreign(&self, symbol: crate::symbol::semantics::SymbolId) -> String {
    self
      .bindings
      .name_for(symbol)
      .expect("foreign binding should exist")
      .to_string()
  }

  fn name_unknown(&self, name: &str) -> String {
    name.to_string()
  }
}

impl FnEmitter for FunctionDecompiler<'_> {
  fn emit_function(&self, id: usize) -> Node<Expr> {
    identifier(format!("fn{id}"))
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::cfg::cfg::{Cfg, CfgBBlocks, CfgGraph};

  fn empty_program_function() -> ProgramFunction {
    ProgramFunction {
      debug: None,
      body: Cfg {
        graph: CfgGraph::default(),
        bblocks: CfgBBlocks::default(),
        entry: 0,
      },
      stats: Default::default(),
    }
  }

  #[test]
  fn break_to_outer_loop_is_labeled() {
    let tree = ControlTree::Loop {
      header: 0,
      follow: None,
      loop_label: LoopLabel(0),
      body: Box::new(ControlTree::Seq(vec![
        ControlTree::Loop {
          header: 1,
          follow: None,
          loop_label: LoopLabel(1),
          body: Box::new(ControlTree::Seq(vec![ControlTree::Break {
            target: BreakTarget::Loop(LoopLabel(0)),
          }])),
        },
        ControlTree::Continue {
          target: LoopLabel(0),
        },
      ])),
    };

    let func = empty_program_function();
    let labeled = collect_labeled_loops(&tree);
    let bindings = ForeignBindings::default();
    let options = DecompileOptions::default();
    let mut decompiler = FunctionDecompiler::new(
      &func,
      &bindings,
      &options,
      TempDeclScope::Function,
      labeled,
    );
    let stmts = decompiler.lower_tree(&tree).expect("lower");

    assert_eq!(stmts.len(), 1);
    let label = match stmts[0].stx.as_ref() {
      Stmt::Label(label) => label,
      other => panic!("expected label stmt, got {other:?}"),
    };
    assert_eq!(label.stx.name, "loop");

    let while_stmt = match label.stx.statement.stx.as_ref() {
      Stmt::While(w) => w,
      other => panic!("expected labeled while loop, got {other:?}"),
    };
    let body = match while_stmt.stx.body.stx.as_ref() {
      Stmt::Block(block) => &block.stx.body,
      other => panic!("expected block body, got {other:?}"),
    };
    assert!(
      body.iter().any(|stmt| matches!(stmt.stx.as_ref(), Stmt::While(_))),
      "expected inner loop"
    );
    assert!(
      body
        .iter()
        .any(|stmt| matches!(stmt.stx.as_ref(), Stmt::Continue(cont) if cont.stx.label.as_deref() == Some("loop"))),
      "expected labeled continue to outer loop"
    );

    let inner_while = body
      .iter()
      .find_map(|stmt| match stmt.stx.as_ref() {
        Stmt::While(w) => Some(w),
        _ => None,
      })
      .expect("inner while loop");
    let inner_body = match inner_while.stx.body.stx.as_ref() {
      Stmt::Block(block) => &block.stx.body,
      other => panic!("expected block body, got {other:?}"),
    };
    assert!(
      inner_body.iter().any(|stmt| matches!(stmt.stx.as_ref(), Stmt::Break(brk) if brk.stx.label.as_deref() == Some("loop"))),
      "expected break to outer loop"
    );
  }
}

fn collect_labeled_loops(tree: &ControlTree) -> HashSet<LoopLabel> {
  fn walk(
    tree: &ControlTree,
    stack: &mut Vec<LoopLabel>,
    labeled: &mut HashSet<LoopLabel>,
  ) {
    match tree {
      ControlTree::Seq(nodes) => {
        for node in nodes {
          walk(node, stack, labeled);
        }
      }
      ControlTree::Block { .. } => {}
      ControlTree::If {
        then_t, else_t, ..
      } => {
        walk(then_t, stack, labeled);
        walk(else_t, stack, labeled);
      }
      ControlTree::Loop { loop_label, body, .. } => {
        stack.push(*loop_label);
        walk(body, stack, labeled);
        stack.pop();
      }
      ControlTree::Break { target } => {
        if let BreakTarget::Loop(label) = target {
          if stack.last().copied() != Some(*label) {
            labeled.insert(*label);
          }
        }
      }
      ControlTree::Continue { target } => {
        if stack.last().copied() != Some(*target) {
          labeled.insert(*target);
        }
      }
      ControlTree::StateMachine { .. } => {}
    }
  }

  let mut labeled = HashSet::new();
  walk(tree, &mut Vec::new(), &mut labeled);
  labeled
}
