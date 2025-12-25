use crate::il::inst::{Arg, BinOp, Const, Inst, InstTyp, UnOp};
use derive_visitor::{Drive, DriveMut};
use parse_js::ast::expr::lit::{LitBigIntExpr, LitBoolExpr, LitNullExpr, LitNumExpr, LitStrExpr};
use parse_js::ast::expr::pat::{IdPat, Pat};
use parse_js::ast::expr::{
  BinaryExpr, CallArg, CallExpr, ComputedMemberExpr, Expr, IdExpr, MemberExpr, UnaryExpr,
};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{PatDecl, VarDecl, VarDeclMode, VarDeclarator};
use parse_js::ast::stmt::{ExprStmt, Stmt};
use parse_js::char::{ID_CONTINUE, ID_START};
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;
use symbol_js::symbol::Symbol;

const DEFAULT_LOC: Loc = Loc(0, 0);

/// Helper to create a [`Node`] with a default zero location.
pub fn node<T>(stx: T) -> Node<T>
where
  T: Drive + DriveMut,
{
  Node::new(DEFAULT_LOC, stx)
}

pub trait VarNamer {
  fn name_var(&self, var: u32) -> String;
  fn name_foreign(&self, symbol: Symbol) -> String;
  fn name_unknown(&self, name: &str) -> String;
}

pub trait FnEmitter {
  fn emit_function(&self, id: usize) -> Node<Expr>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VarInit {
  Assign,
  Declare(VarDeclMode),
}

impl Default for VarInit {
  fn default() -> Self {
    VarInit::Assign
  }
}

fn identifier(name: String) -> Node<Expr> {
  node(Expr::Id(node(IdExpr { name })))
}

fn lower_const(c: &Const) -> Node<Expr> {
  match c {
    Const::Bool(value) => node(Expr::LitBool(node(LitBoolExpr { value: *value }))),
    Const::Num(value) => node(Expr::LitNum(node(LitNumExpr { value: *value }))),
    Const::Str(value) => node(Expr::LitStr(node(LitStrExpr {
      value: value.clone(),
    }))),
    Const::Null => node(Expr::LitNull(node(LitNullExpr {}))),
    Const::BigInt(value) => node(Expr::LitBigInt(node(LitBigIntExpr {
      value: format!("{value}n"),
    }))),
    Const::Undefined => node(Expr::Unary(node(UnaryExpr {
      operator: OperatorName::Void,
      argument: node(Expr::LitNum(node(LitNumExpr {
        value: JsNumber(0.0),
      }))),
    }))),
  }
}

fn lower_builtin(path: &str) -> Node<Expr> {
  let mut parts = path.split('.').peekable();
  let first = parts
    .next()
    .expect("builtin path should contain at least one segment");
  let mut expr = identifier(first.to_string());
  while let Some(next) = parts.next() {
    expr = node(Expr::Member(node(MemberExpr {
      optional_chaining: false,
      left: expr,
      right: next.to_string(),
    })));
  }
  expr
}

fn bin_operator(op: BinOp) -> OperatorName {
  match op {
    BinOp::Add => OperatorName::Addition,
    BinOp::Div => OperatorName::Division,
    BinOp::Exp => OperatorName::Exponentiation,
    BinOp::Geq => OperatorName::GreaterThanOrEqual,
    BinOp::Gt => OperatorName::GreaterThan,
    BinOp::Leq => OperatorName::LessThanOrEqual,
    BinOp::LooseEq => OperatorName::Equality,
    BinOp::Lt => OperatorName::LessThan,
    BinOp::Mod => OperatorName::Remainder,
    BinOp::Mul => OperatorName::Multiplication,
    BinOp::NotLooseEq => OperatorName::Inequality,
    BinOp::NotStrictEq => OperatorName::StrictInequality,
    BinOp::StrictEq => OperatorName::StrictEquality,
    BinOp::Sub => OperatorName::Subtraction,
    BinOp::GetProp => panic!("GetProp is handled separately"),
    BinOp::_Dummy => unreachable!("dummy bin op should not be lowered"),
  }
}

fn un_operator(op: UnOp) -> OperatorName {
  match op {
    UnOp::Neg => OperatorName::UnaryNegation,
    UnOp::Not => OperatorName::LogicalNot,
    UnOp::Plus => OperatorName::UnaryPlus,
    UnOp::Typeof => OperatorName::Typeof,
    UnOp::Void => OperatorName::Void,
    UnOp::_Dummy => unreachable!("dummy un op should not be lowered"),
  }
}

fn is_valid_identifier(name: &str) -> bool {
  let mut chars = name.chars();
  let Some(first) = chars.next() else {
    return false;
  };
  if !ID_START.has(first) {
    return false;
  }
  chars.all(|c| ID_CONTINUE.has(c))
}

pub fn lower_arg<V: VarNamer, F: FnEmitter>(
  var_namer: &V,
  fn_emitter: &F,
  arg: &Arg,
) -> Node<Expr> {
  match arg {
    Arg::Var(var) => identifier(var_namer.name_var(*var)),
    Arg::Const(c) => lower_const(c),
    Arg::Builtin(path) => lower_builtin(path),
    Arg::Fn(id) => {
      let mut expr = fn_emitter.emit_function(*id);
      expr.loc = DEFAULT_LOC;
      expr
    }
  }
}

pub fn lower_un_expr<V: VarNamer, F: FnEmitter>(
  var_namer: &V,
  fn_emitter: &F,
  op: UnOp,
  arg: &Arg,
) -> Node<Expr> {
  node(Expr::Unary(node(UnaryExpr {
    operator: un_operator(op),
    argument: lower_arg(var_namer, fn_emitter, arg),
  })))
}

pub fn lower_get_prop<V: VarNamer, F: FnEmitter>(
  var_namer: &V,
  fn_emitter: &F,
  object: &Arg,
  prop: &Arg,
) -> Node<Expr> {
  let object_expr = lower_arg(var_namer, fn_emitter, object);
  match prop {
    Arg::Const(Const::Str(key)) if is_valid_identifier(key) => {
      node(Expr::Member(node(MemberExpr {
        optional_chaining: false,
        left: object_expr,
        right: key.clone(),
      })))
    }
    _ => node(Expr::ComputedMember(node(ComputedMemberExpr {
      optional_chaining: false,
      object: object_expr,
      member: lower_arg(var_namer, fn_emitter, prop),
    }))),
  }
}

pub fn lower_bin_expr<V: VarNamer, F: FnEmitter>(
  var_namer: &V,
  fn_emitter: &F,
  op: BinOp,
  left: &Arg,
  right: &Arg,
) -> Node<Expr> {
  if matches!(op, BinOp::GetProp) {
    return lower_get_prop(var_namer, fn_emitter, left, right);
  }
  node(Expr::Binary(node(BinaryExpr {
    operator: bin_operator(op),
    left: lower_arg(var_namer, fn_emitter, left),
    right: lower_arg(var_namer, fn_emitter, right),
  })))
}

pub fn lower_value_inst<V: VarNamer, F: FnEmitter>(
  var_namer: &V,
  fn_emitter: &F,
  inst: &Inst,
) -> Option<Node<Expr>> {
  match inst.t {
    InstTyp::Bin => {
      let (_, left, op, right) = inst.as_bin();
      Some(lower_bin_expr(var_namer, fn_emitter, op, left, right))
    }
    InstTyp::Un => {
      let (_, op, arg) = inst.as_un();
      Some(lower_un_expr(var_namer, fn_emitter, op, arg))
    }
    InstTyp::ForeignLoad => Some(identifier(var_namer.name_foreign(inst.foreign))),
    InstTyp::UnknownLoad => Some(identifier(var_namer.name_unknown(&inst.unknown))),
    _ => None,
  }
}

fn var_binding<V: VarNamer>(
  var_namer: &V,
  tgt: u32,
  value: Node<Expr>,
  init: VarInit,
) -> Node<Stmt> {
  let name = var_namer.name_var(tgt);
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

pub fn lower_var_assign_inst<V: VarNamer, F: FnEmitter>(
  var_namer: &V,
  fn_emitter: &F,
  inst: &Inst,
  init: VarInit,
) -> Option<Node<Stmt>> {
  if inst.t != InstTyp::VarAssign {
    return None;
  }
  let (tgt, arg) = inst.as_var_assign();
  Some(var_binding(
    var_namer,
    tgt,
    lower_arg(var_namer, fn_emitter, arg),
    init,
  ))
}

pub fn lower_prop_assign<V: VarNamer, F: FnEmitter>(
  var_namer: &V,
  fn_emitter: &F,
  obj: &Arg,
  prop: &Arg,
  value: &Arg,
) -> Node<Stmt> {
  node(Stmt::Expr(node(ExprStmt {
    expr: node(Expr::Binary(node(BinaryExpr {
      operator: OperatorName::Assignment,
      left: lower_get_prop(var_namer, fn_emitter, obj, prop),
      right: lower_arg(var_namer, fn_emitter, value),
    }))),
  })))
}

pub fn lower_prop_assign_inst<V: VarNamer, F: FnEmitter>(
  var_namer: &V,
  fn_emitter: &F,
  inst: &Inst,
) -> Option<Node<Stmt>> {
  if inst.t != InstTyp::PropAssign {
    return None;
  }
  let (obj, prop, value) = inst.as_prop_assign();
  Some(lower_prop_assign(var_namer, fn_emitter, obj, prop, value))
}

pub fn lower_foreign_store_inst<V: VarNamer, F: FnEmitter>(
  var_namer: &V,
  fn_emitter: &F,
  inst: &Inst,
) -> Option<Node<Stmt>> {
  if inst.t != InstTyp::ForeignStore {
    return None;
  }
  let (_, arg) = inst.as_foreign_store();
  let left = identifier(var_namer.name_foreign(inst.foreign));
  Some(node(Stmt::Expr(node(ExprStmt {
    expr: node(Expr::Binary(node(BinaryExpr {
      operator: OperatorName::Assignment,
      left,
      right: lower_arg(var_namer, fn_emitter, arg),
    }))),
  }))))
}

pub fn lower_unknown_store_inst<V: VarNamer, F: FnEmitter>(
  var_namer: &V,
  fn_emitter: &F,
  inst: &Inst,
) -> Option<Node<Stmt>> {
  if inst.t != InstTyp::UnknownStore {
    return None;
  }
  let (_, arg) = inst.as_unknown_store();
  let left = identifier(var_namer.name_unknown(&inst.unknown));
  Some(node(Stmt::Expr(node(ExprStmt {
    expr: node(Expr::Binary(node(BinaryExpr {
      operator: OperatorName::Assignment,
      left,
      right: lower_arg(var_namer, fn_emitter, arg),
    }))),
  }))))
}

fn expr_eq(left: &Node<Expr>, right: &Node<Expr>) -> bool {
  match (left.stx.as_ref(), right.stx.as_ref()) {
    (Expr::Id(a), Expr::Id(b)) => a.stx.name == b.stx.name,
    (Expr::LitNum(a), Expr::LitNum(b)) => a.stx.value == b.stx.value,
    (Expr::LitStr(a), Expr::LitStr(b)) => a.stx.value == b.stx.value,
    (Expr::LitBool(a), Expr::LitBool(b)) => a.stx.value == b.stx.value,
    (Expr::LitNull(_), Expr::LitNull(_)) => true,
    (Expr::Member(a), Expr::Member(b)) => {
      a.stx.optional_chaining == b.stx.optional_chaining
        && a.stx.right == b.stx.right
        && expr_eq(&a.stx.left, &b.stx.left)
    }
    (Expr::ComputedMember(a), Expr::ComputedMember(b)) => {
      a.stx.optional_chaining == b.stx.optional_chaining
        && expr_eq(&a.stx.object, &b.stx.object)
        && expr_eq(&a.stx.member, &b.stx.member)
    }
    _ => false,
  }
}

fn call_args(args: Vec<Node<Expr>>, spreads: &[usize]) -> Vec<Node<CallArg>> {
  args
    .into_iter()
    .enumerate()
    .map(|(i, expr)| {
      let spread = spreads.contains(&(i + 2));
      node(CallArg {
        spread,
        value: expr,
      })
    })
    .collect()
}

pub fn lower_call_inst<V: VarNamer, F: FnEmitter>(
  var_namer: &V,
  fn_emitter: &F,
  inst: &Inst,
  callee_expr: Option<Node<Expr>>,
  this_expr: Option<Node<Expr>>,
  arg_exprs: Option<Vec<Node<Expr>>>,
  target_init: VarInit,
) -> Option<Node<Stmt>> {
  if inst.t != InstTyp::Call {
    return None;
  }
  let (tgt, callee_arg, this_arg, args, spreads) = inst.as_call();
  let callee_expr = callee_expr.unwrap_or_else(|| lower_arg(var_namer, fn_emitter, callee_arg));
  let this_expr = this_expr.unwrap_or_else(|| lower_arg(var_namer, fn_emitter, this_arg));
  let args_exprs = arg_exprs.unwrap_or_else(|| {
    args
      .iter()
      .map(|a| lower_arg(var_namer, fn_emitter, a))
      .collect()
  });
  let this_defined = !matches!(this_arg, Arg::Const(Const::Undefined));
  let args_nodes = call_args(args_exprs, spreads);

  let use_member_call = match callee_expr.stx.as_ref() {
    Expr::Member(m) => this_defined && expr_eq(&this_expr, &m.stx.left),
    Expr::ComputedMember(m) => this_defined && expr_eq(&this_expr, &m.stx.object),
    _ => false,
  };

  let call_expr = if use_member_call {
    node(Expr::Call(node(CallExpr {
      optional_chaining: false,
      callee: callee_expr,
      arguments: args_nodes,
    })))
  } else if this_defined {
    let mut arguments = Vec::with_capacity(args_nodes.len() + 1);
    arguments.push(node(CallArg {
      spread: false,
      value: this_expr,
    }));
    arguments.extend(args_nodes);
    let callee = node(Expr::Member(node(MemberExpr {
      optional_chaining: false,
      left: callee_expr,
      right: "call".to_string(),
    })));
    node(Expr::Call(node(CallExpr {
      optional_chaining: false,
      callee,
      arguments,
    })))
  } else {
    node(Expr::Call(node(CallExpr {
      optional_chaining: false,
      callee: callee_expr,
      arguments: args_nodes,
    })))
  };

  match tgt {
    Some(tgt) => Some(var_binding(var_namer, tgt, call_expr, target_init)),
    None => Some(node(Stmt::Expr(node(ExprStmt { expr: call_expr })))),
  }
}

pub fn lower_effect_inst<V: VarNamer, F: FnEmitter>(
  var_namer: &V,
  fn_emitter: &F,
  inst: &Inst,
  init: VarInit,
) -> Option<Node<Stmt>> {
  match inst.t {
    InstTyp::VarAssign => lower_var_assign_inst(var_namer, fn_emitter, inst, init),
    InstTyp::PropAssign => lower_prop_assign_inst(var_namer, fn_emitter, inst),
    InstTyp::ForeignStore => lower_foreign_store_inst(var_namer, fn_emitter, inst),
    InstTyp::UnknownStore => lower_unknown_store_inst(var_namer, fn_emitter, inst),
    InstTyp::Call => lower_call_inst(var_namer, fn_emitter, inst, None, None, None, init),
    _ => None,
  }
}
