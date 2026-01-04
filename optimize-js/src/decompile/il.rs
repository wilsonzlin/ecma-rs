use super::foreign::ForeignBindings;
use crate::il::inst::{Arg, BinOp, Const, Inst, InstTyp, UnOp};
use crate::symbol::semantics::SymbolId;
use crate::{Program, ProgramFunction};
use derive_visitor::{Drive, DriveMut};
use num_bigint::BigInt;
use parse_js::ast::class_or_object::{
  ClassOrObjKey, ClassOrObjMemberDirectKey, ClassOrObjVal, ObjMember, ObjMemberType,
};
use parse_js::ast::expr::lit::{
  LitArrElem, LitArrExpr, LitBigIntExpr, LitBoolExpr, LitNullExpr, LitNumExpr, LitObjExpr,
  LitRegexExpr, LitStrExpr, LitTemplateExpr, LitTemplatePart,
};
use parse_js::ast::expr::pat::{IdPat, Pat};
use parse_js::ast::expr::{
  BinaryExpr, CallArg, CallExpr, ComputedMemberExpr, Expr, IdExpr, ImportExpr, MemberExpr,
  TaggedTemplateExpr, UnaryExpr,
};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{PatDecl, VarDecl, VarDeclMode, VarDeclarator};
use parse_js::ast::stmt::{ExprStmt, Stmt};
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;
use parse_js::token::TT;
use std::collections::{BTreeMap, BTreeSet};

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
  fn name_foreign(&self, symbol: SymbolId) -> String;
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecompileError {
  Unsupported(String),
}

pub type DecompileResult<T> = Result<T, DecompileError>;

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
    BinOp::BitAnd => OperatorName::BitwiseAnd,
    BinOp::BitOr => OperatorName::BitwiseOr,
    BinOp::BitXor => OperatorName::BitwiseXor,
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
    BinOp::Shl => OperatorName::BitwiseLeftShift,
    BinOp::Shr => OperatorName::BitwiseRightShift,
    BinOp::UShr => OperatorName::BitwiseUnsignedRightShift,
    BinOp::StrictEq => OperatorName::StrictEquality,
    BinOp::Sub => OperatorName::Subtraction,
    BinOp::GetProp => panic!("GetProp is handled separately"),
    BinOp::_Dummy => unreachable!("dummy bin op should not be lowered"),
  }
}

fn un_operator(op: UnOp) -> OperatorName {
  match op {
    UnOp::BitNot => OperatorName::BitwiseNot,
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
  if !(first == '$' || first == '_' || first.is_ascii_alphabetic() || first.is_alphabetic()) {
    return false;
  }
  chars.all(|c| c == '$' || c == '_' || c.is_ascii_alphanumeric() || c.is_alphanumeric())
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
  const INTERNAL_IN_CALLEE: &str = "__optimize_js_in";
  const INTERNAL_INSTANCEOF_CALLEE: &str = "__optimize_js_instanceof";
  const INTERNAL_DELETE_CALLEE: &str = "__optimize_js_delete";
  const INTERNAL_NEW_CALLEE: &str = "__optimize_js_new";
  const INTERNAL_REGEX_CALLEE: &str = "__optimize_js_regex";
  const INTERNAL_ARRAY_CALLEE: &str = "__optimize_js_array";
  const INTERNAL_ARRAY_HOLE: &str = "__optimize_js_array_hole";
  const INTERNAL_OBJECT_CALLEE: &str = "__optimize_js_object";
  const INTERNAL_OBJECT_PROP_MARKER: &str = "__optimize_js_object_prop";
  const INTERNAL_OBJECT_COMPUTED_MARKER: &str = "__optimize_js_object_prop_computed";
  const INTERNAL_OBJECT_SPREAD_MARKER: &str = "__optimize_js_object_spread";
  const INTERNAL_TEMPLATE_CALLEE: &str = "__optimize_js_template";
  const INTERNAL_TAGGED_TEMPLATE_CALLEE: &str = "__optimize_js_tagged_template";

  if inst.t != InstTyp::Call {
    return None;
  }
  let (tgt, callee_arg, this_arg, args, spreads) = inst.as_call();

  if let Arg::Builtin(path) = callee_arg {
    if path == INTERNAL_NEW_CALLEE {
      let ctor_expr = this_expr.unwrap_or_else(|| lower_arg(var_namer, fn_emitter, this_arg));
      let args_exprs = arg_exprs.unwrap_or_else(|| {
        args
          .iter()
          .map(|a| lower_arg(var_namer, fn_emitter, a))
          .collect()
      });
      let call_expr = node(Expr::Call(node(CallExpr {
        optional_chaining: false,
        callee: ctor_expr,
        arguments: call_args(args_exprs, spreads),
      })));
      let expr = node(Expr::Unary(node(UnaryExpr {
        operator: OperatorName::New,
        argument: call_expr,
      })));
      return match tgt {
        Some(tgt) => Some(var_binding(var_namer, tgt, expr, target_init)),
        None => Some(node(Stmt::Expr(node(ExprStmt { expr })))),
      };
    }
  }

  if matches!(callee_arg, Arg::Builtin(path) if path == INTERNAL_ARRAY_CALLEE)
    && matches!(this_arg, Arg::Const(Const::Undefined))
  {
    let mut elements = Vec::with_capacity(args.len());
    for (idx, arg) in args.iter().enumerate() {
      let is_spread = spreads.contains(&(idx + 2));
      if is_spread {
        elements.push(LitArrElem::Rest(lower_arg(var_namer, fn_emitter, arg)));
      } else if matches!(arg, Arg::Builtin(path) if path == INTERNAL_ARRAY_HOLE) {
        elements.push(LitArrElem::Empty);
      } else {
        elements.push(LitArrElem::Single(lower_arg(var_namer, fn_emitter, arg)));
      }
    }
    let expr = node(Expr::LitArr(node(LitArrExpr { elements })));
    return match tgt {
      Some(tgt) => Some(var_binding(var_namer, tgt, expr, target_init)),
      None => Some(node(Stmt::Expr(node(ExprStmt { expr })))),
    };
  }

  if matches!(callee_arg, Arg::Builtin(path) if path == INTERNAL_OBJECT_CALLEE)
    && matches!(this_arg, Arg::Const(Const::Undefined))
    && spreads.is_empty()
  {
    assert!(
      args.len() % 3 == 0,
      "object literal marker call must have arg count divisible by 3"
    );
    let mut members = Vec::with_capacity(args.len() / 3);
    for chunk in args.chunks(3) {
      let marker = &chunk[0];
      let key_or_value = &chunk[1];
      let value = &chunk[2];

      let Arg::Builtin(marker) = marker else {
        panic!("object literal marker call expects builtin markers, got {marker:?}");
      };
      match marker.as_str() {
        INTERNAL_OBJECT_PROP_MARKER => {
          let Arg::Const(Const::Str(key)) = key_or_value else {
            panic!("object literal prop marker expects string key, got {key_or_value:?}");
          };
          let tt = if is_valid_identifier(key) {
            TT::Identifier
          } else {
            TT::LiteralString
          };
          let key = ClassOrObjKey::Direct(node(ClassOrObjMemberDirectKey {
            key: key.clone(),
            tt,
          }));
          let val = ClassOrObjVal::Prop(Some(lower_arg(var_namer, fn_emitter, value)));
          members.push(node(ObjMember {
            typ: ObjMemberType::Valued { key, val },
          }));
        }
        INTERNAL_OBJECT_COMPUTED_MARKER => {
          let key = ClassOrObjKey::Computed(lower_arg(var_namer, fn_emitter, key_or_value));
          let val = ClassOrObjVal::Prop(Some(lower_arg(var_namer, fn_emitter, value)));
          members.push(node(ObjMember {
            typ: ObjMemberType::Valued { key, val },
          }));
        }
        INTERNAL_OBJECT_SPREAD_MARKER => {
          members.push(node(ObjMember {
            typ: ObjMemberType::Rest {
              val: lower_arg(var_namer, fn_emitter, key_or_value),
            },
          }));
        }
        other => panic!("unknown object literal marker {other:?}"),
      }
    }

    let expr = node(Expr::LitObj(node(LitObjExpr { members })));
    return match tgt {
      Some(tgt) => Some(var_binding(var_namer, tgt, expr, target_init)),
      None => Some(node(Stmt::Expr(node(ExprStmt { expr })))),
    };
  }

  if matches!(callee_arg, Arg::Builtin(path) if path == INTERNAL_TEMPLATE_CALLEE)
    && matches!(this_arg, Arg::Const(Const::Undefined))
    && spreads.is_empty()
  {
    assert!(
      args.len() % 2 == 1,
      "template literal marker call must have odd arg count"
    );
    let mut parts = Vec::with_capacity(args.len());
    for (idx, arg) in args.iter().enumerate() {
      if idx % 2 == 0 {
        let Arg::Const(Const::Str(segment)) = arg else {
          panic!("template literal expects string segments, got {arg:?}");
        };
        parts.push(LitTemplatePart::String(segment.clone()));
      } else {
        parts.push(LitTemplatePart::Substitution(lower_arg(
          var_namer, fn_emitter, arg,
        )));
      }
    }

    let expr = node(Expr::LitTemplate(node(LitTemplateExpr { parts })));
    return match tgt {
      Some(tgt) => Some(var_binding(var_namer, tgt, expr, target_init)),
      None => Some(node(Stmt::Expr(node(ExprStmt { expr })))),
    };
  }

  if matches!(callee_arg, Arg::Builtin(path) if path == INTERNAL_TAGGED_TEMPLATE_CALLEE)
    && matches!(this_arg, Arg::Const(Const::Undefined))
    && spreads.is_empty()
  {
    assert!(
      args.len() >= 2 && args.len() % 2 == 0,
      "tagged template marker call must have even arg count >= 2"
    );
    let tag_expr = lower_arg(var_namer, fn_emitter, &args[0]);

    let mut parts = Vec::with_capacity(args.len() - 1);
    for (idx, arg) in args[1..].iter().enumerate() {
      if idx % 2 == 0 {
        let Arg::Const(Const::Str(segment)) = arg else {
          panic!("tagged template expects string segments, got {arg:?}");
        };
        parts.push(LitTemplatePart::String(segment.clone()));
      } else {
        parts.push(LitTemplatePart::Substitution(lower_arg(
          var_namer, fn_emitter, arg,
        )));
      }
    }

    let expr = node(Expr::TaggedTemplate(node(TaggedTemplateExpr {
      function: tag_expr,
      parts,
    })));
    return match tgt {
      Some(tgt) => Some(var_binding(var_namer, tgt, expr, target_init)),
      None => Some(node(Stmt::Expr(node(ExprStmt { expr })))),
    };
  }

  if spreads.is_empty()
    && matches!(this_arg, Arg::Const(Const::Undefined))
    && matches!(callee_arg, Arg::Builtin(path) if path == "import")
    && (args.len() == 1 || args.len() == 2)
  {
    let module = lower_arg(var_namer, fn_emitter, &args[0]);
    let attributes = args
      .get(1)
      .map(|arg| lower_arg(var_namer, fn_emitter, arg));
    let expr = node(Expr::Import(node(ImportExpr { module, attributes })));
    return match tgt {
      Some(tgt) => Some(var_binding(var_namer, tgt, expr, target_init)),
      None => Some(node(Stmt::Expr(node(ExprStmt { expr })))),
    };
  }

  if spreads.is_empty() && matches!(this_arg, Arg::Const(Const::Undefined)) && args.len() == 1 {
    if let (Arg::Builtin(path), Arg::Const(Const::Str(regex))) = (callee_arg, &args[0]) {
      if path == INTERNAL_REGEX_CALLEE {
        let expr = node(Expr::LitRegex(node(LitRegexExpr {
          value: regex.clone(),
        })));
        return match tgt {
          Some(tgt) => Some(var_binding(var_namer, tgt, expr, target_init)),
          None => Some(node(Stmt::Expr(node(ExprStmt { expr })))),
        };
      }
    }
  }

  if spreads.is_empty() && matches!(this_arg, Arg::Const(Const::Undefined)) && args.len() == 2 {
    if let Arg::Builtin(path) = callee_arg {
      if path == INTERNAL_DELETE_CALLEE {
        let member = lower_get_prop(var_namer, fn_emitter, &args[0], &args[1]);
        let expr = node(Expr::Unary(node(UnaryExpr {
          operator: OperatorName::Delete,
          argument: member,
        })));
        return match tgt {
          Some(tgt) => Some(var_binding(var_namer, tgt, expr, target_init)),
          None => Some(node(Stmt::Expr(node(ExprStmt { expr })))),
        };
      }

      let op = if path == INTERNAL_IN_CALLEE {
        Some(OperatorName::In)
      } else if path == INTERNAL_INSTANCEOF_CALLEE {
        Some(OperatorName::Instanceof)
      } else {
        None
      };
      if let Some(op) = op {
        let expr = node(Expr::Binary(node(BinaryExpr {
          operator: op,
          left: lower_arg(var_namer, fn_emitter, &args[0]),
          right: lower_arg(var_namer, fn_emitter, &args[1]),
        })));
        return match tgt {
          Some(tgt) => Some(var_binding(var_namer, tgt, expr, target_init)),
          None => Some(node(Stmt::Expr(node(ExprStmt { expr })))),
        };
      }
    }
  }

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

fn temp_name(id: u32) -> String {
  format!("t{id}")
}

#[derive(Clone)]
struct FlatCallArg {
  expr: FlatExpr,
  spread: bool,
}

#[derive(Clone)]
enum FlatExpr {
  Identifier(String),
  Member {
    object: Box<FlatExpr>,
    property: String,
  },
  ComputedMember {
    object: Box<FlatExpr>,
    property: Box<FlatExpr>,
  },
  Call {
    callee: Box<FlatExpr>,
    args: Vec<FlatCallArg>,
  },
  Binary {
    op: OperatorName,
    left: Box<FlatExpr>,
    right: Box<FlatExpr>,
  },
  Unary {
    op: OperatorName,
    arg: Box<FlatExpr>,
  },
  Bool(bool),
  Num(JsNumber),
  Str(String),
  Null,
  Undefined,
  BigInt(BigInt),
}

#[derive(Clone)]
enum ValueOrigin {
  GetProp { object: Arg, prop: Arg },
  Other,
}

#[derive(Clone)]
struct VarValue {
  expr: FlatExpr,
  origin: ValueOrigin,
}

fn builtin_to_expr(path: &str) -> FlatExpr {
  let mut parts = path.split('.');
  let first = parts
    .next()
    .expect("builtin path should contain at least one segment");
  let mut expr = FlatExpr::Identifier(first.to_string());
  for part in parts {
    expr = FlatExpr::Member {
      object: Box::new(expr),
      property: part.to_string(),
    };
  }
  expr
}

fn expr_from_arg(arg: &Arg, env: &BTreeMap<u32, VarValue>) -> FlatExpr {
  match arg {
    Arg::Var(id) => env
      .get(id)
      .map(|value| value.expr.clone())
      .unwrap_or_else(|| FlatExpr::Identifier(temp_name(*id))),
    Arg::Const(Const::Bool(value)) => FlatExpr::Bool(*value),
    Arg::Const(Const::Num(value)) => FlatExpr::Num(*value),
    Arg::Const(Const::Str(value)) => FlatExpr::Str(value.clone()),
    Arg::Const(Const::Null) => FlatExpr::Null,
    Arg::Const(Const::Undefined) => FlatExpr::Undefined,
    Arg::Const(Const::BigInt(value)) => FlatExpr::BigInt(value.clone()),
    Arg::Builtin(path) => builtin_to_expr(path),
    Arg::Fn(id) => FlatExpr::Identifier(format!("fn{id}")),
  }
}

fn origin_from_arg(arg: &Arg, env: &BTreeMap<u32, VarValue>) -> ValueOrigin {
  match arg {
    Arg::Var(id) => env
      .get(id)
      .map(|value| value.origin.clone())
      .unwrap_or(ValueOrigin::Other),
    _ => ValueOrigin::Other,
  }
}

fn member_from_prop(object: &FlatExpr, prop: &Arg, env: &BTreeMap<u32, VarValue>) -> FlatExpr {
  match prop {
    Arg::Const(Const::Str(key)) if is_valid_identifier(key) => FlatExpr::Member {
      object: Box::new(object.clone()),
      property: key.clone(),
    },
    _ => FlatExpr::ComputedMember {
      object: Box::new(object.clone()),
      property: Box::new(expr_from_arg(prop, env)),
    },
  }
}

fn to_ast_expr(expr: &FlatExpr) -> Node<Expr> {
  match expr {
    FlatExpr::Identifier(name) => identifier(name.clone()),
    FlatExpr::Member { object, property } => node(Expr::Member(node(MemberExpr {
      optional_chaining: false,
      left: to_ast_expr(object),
      right: property.clone(),
    }))),
    FlatExpr::ComputedMember { object, property } => {
      node(Expr::ComputedMember(node(ComputedMemberExpr {
        optional_chaining: false,
        object: to_ast_expr(object),
        member: to_ast_expr(property),
      })))
    }
    FlatExpr::Call { callee, args } => {
      let arguments = args
        .iter()
        .map(|arg| {
          node(CallArg {
            spread: arg.spread,
            value: to_ast_expr(&arg.expr),
          })
        })
        .collect();
      node(Expr::Call(node(CallExpr {
        optional_chaining: false,
        callee: to_ast_expr(callee),
        arguments,
      })))
    }
    FlatExpr::Binary { op, left, right } => node(Expr::Binary(node(BinaryExpr {
      operator: *op,
      left: to_ast_expr(left),
      right: to_ast_expr(right),
    }))),
    FlatExpr::Unary { op, arg } => node(Expr::Unary(node(UnaryExpr {
      operator: *op,
      argument: to_ast_expr(arg),
    }))),
    FlatExpr::Bool(value) => node(Expr::LitBool(node(LitBoolExpr { value: *value }))),
    FlatExpr::Num(value) => node(Expr::LitNum(node(LitNumExpr { value: *value }))),
    FlatExpr::Str(value) => node(Expr::LitStr(node(LitStrExpr {
      value: value.clone(),
    }))),
    FlatExpr::Null => node(Expr::LitNull(node(LitNullExpr {}))),
    FlatExpr::Undefined => node(Expr::Unary(node(UnaryExpr {
      operator: OperatorName::Void,
      argument: node(Expr::LitNum(node(LitNumExpr {
        value: JsNumber(0.0),
      }))),
    }))),
    FlatExpr::BigInt(value) => node(Expr::LitBigInt(node(LitBigIntExpr {
      value: format!("{value}n"),
    }))),
  }
}

fn expr_stmt(expr: FlatExpr) -> Node<Stmt> {
  node(Stmt::Expr(node(ExprStmt {
    expr: to_ast_expr(&expr),
  })))
}

fn assignment_stmt(lhs: FlatExpr, rhs: FlatExpr) -> Node<Stmt> {
  node(Stmt::Expr(node(ExprStmt {
    expr: node(Expr::Binary(node(BinaryExpr {
      operator: OperatorName::Assignment,
      left: to_ast_expr(&lhs),
      right: to_ast_expr(&rhs),
    }))),
  })))
}

fn handle_call(inst: &Inst, env: &BTreeMap<u32, VarValue>) -> (FlatExpr, Option<u32>) {
  let (tgt, callee, this_arg, args, spreads) = inst.as_call();
  let callee_expr = expr_from_arg(callee, env);
  let this_expr = expr_from_arg(this_arg, env);
  let args_exprs: Vec<_> = args
    .iter()
    .enumerate()
    .map(|(i, arg)| FlatCallArg {
      expr: expr_from_arg(arg, env),
      spread: spreads.contains(&(i + 2)),
    })
    .collect();

  let this_is_undefined = matches!(this_arg, Arg::Const(Const::Undefined));
  if this_is_undefined {
    return (
      FlatExpr::Call {
        callee: Box::new(callee_expr),
        args: args_exprs,
      },
      tgt,
    );
  }

  let callee_origin = match callee {
    Arg::Var(id) => env.get(id).map(|value| value.origin.clone()),
    _ => None,
  };

  let (call_callee, call_args) = match callee_origin {
    Some(ValueOrigin::GetProp { object, prop }) if this_arg == &object => {
      (member_from_prop(&this_expr, &prop, env), args_exprs)
    }
    _ => {
      let mut call_args = Vec::with_capacity(args_exprs.len() + 1);
      call_args.push(FlatCallArg {
        expr: this_expr,
        spread: false,
      });
      call_args.extend(args_exprs);
      (
        FlatExpr::Member {
          object: Box::new(callee_expr),
          property: "call".to_string(),
        },
        call_args,
      )
    }
  };

  (
    FlatExpr::Call {
      callee: Box::new(call_callee),
      args: call_args,
    },
    tgt,
  )
}

/// Decompiles IL into a flat list of JS statements.
///
/// This is intentionally limited today: it only supports straight-line control
/// flow and emits statements in execution order. The output is useful for
/// debugging and for validating individual lowering rules (for example, `this`
/// handling in calls).
pub fn decompile_function(func: &ProgramFunction) -> DecompileResult<Vec<Node<Stmt>>> {
  let cfg = &func.body;
  let all_labels = cfg.graph.sorted_labels();
  if !all_labels.contains(&0) {
    return Err(DecompileError::Unsupported(
      "CFG missing entry block".to_string(),
    ));
  }

  let mut env = BTreeMap::<u32, VarValue>::new();
  let mut stmts = Vec::new();
  let mut visited = BTreeSet::<u32>::new();

  let mut label = 0u32;
  loop {
    if !visited.insert(label) {
      return Err(DecompileError::Unsupported(
        "cyclic control flow not supported".to_string(),
      ));
    }

    for inst in cfg.bblocks.get(label) {
      match inst.t {
        InstTyp::UnknownLoad => {
          let (tgt, name) = inst.as_unknown_load();
          env.insert(
            tgt,
            VarValue {
              expr: FlatExpr::Identifier(name.clone()),
              origin: ValueOrigin::Other,
            },
          );
        }
        InstTyp::ForeignLoad => {
          let (tgt, sym) = inst.as_foreign_load();
          env.insert(
            tgt,
            VarValue {
              expr: FlatExpr::Identifier(format!("f{}", sym.raw_id())),
              origin: ValueOrigin::Other,
            },
          );
        }
        InstTyp::VarAssign => {
          let (tgt, arg) = inst.as_var_assign();
          let expr = expr_from_arg(arg, &env);
          let origin = origin_from_arg(arg, &env);
          env.insert(tgt, VarValue { expr, origin });
        }
        InstTyp::Bin => {
          let (tgt, left, op, right) = inst.as_bin();
          if op == BinOp::GetProp {
            let object_expr = expr_from_arg(left, &env);
            let expr = member_from_prop(&object_expr, right, &env);
            env.insert(
              tgt,
              VarValue {
                expr,
                origin: ValueOrigin::GetProp {
                  object: left.clone(),
                  prop: right.clone(),
                },
              },
            );
          } else {
            let expr = FlatExpr::Binary {
              op: bin_operator(op),
              left: Box::new(expr_from_arg(left, &env)),
              right: Box::new(expr_from_arg(right, &env)),
            };
            env.insert(
              tgt,
              VarValue {
                expr,
                origin: ValueOrigin::Other,
              },
            );
          }
        }
        InstTyp::Un => {
          let (tgt, op, arg) = inst.as_un();
          env.insert(
            tgt,
            VarValue {
              expr: FlatExpr::Unary {
                op: un_operator(op),
                arg: Box::new(expr_from_arg(arg, &env)),
              },
              origin: ValueOrigin::Other,
            },
          );
        }
        InstTyp::Call => {
          let (call_expr, tgt) = handle_call(inst, &env);
          if let Some(tgt) = tgt {
            let lhs = FlatExpr::Identifier(temp_name(tgt));
            stmts.push(assignment_stmt(lhs.clone(), call_expr));
            env.insert(
              tgt,
              VarValue {
                expr: lhs,
                origin: ValueOrigin::Other,
              },
            );
          } else {
            stmts.push(expr_stmt(call_expr));
          }
        }
        InstTyp::PropAssign => {
          let (obj, prop, value) = inst.as_prop_assign();
          let object_expr = expr_from_arg(obj, &env);
          let left = member_from_prop(&object_expr, prop, &env);
          let right = expr_from_arg(value, &env);
          stmts.push(assignment_stmt(left, right));
        }
        InstTyp::UnknownStore => {
          let (name, value) = inst.as_unknown_store();
          stmts.push(assignment_stmt(
            FlatExpr::Identifier(name.clone()),
            expr_from_arg(value, &env),
          ));
        }
        InstTyp::ForeignStore => {
          let (sym, value) = inst.as_foreign_store();
          stmts.push(assignment_stmt(
            FlatExpr::Identifier(format!("f{}", sym.raw_id())),
            expr_from_arg(value, &env),
          ));
        }
        InstTyp::_Dummy => {}
        InstTyp::CondGoto | InstTyp::Phi | InstTyp::_Goto | InstTyp::_Label => {
          return Err(DecompileError::Unsupported(
            "control flow not supported".to_string(),
          ));
        }
      }
    }

    match cfg.terminator(label) {
      crate::cfg::cfg::Terminator::Stop => break,
      crate::cfg::cfg::Terminator::Goto(next) => label = next,
      crate::cfg::cfg::Terminator::CondGoto { .. } | crate::cfg::cfg::Terminator::Multi { .. } => {
        return Err(DecompileError::Unsupported(
          "control flow not supported".to_string(),
        ));
      }
    }
  }

  if visited.len() != all_labels.len() {
    return Err(DecompileError::Unsupported(
      "non-linear control flow not supported".to_string(),
    ));
  }

  Ok(stmts)
}

pub fn decompile_program(program: &Program) -> DecompileResult<Node<TopLevel>> {
  let body = decompile_function(&program.top_level)?;
  Ok(node(TopLevel { body }))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoweredArg {
  Builtin(String),
  Const(Const),
  Fn(usize),
  Ident(String),
  Var(u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoweredInst {
  Bin {
    tgt: u32,
    left: LoweredArg,
    op: BinOp,
    right: LoweredArg,
  },
  Call {
    tgt: Option<u32>,
    callee: LoweredArg,
    this_: LoweredArg,
    args: Vec<LoweredArg>,
    spreads: Vec<usize>,
  },
  CondGoto {
    cond: LoweredArg,
    t_label: u32,
    f_label: u32,
  },
  Goto {
    label: u32,
  },
  IdentLoad {
    tgt: u32,
    name: String,
  },
  IdentStore {
    name: String,
    value: LoweredArg,
  },
  Label {
    label: u32,
  },
  Phi {
    tgt: u32,
    labels: Vec<u32>,
    args: Vec<LoweredArg>,
  },
  PropAssign {
    obj: LoweredArg,
    prop: LoweredArg,
    value: LoweredArg,
  },
  Un {
    tgt: u32,
    op: UnOp,
    arg: LoweredArg,
  },
  VarAssign {
    tgt: u32,
    value: LoweredArg,
  },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoweredBlock {
  pub label: u32,
  pub insts: Vec<LoweredInst>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoweredFunction {
  pub bblocks: Vec<LoweredBlock>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoweredProgram {
  pub foreign_bindings: ForeignBindings,
  pub top_level: LoweredFunction,
  pub functions: Vec<LoweredFunction>,
}

fn lowered_arg(arg: &Arg) -> LoweredArg {
  match arg {
    Arg::Builtin(v) => LoweredArg::Builtin(v.clone()),
    Arg::Const(v) => LoweredArg::Const(v.clone()),
    Arg::Fn(v) => LoweredArg::Fn(*v),
    Arg::Var(v) => LoweredArg::Var(*v),
  }
}

fn lower_inst(inst: &Inst, bindings: &ForeignBindings) -> LoweredInst {
  match inst.t {
    InstTyp::Bin => LoweredInst::Bin {
      tgt: inst.tgts[0],
      left: lowered_arg(&inst.args[0]),
      op: inst.bin_op,
      right: lowered_arg(&inst.args[1]),
    },
    InstTyp::Un => LoweredInst::Un {
      tgt: inst.tgts[0],
      op: inst.un_op,
      arg: lowered_arg(&inst.args[0]),
    },
    InstTyp::VarAssign => LoweredInst::VarAssign {
      tgt: inst.tgts[0],
      value: lowered_arg(&inst.args[0]),
    },
    InstTyp::PropAssign => LoweredInst::PropAssign {
      obj: lowered_arg(&inst.args[0]),
      prop: lowered_arg(&inst.args[1]),
      value: lowered_arg(&inst.args[2]),
    },
    InstTyp::CondGoto => LoweredInst::CondGoto {
      cond: lowered_arg(&inst.args[0]),
      t_label: inst.labels[0],
      f_label: inst.labels[1],
    },
    InstTyp::Call => LoweredInst::Call {
      tgt: inst.tgts.get(0).copied(),
      callee: lowered_arg(&inst.args[0]),
      this_: lowered_arg(&inst.args[1]),
      args: inst.args[2..].iter().map(lowered_arg).collect(),
      spreads: inst.spreads.clone(),
    },
    InstTyp::ForeignLoad => LoweredInst::IdentLoad {
      tgt: inst.tgts[0],
      name: bindings
        .name_for(inst.foreign)
        .expect("missing foreign binding")
        .to_string(),
    },
    InstTyp::ForeignStore => LoweredInst::IdentStore {
      name: bindings
        .name_for(inst.foreign)
        .expect("missing foreign binding")
        .to_string(),
      value: lowered_arg(&inst.args[0]),
    },
    InstTyp::UnknownLoad => LoweredInst::IdentLoad {
      tgt: inst.tgts[0],
      name: inst.unknown.clone(),
    },
    InstTyp::UnknownStore => LoweredInst::IdentStore {
      name: inst.unknown.clone(),
      value: lowered_arg(&inst.args[0]),
    },
    InstTyp::Phi => LoweredInst::Phi {
      tgt: inst.tgts[0],
      labels: inst.labels.clone(),
      args: inst.args.iter().map(lowered_arg).collect(),
    },
    InstTyp::_Label => LoweredInst::Label {
      label: inst.labels[0],
    },
    InstTyp::_Goto => LoweredInst::Goto {
      label: inst.labels[0],
    },
    InstTyp::_Dummy => unreachable!("cannot lower dummy inst"),
  }
}

fn lower_function_inner(func: &ProgramFunction, bindings: &ForeignBindings) -> LoweredFunction {
  let mut bblocks: Vec<_> = func.body.bblocks.all().collect();
  bblocks.sort_by_key(|(label, _)| *label);

  let mut lowered_blocks = Vec::with_capacity(bblocks.len());
  for (label, insts) in bblocks.into_iter() {
    lowered_blocks.push(LoweredBlock {
      label,
      insts: insts.iter().map(|i| lower_inst(i, bindings)).collect(),
    });
  }

  LoweredFunction {
    bblocks: lowered_blocks,
  }
}

pub fn lower_function(func: &ProgramFunction, bindings: &ForeignBindings) -> LoweredFunction {
  lower_function_inner(func, bindings)
}

pub fn lower_program(program: &Program) -> LoweredProgram {
  let foreign_bindings = super::foreign::collect_foreign_bindings(program);
  let top_level = lower_function_inner(&program.top_level, &foreign_bindings);
  let functions = program
    .functions
    .iter()
    .map(|f| lower_function_inner(f, &foreign_bindings))
    .collect();

  LoweredProgram {
    foreign_bindings,
    top_level,
    functions,
  }
}
