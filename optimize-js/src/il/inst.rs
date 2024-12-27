use ahash::HashMap;
use itertools::Itertools;
use num_bigint::BigInt;
use parse_js::num::JsNumber;
use serde::Serialize;
use symbol_js::symbol::Symbol;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::fmt::{self};

// PartialOrd and Ord are for some arbitrary canonical order, even if semantics of ordering is opaque.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub enum Const {
  BigInt(BigInt),
  Bool(bool),
  Null,
  Num(JsNumber),
  Str(String),
  Undefined,
}

impl Debug for Const {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      Self::BigInt(v) => write!(f, "{v}"),
      Self::Bool(v) => write!(f, "{v}"),
      Self::Null => write!(f, "null"),
      Self::Num(v) => write!(f, "{v}"),
      Self::Str(v) => write!(f, "'{v}'"),
      Self::Undefined => write!(f, "undefined"),
    }
  }
}

// PartialOrd and Ord are for some arbitrary canonical order, even if semantics of ordering are opaque.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub enum Arg {
  Builtin(String), // The value is a path (e.g. `Array.prototype.forEach`). Using a single string makes it easier to match.
  Const(Const),
  Fn(usize), // The value is a function index. Functions are immutable so are similar to Const rather than an inst to load it.
  Var(u32),
}

impl Arg {
  pub fn maybe_var(&self) -> Option<u32> {
    match self {
      Arg::Var(n) => Some(*n),
      _ => None,
    }
  }

  pub fn to_var(&self) -> u32 {
    self
      .maybe_var()
      .expect("not a variable")
  }

  pub fn to_const(&self) -> Const {
    match self {
      Arg::Const(c) => c.clone(),
      _ => panic!("not a constant"),
    }
  }
}

impl Debug for Arg {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      Self::Builtin(p) => write!(f, "{p}"),
      Self::Const(v) => write!(f, "{v:?}"),
      Self::Fn(n) => write!(f, "Fn{n}"),
      Self::Var(n) => write!(f, "%{n}"),
    }
  }
}

/// These must all be pure; impure operations (e.g. prop assign) are separate insts.
#[derive(PartialEq, Eq, Hash, Clone, Copy, Serialize)]
pub enum BinOp {
  Add,
  Div, // Divide.
  Exp, // Exponentiate.
  Geq, // Greater than or equals to.
  GetProp,
  Gt,  // Greater than.
  Leq, // Less than or equals to.
  LooseEq,
  Lt,  // Less than.
  Mod, // Modulo.
  Mul, // Multiply.
  NotLooseEq,
  NotStrictEq,
  StrictEq,
  Sub, // Subtract.
  _Dummy,
}

impl Debug for BinOp {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      Self::Add => write!(f, "+"),
      Self::Div => write!(f, "/"),
      Self::Exp => write!(f, "**"),
      Self::Geq => write!(f, ">="),
      Self::GetProp => write!(f, "."),
      Self::Gt => write!(f, ">"),
      Self::Leq => write!(f, "<="),
      Self::LooseEq => write!(f, "=="),
      Self::Lt => write!(f, "<"),
      Self::Mod => write!(f, "%"),
      Self::Mul => write!(f, "*"),
      Self::NotLooseEq => write!(f, "!="),
      Self::NotStrictEq => write!(f, "!=="),
      Self::StrictEq => write!(f, "==="),
      Self::Sub => write!(f, "-"),
      Self::_Dummy => write!(f, "_DUMMY"),
    }
  }
}

/// These must all be pure; impure operations (e.g. prop assign) are separate insts.
#[derive(PartialEq, Eq, Hash, Clone, Copy, Serialize)]
pub enum UnOp {
  Neg,
  Not,
  Plus,
  Typeof,
  Void,
  _Dummy,
}

impl Debug for UnOp {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      Self::Neg => write!(f, "-"),
      Self::Not => write!(f, "!"),
      Self::Plus => write!(f, "+"),
      Self::Typeof => write!(f, "typeof"),
      Self::Void => write!(f, "void"),
      Self::_Dummy => write!(f, "_DUMMY"),
    }
  }
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub enum InstTyp {
  Bin, // tgts[0] = args[0] bin_op args[1]
  Un, // tgts[0] = un_op args[0]
  VarAssign, // tgts[0] = args[0]
  PropAssign, // args[0][args[1]] = args[2]
  CondGoto, // goto labels[0] if args[0] else labels[1]
  Call, // tgts.at(0)? = args[0](this=args[1], ...args[2..])
  // A foreign variable is one in an ancestor scope, all the way up to and including the global scope.
  // We don't simply add another Target variant (e.g. Target::Foreign) as it makes analyses and optimisations more tedious. Consider that standard SSA doesn't really have a concept of nonlocal memory locations. In LLVM such vars are covered using ordinary memory location read/write instructions.
  // NOTE: It still violates SSA if we only have ForeignStore but not ForeignLoad (and instead use another enum variant for Arg). Consider: `%a0 = foreign(3); %a1 = %a0 + 42; foreign(3) = %a1; %a2 = foreign(3);` but `%a0` and `%a2` are not identical.
  ForeignLoad, // tgts[0] = foreign
  ForeignStore, // foreign = args[0]
  UnknownLoad, // tgts[0] = unknown
  UnknownStore,  // unknown = args[0]
  // Pick one assigned value of `tgt` from one of these blocks. Due to const propagation, input targets could be transformed to const values, which is why we have `Arg` and not just `Target`.
  Phi, // tgts[0] = ϕ{labels[0]: args[0], labels[1]: args[1], ...}
  // No-op marker for a position in Vec<Inst> during source_to_inst. We can't just use indices as we may reorder and splice the instructions during optimisations.
  _Label, // labels[0]
  // We only want these during source_to_inst. Afterwards, refer to the graph children; otherwise, it's two separate things we have to keep in sync and check.
  _Goto, // labels[0]
  _Dummy,
}

fn is_dummy_binop(op: &BinOp) -> bool {
  matches!(op, BinOp::_Dummy)
}

fn is_dummy_unop(op: &UnOp) -> bool {
  matches!(op, UnOp::_Dummy)
}

fn is_dummy_symbol(sym: &Symbol) -> bool {
  sym.raw_id() == u64::MAX
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct Inst {
  pub t: InstTyp,
  pub tgts: Vec<u32>,
  pub args: Vec<Arg>,
  pub spreads: Vec<usize>, // Indices into `args` that are spread, for Call. Cannot have values less than 2 as the first two args are `callee` and `this`.
  pub labels: Vec<u32>,
  // Garbage values if not applicable.
  #[serde(default = "BinOp::_Unreachable", skip_serializing_if = "is_dummy_binop")]
  pub bin_op: BinOp,
  #[serde(default = "UnOp::_Unreachable", skip_serializing_if = "is_dummy_unop")]
  pub un_op: UnOp,
  #[serde(default = "Symbol::from_raw_id_max", skip_serializing_if = "is_dummy_symbol")]
  pub foreign: Symbol,
  #[serde(default, skip_serializing_if = "String::is_empty")]
  pub unknown: String,
}

impl Inst {
  pub fn remove_phi(&mut self, label: u32) -> Option<Arg> {
    assert!(self.t == InstTyp::Phi);
    assert_eq!(self.labels.len(), self.args.len());
    let i = self.labels.iter().position(|&l| l == label)?;
    self.labels.remove(i);
    Some(self.args.remove(i))
  }

  pub fn insert_phi(&mut self, label: u32, arg: Arg) {
    assert!(self.t == InstTyp::Phi);
    assert_eq!(self.labels.len(), self.args.len());
    // This catches a lot of bugs.
    assert!(!self.labels.contains(&label), "can't insert {label}=>{arg:?} to {self:?}");
    self.labels.push(label);
    self.args.push(arg);
  }
}

impl Default for Inst {
  fn default() -> Self {
    Self {
      t: InstTyp::_Dummy,
      tgts: Default::default(),
      args: Default::default(),
      spreads: Default::default(),
      labels: Default::default(),
      bin_op: BinOp::_Dummy,
      un_op: UnOp::_Dummy,
      foreign: Symbol::from_raw_id(u64::MAX),
      unknown: Default::default(),
    }
  }
}

/// Convenient builders for Inst.
impl Inst {
  pub fn bin(tgt: u32, left: Arg, op: BinOp, right: Arg) -> Self {
    Self {
      t: InstTyp::Bin,
      tgts: vec![tgt],
      args: vec![left, right],
      bin_op: op,
      ..Default::default()
    }
  }

  pub fn un(tgt: u32, op: UnOp, arg: Arg) -> Self {
    Self {
      t: InstTyp::Un,
      tgts: vec![tgt],
      args: vec![arg],
      un_op: op,
      ..Default::default()
    }
  }

  pub fn var_assign(tgt: u32, arg: Arg) -> Self {
    Self {
      t: InstTyp::VarAssign,
      tgts: vec![tgt],
      args: vec![arg],
      ..Default::default()
    }
  }

  pub fn prop_assign(obj: Arg, prop: Arg, val: Arg) -> Self {
    Self {
      t: InstTyp::PropAssign,
      args: vec![obj, prop, val],
      ..Default::default()
    }
  }

  pub fn goto(label: u32) -> Self {
    Self {
      t: InstTyp::_Goto,
      labels: vec![label],
      ..Default::default()
    }
  }

  pub fn cond_goto(cond: Arg, t: u32, f: u32) -> Self {
    Self {
      t: InstTyp::CondGoto,
      args: vec![cond],
      labels: vec![t, f],
      ..Default::default()
    }
  }

  pub fn call(tgt: impl Into<Option<u32>>, callee: Arg, this: Arg, args: Vec<Arg>, spreads: Vec<usize>) -> Self {
    assert!(spreads.iter().all(|&i| i >= 2 && i < args.len()));
    Self {
      t: InstTyp::Call,
      tgts: tgt.into().into_iter().collect(),
      args: [callee, this].into_iter().chain(args).collect(),
      spreads,
      ..Default::default()
    }
  }

  pub fn foreign_load(tgt: u32, foreign: Symbol) -> Self {
    Self {
      t: InstTyp::ForeignLoad,
      tgts: vec![tgt],
      foreign,
      ..Default::default()
    }
  }

  pub fn foreign_store(foreign: Symbol, arg: Arg) -> Self {
    Self {
      t: InstTyp::ForeignStore,
      args: vec![arg],
      foreign,
      ..Default::default()
    }
  }

  pub fn unknown_load(tgt: u32, unknown: String) -> Self {
    Self {
      t: InstTyp::UnknownLoad,
      tgts: vec![tgt],
      unknown,
      ..Default::default()
    }
  }

  pub fn unknown_store(unknown: String, arg: Arg) -> Self {
    Self {
      t: InstTyp::UnknownStore,
      args: vec![arg],
      unknown,
      ..Default::default()
    }
  }

  /// Use .insert_phi() to add more labels and args.
  pub fn phi_empty(tgt: u32) -> Self {
    Self {
      t: InstTyp::Phi,
      tgts: vec![tgt],
      ..Default::default()
    }
  }

  pub fn label(label: u32) -> Self {
    Self {
      t: InstTyp::_Label,
      labels: vec![label],
      ..Default::default()
    }
  }
}

/// Convenient component getters for Inst.
impl Inst {
  pub fn as_bin(&self) -> (u32, &Arg, BinOp, &Arg) {
    assert_eq!(self.t, InstTyp::Bin);
    (self.tgts[0], &self.args[0], self.bin_op, &self.args[1])
  }

  pub fn as_un(&self) -> (u32, UnOp, &Arg) {
    assert_eq!(self.t, InstTyp::Un);
    (self.tgts[0], self.un_op, &self.args[0])
  }

  pub fn as_var_assign(&self) -> (u32, &Arg) {
    assert_eq!(self.t, InstTyp::VarAssign);
    (self.tgts[0], &self.args[0])
  }

  pub fn as_prop_assign(&self) -> (&Arg, &Arg, &Arg) {
    assert_eq!(self.t, InstTyp::PropAssign);
    (&self.args[0], &self.args[1], &self.args[2])
  }

  pub fn as_cond_goto(&self) -> (&Arg, u32, u32) {
    assert_eq!(self.t, InstTyp::CondGoto);
    (&self.args[0], self.labels[0], self.labels[1])
  }

  pub fn as_call(&self) -> (Option<u32>, &Arg, &Arg, &[Arg], &[usize]) {
    assert_eq!(self.t, InstTyp::Call);
    (self.tgts.get(0).copied(), &self.args[0], &self.args[1], &self.args[2..], &self.spreads)
  }

  pub fn as_foreign_load(&self) -> (u32, Symbol) {
    assert_eq!(self.t, InstTyp::ForeignLoad);
    (self.tgts[0], self.foreign)
  }

  pub fn as_foreign_store(&self) -> (Symbol, &Arg) {
    assert_eq!(self.t, InstTyp::ForeignStore);
    (self.foreign, &self.args[0])
  }

  pub fn as_unknown_load(&self) -> (u32, &String) {
    assert_eq!(self.t, InstTyp::UnknownLoad);
    (self.tgts[0], &self.unknown)
  }

  pub fn as_unknown_store(&self) -> (&String, &Arg) {
    assert_eq!(self.t, InstTyp::UnknownStore);
    (&self.unknown, &self.args[0])
  }
}
