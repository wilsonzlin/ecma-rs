//! Resumable body evaluation for generators and async functions.
//!
//! Architecture: a step interpreter ("frame machine") used ONLY for function bodies that can
//! suspend (`function*`, `async function`). Normal functions keep the fast recursive path in
//! `exec.rs`.
//!
//! Design contract (see wiki/crates/vm-js.md § Design):
//! - A suspended activation is an explicit heap value: `ResumableBody` = a stack of `Frame`s plus
//!   the environment/`this` snapshot. It lives inside the generator heap object and is traced by
//!   the GC like any other host data (all held `Value`s / `GcEnv`s / iterator records are traced).
//! - Driving is a loop: `step()` inspects the top frame under a short `RefCell` borrow and
//!   returns either a pure state transition or an `Action`; the driver performs actions (which
//!   may allocate, run user code, or recurse into the normal evaluator) with NO borrow held, and
//!   feeds the result back as `Feedback`. GC can therefore always trace the body: no borrow is
//!   ever held across an allocation point. A conflicting borrow would panic loudly (RefCell),
//!   never corrupt.
//! - Suspend-free subtrees (no `yield`/`await` outside nested function boundaries) are delegated
//!   wholesale to the recursive evaluator (`Action::EvalExpr` / `Action::EvalStmt`); frames exist
//!   only along the "spine" from the body root to each suspension point.
//! - Suspension points are supported in the common expression positions (expression statements,
//!   variable initializers, assignment RHS, call arguments, binary/logical/conditional operands,
//!   array literals (incl. `...` spread / IteratorSpread), object literals (incl. object spread),
//!   computed members / optional `?.[…]` chains, return/throw operands). Exotic hosts
//!   (template literals, `new`, call/new argument spread, destructuring targets, switch/for-in
//!   bodies) report `VmError::Unimplemented` — a precise, documented boundary rather than silently
//!   wrong semantics. `with` is supported (Object Environment + `@@unscopables`).

use std::cell::RefCell;
use std::ptr::NonNull;
use std::rc::Rc;

use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMemberType};
use parse_js::ast::expr::lit::{LitArrElem, LitArrExpr, LitObjExpr, LitTemplatePart};
use parse_js::ast::expr::{BinaryExpr, CallExpr, ComputedMemberExpr, CondExpr, Expr};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{VarDecl, VarDeclMode};
use parse_js::ast::stmt::{
  CatchBlock, DoWhileStmt, ForOfStmt, ForTripleStmt, ForTripleStmtInit, IfStmt, ReturnStmt, Stmt,
  ThrowStmt, TryStmt, WhileStmt, WithStmt,
};
use parse_js::operator::OperatorName;

use crate::error::VmError;
use crate::exec::{Completion, Evaluator, OwnedReference};
use crate::handle::{GcEnv, GcObject};
use crate::heap::Scope;
use crate::heap::{Trace, Tracer};
use crate::iterator::IteratorRecord;
use crate::value::Value;

// ---------------------------------------------------------------------------
// AST references
// ---------------------------------------------------------------------------

/// A raw pointer to a node inside a retained AST (`Arc<ParsedProgram>`).
///
/// Safety: the owning `ResumableBody` holds the `Arc<ParsedProgram>`, and ASTs are immutable
/// after parse, so the pointee outlives this reference and never moves.
pub(crate) struct NodeRef<T: derive_visitor::Drive + derive_visitor::DriveMut>(NonNull<Node<T>>);

impl<T: derive_visitor::Drive + derive_visitor::DriveMut> NodeRef<T> {
  pub(crate) fn new(node: &Node<T>) -> Self {
    Self(NonNull::from(node))
  }

  pub(crate) fn get(&self) -> &Node<T> {
    // SAFETY: see type-level comment.
    unsafe { self.0.as_ref() }
  }
}

impl<T: derive_visitor::Drive + derive_visitor::DriveMut> Clone for NodeRef<T> {
  fn clone(&self) -> Self {
    *self
  }
}
impl<T: derive_visitor::Drive + derive_visitor::DriveMut> Copy for NodeRef<T> {}

/// A raw pointer to a node list inside a retained AST (e.g. a statement list).
pub(crate) struct ListRef<T: derive_visitor::Drive + derive_visitor::DriveMut>(NonNull<[Node<T>]>);

impl<T: derive_visitor::Drive + derive_visitor::DriveMut> ListRef<T> {
  pub(crate) fn new(list: &[Node<T>]) -> Self {
    Self(NonNull::from(list))
  }

  pub(crate) fn get(&self) -> &[Node<T>] {
    // SAFETY: see NodeRef.
    unsafe { self.0.as_ref() }
  }
}

impl<T: derive_visitor::Drive + derive_visitor::DriveMut> Clone for ListRef<T> {
  fn clone(&self) -> Self {
    *self
  }
}
impl<T: derive_visitor::Drive + derive_visitor::DriveMut> Copy for ListRef<T> {}

// ---------------------------------------------------------------------------
// Suspension protocol
// ---------------------------------------------------------------------------

/// Why a drive returned without completing.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum SuspendKind {
  /// `yield v`: v is handed to the caller of `next()` as the iterator result value.
  Yield,
  /// `await v`: v is the awaited value; the async driver arranges resumption.
  Await,
}

/// Result of driving a resumable body.
pub(crate) enum DriveOutcome {
  Suspended(SuspendKind, Value),
  Completed(Completion),
}

/// Values injected into the frame machine: results of performed actions, sub-evaluation results,
/// and resume injections from `next(v)` / `throw(v)` / `return(v)`.
pub(crate) enum Feedback {
  /// Initial entry of a freshly pushed frame (or of the whole body).
  Start,
  /// An expression value.
  Value(Value),
  /// A statement completion or an abrupt signal (throw/return injection, JS exception from an
  /// action).
  Completion(Completion),
  /// Result of `Action::ResolveTarget`.
  Reference(OwnedReference),
  /// Result of `Action::EvalCallee`.
  Callee { func: Value, this: Value },
  /// Result of `Action::GetIterator`.
  Iterator(IteratorRecord),
  /// Result of `Action::IterStepValue`: updated record + next value (None = done).
  IterStep(IteratorRecord, Option<Value>),
  /// Result of `Action::IterResultParts`.
  IterParts(Value, bool),
  /// Result of env-entering actions: the PREVIOUS lexical env (to restore later).
  Env(Option<GcEnv>),
  /// A fresh array-literal object.
  Array(GcObject),
  /// A fresh object-literal object.
  Object(GcObject),
  /// Result of `Action::GetMethod` (callable or Undefined).
  Method(Value),
  /// Optional-chain short-circuit (§13.3.9): remaining links must not evaluate.
  ShortCircuit,
  /// Acknowledgement of an effect-only action.
  Done,
}

/// Effects requested by `step()`; performed by the driver with no body borrow held.
pub(crate) enum Action {
  /// Evaluate a suspend-free expression via the recursive evaluator.
  EvalExpr(NodeRef<Expr>),
  /// Evaluate a suspend-free optional-chain spine, preserving short-circuit as
  /// `Feedback::ShortCircuit` (unlike `EvalExpr`, which collapses it to `undefined`).
  EvalChain(NodeRef<Expr>),
  /// Evaluate a suspend-free statement via the recursive evaluator (with label set).
  EvalStmt(NodeRef<Stmt>, Vec<String>),
  /// Evaluate a suspend-free `var`/`let`/`const` declaration via the recursive evaluator.
  EvalVarDecl(NodeRef<VarDecl>),
  /// Create a block env (child of current), instantiate the list's lexical declarations in it,
  /// and switch to it. Feedback: previous env.
  EnterBlockEnv(ListRef<Stmt>),
  /// Create a plain child env and switch to it (for-loop init decl scope). Feedback: prev env.
  EnterPlainEnv,
  BinaryOp(OperatorName, Value, Value),
  /// `#PrivateIdentifier in rhs` after the RHS value is known.
  PrivateIn(NodeRef<BinaryExpr>, Value),
  UnaryOp(OperatorName, Value),
  /// Resolve a simple assignment target (id/member/computed) to a reference.
  ResolveTarget(NodeRef<Expr>),
  LoadReference(OwnedReference),
  /// Write through a reference. Feedback: the stored value.
  StoreReference(OwnedReference, Value),
  /// Evaluate a call callee, producing (function, this).
  EvalCallee(NodeRef<Expr>),
  Call {
    func: Value,
    this: Value,
    args: Vec<Value>,
  },
  GetIterator(Value),
  /// GetIterator with async hint (`@@asyncIterator`).
  GetAsyncIterator(Value),
  IterStepValue(IteratorRecord),
  /// Call `iterator.next()` (protocol path); Feedback: Value (possibly a Promise).
  IteratorNext(IteratorRecord),
  /// IteratorClose (errors swallowed; used on abrupt paths). Feedback: Done.
  IterClose(IteratorRecord),
  /// Extract (value, done) from an iterator result object (yield* protocol).
  IterResultParts(Value),
  /// Bind a for-of LHS (decl → fresh per-iteration env; assignment → in place).
  /// Feedback: previous env when a per-iteration env was created.
  BindForOfLhs(NodeRef<ForOfStmt>, Value),
  /// Enter catch scope and bind the catch parameter. Feedback: previous env.
  EnterCatch(NodeRef<CatchBlock>, Value),
  /// Bind declarator `idx` of the declaration to a value. Feedback: Done.
  BindDeclarator(NodeRef<VarDecl>, usize, Value),
  /// Allocate an empty array-literal object. Feedback: Array.
  ArrayNew,
  /// CreateDataProperty(arr, idx, value). Feedback: Done.
  ArrayDefine(GcObject, u32, Value),
  /// Set final `length`. Feedback: Done.
  ArrayFinalize(GcObject, u32),
  /// Allocate an empty object-literal object. Feedback: Object.
  ObjectNew,
  /// Apply one suspend-free object-literal member onto `obj`. Feedback: Done.
  ObjectApplyMember(GcObject, NodeRef<LitObjExpr>, usize),
  /// CreateDataProperty(obj, ToPropertyKey(key), value). Feedback: Done.
  ObjectDefine(GcObject, Value, Value),
  /// CreateDataProperty with a Direct (non-computed) key from member `idx`. Feedback: Done.
  ObjectDefineDirect(GcObject, NodeRef<LitObjExpr>, usize, Value),
  /// CopyDataProperties-style object spread onto `obj`. Feedback: Done.
  ObjectSpread(GcObject, Value),
  /// GetV(base, ToPropertyKey(key)). Feedback: Value.
  GetComputed(Value, Value),
  /// GetMethod(obj, name); Undefined when absent. Feedback: Method.
  GetMethod(Value, &'static str),
  /// Throw a TypeError (feeds back as Completion::Throw via the driver's error handling).
  ThrowTypeError(&'static str),
  /// `ToObject` + NewObjectEnvironment(withEnvironment=true). Feedback: previous env.
  EnterWithEnv(Value),
}

// ---------------------------------------------------------------------------
// Frames
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum LoopPhase {
  Cond,
  Body,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum ForTriplePhase {
  /// Running the init clause (expr or var decl; possibly preceded by EnterPlainEnv).
  Init,
  /// Waiting for the condition value.
  Cond,
  /// Waiting for the body completion.
  Body,
  /// Waiting for the update expression value.
  Post,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum ForOfPhase {
  Rhs,
  GetIter,
  /// Sync: waiting for IterStepValue. Async: waiting for `next()` call result (a Promise).
  Next,
  /// Async only: resumed after awaiting the `next()` promise; value is the iter result object.
  AwaitNext,
  Bind,
  Body,
  /// Closing the iterator after an abrupt exit; then re-emit `pending`.
  Closing,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum TryPhase {
  Block,
  CatchEnter,
  Catch,
  Finally,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum WithPhase {
  /// Waiting for the object expression value.
  Object,
  /// Waiting for the body completion (object env already installed).
  Body,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum YieldStarPhase {
  /// Waiting for the iterable operand value.
  Operand,
  /// Waiting for GetIterator.
  GetIter,
  /// Waiting for an engine fast-path iterator step (array records without a reified `next`).
  FastStep,
  /// Waiting for the result of an inner next/throw call.
  AwaitResult,
  /// Waiting for IterResultParts of an inner next/throw result.
  AwaitParts,
  /// Suspended: the last inner value was yielded outward; resume routes here.
  Forwarding,
  /// Waiting for GetMethod(iterator, "throw").
  AwaitThrowMethod,
  /// Waiting for GetMethod(iterator, "return").
  AwaitReturnMethod,
  /// Waiting for IterClose after a missing `throw` method; then TypeError.
  CloseThenTypeError,
  /// Waiting for the result of an inner `return` call.
  AwaitReturnResult,
  /// Waiting for IterResultParts of an inner `return` result.
  AwaitReturnParts,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum BinPhase {
  Left,
  Right,
  /// Assignment: waiting for the resolved target reference.
  Target,
  /// Assignment: waiting for the target's current value (compound / logical assignment).
  Load,
  /// Compound assignment: waiting for the operator application; then store.
  Apply,
  /// Assignment: waiting for the store acknowledgement.
  Store,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum CallPhase {
  Callee,
  Args,
  Invoke,
}

/// Phases for array-literal evaluation, including IteratorSpread of Rest elements.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum ArrayLitPhase {
  /// Creating the array / advancing across elements.
  Elements,
  /// Waiting for a `Single` element's value.
  Single,
  /// Waiting for a Rest element's iterable source value.
  SpreadSource,
  /// Waiting for `GetIterator` of the spread source.
  SpreadGetIter,
  /// Waiting for the next `IteratorStepValue` during spread.
  SpreadStep,
}

/// Phases for object-literal evaluation, including object spread (`...expr`).
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum ObjectLitPhase {
  /// Creating the object / advancing across members.
  Members,
  /// Waiting for a computed property key.
  PropKey,
  /// Waiting for a property value (Direct key already known via member index).
  PropValueDirect,
  /// Waiting for a property value after a computed key.
  PropValueComputed,
  /// Waiting for an object-spread source value.
  SpreadSource,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum ComputedMemberPhase {
  Object,
  Key,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum VarDeclPhase {
  NextDecl,
  Init,
  Bound,
}

/// One suspended activation record element.
pub(crate) enum Frame {
  /// A statement list (function body, block body, loop body, catch body).
  /// `needs_env` lists own a block lexical environment (created on Start, restored on exit).
  StmtList {
    list: ListRef<Stmt>,
    idx: usize,
    last: Option<Value>,
    needs_env: bool,
    restore_env: Option<GcEnv>,
  },
  ExprStmt {
    node: NodeRef<parse_js::ast::stmt::ExprStmt>,
    started: bool,
  },
  If {
    node: NodeRef<IfStmt>,
    started: bool,
  },
  While {
    node: NodeRef<WhileStmt>,
    labels: Vec<String>,
    phase: LoopPhase,
    v: Option<Value>,
  },
  DoWhile {
    node: NodeRef<DoWhileStmt>,
    labels: Vec<String>,
    phase: LoopPhase,
    v: Option<Value>,
  },
  ForTriple {
    node: NodeRef<ForTripleStmt>,
    labels: Vec<String>,
    phase: ForTriplePhase,
    v: Option<Value>,
    restore_env: Option<GcEnv>,
    init_done: bool,
    /// BoundNames of a `let`/`const` for-head (for CreatePerIterationEnvironment).
    per_iteration_names: Vec<String>,
  },
  ForOf {
    node: NodeRef<ForOfStmt>,
    labels: Vec<String>,
    phase: ForOfPhase,
    record: Option<IteratorRecord>,
    v: Option<Value>,
    /// Env to restore after each iteration body (per-iteration decl env).
    iter_restore: Option<GcEnv>,
    /// Completion to re-emit after Closing.
    pending: Option<Completion>,
  },
  Try {
    node: NodeRef<TryStmt>,
    phase: TryPhase,
    /// Completion to re-emit after the finally block completes normally.
    resume: Option<Completion>,
    /// Env to restore when leaving the catch block.
    catch_restore: Option<GcEnv>,
  },
  Label {
    name: String,
    node: NodeRef<parse_js::ast::stmt::LabelStmt>,
    labels: Vec<String>,
    started: bool,
  },
  With {
    node: NodeRef<WithStmt>,
    phase: WithPhase,
    restore_env: Option<GcEnv>,
  },
  Return {
    node: NodeRef<ReturnStmt>,
    started: bool,
  },
  /// Expression-bodied arrow (`async x => expr`): evaluate and return the value.
  ImplicitReturn {
    operand: NodeRef<Expr>,
    started: bool,
  },
  Throw {
    node: NodeRef<ThrowStmt>,
    started: bool,
  },
  VarDecl {
    node: NodeRef<VarDecl>,
    idx: usize,
    phase: VarDeclPhase,
  },
  // --- expressions ---
  /// `yield e`: operand value arrives → pop self → suspend. Resume feedback reaches the parent.
  Yield {
    operand: NodeRef<Expr>,
    started: bool,
  },
  Await {
    operand: NodeRef<Expr>,
    started: bool,
  },
  YieldStar {
    operand: NodeRef<Expr>,
    phase: YieldStarPhase,
    record: Option<IteratorRecord>,
    /// Injected completion being routed to the inner iterator (throw/return).
    sent: Option<Completion>,
  },
  Unary {
    op: OperatorName,
    operand: NodeRef<Expr>,
    started: bool,
  },
  Binary {
    node: NodeRef<BinaryExpr>,
    phase: BinPhase,
    left: Option<Value>,
    target: Option<OwnedReference>,
  },
  Cond {
    node: NodeRef<CondExpr>,
    started: bool,
  },
  Call {
    node: NodeRef<CallExpr>,
    phase: CallPhase,
    func: Value,
    this: Value,
    args: Vec<Value>,
    arg_idx: usize,
  },
  ArrayLit {
    node: NodeRef<LitArrExpr>,
    elem_idx: usize,
    arr: Option<GcObject>,
    next_index: u32,
    /// Set when finalize has been requested; the next Done pops the frame.
    finalizing: bool,
    phase: ArrayLitPhase,
    /// Iterator record while expanding a Rest element (IteratorSpread).
    spread_record: Option<IteratorRecord>,
  },
  ObjectLit {
    node: NodeRef<LitObjExpr>,
    member_idx: usize,
    obj: Option<GcObject>,
    phase: ObjectLitPhase,
    /// Computed key value while waiting for the property value.
    pending_key: Option<Value>,
  },
  ComputedMember {
    node: NodeRef<ComputedMemberExpr>,
    phase: ComputedMemberPhase,
    object: Option<Value>,
  },
}

impl Trace for Frame {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    match self {
      Frame::StmtList {
        last, restore_env, ..
      } => {
        if let Some(v) = last {
          tracer.trace_value(*v);
        }
        if let Some(e) = restore_env {
          tracer.trace_env(*e);
        }
      }
      Frame::ExprStmt { .. }
      | Frame::If { .. }
      | Frame::Return { .. }
      | Frame::ImplicitReturn { .. }
      | Frame::Throw { .. }
      | Frame::VarDecl { .. }
      | Frame::Yield { .. }
      | Frame::Await { .. }
      | Frame::Unary { .. }
      | Frame::Cond { .. } => {}
      Frame::Label { .. } => {}
      Frame::With { restore_env, .. } => {
        if let Some(e) = restore_env {
          tracer.trace_env(*e);
        }
      }
      Frame::While { v, .. } | Frame::DoWhile { v, .. } => {
        if let Some(v) = v {
          tracer.trace_value(*v);
        }
      }
      Frame::ForTriple { v, restore_env, .. } => {
        if let Some(v) = v {
          tracer.trace_value(*v);
        }
        if let Some(e) = restore_env {
          tracer.trace_env(*e);
        }
      }
      Frame::ForOf {
        record,
        v,
        iter_restore,
        pending,
        ..
      } => {
        if let Some(r) = record {
          trace_iterator_record(r, tracer);
        }
        if let Some(v) = v {
          tracer.trace_value(*v);
        }
        if let Some(e) = iter_restore {
          tracer.trace_env(*e);
        }
        if let Some(c) = pending {
          trace_completion(c, tracer);
        }
      }
      Frame::Try {
        resume,
        catch_restore,
        ..
      } => {
        if let Some(c) = resume {
          trace_completion(c, tracer);
        }
        if let Some(e) = catch_restore {
          tracer.trace_env(*e);
        }
      }
      Frame::YieldStar { record, sent, .. } => {
        if let Some(r) = record {
          trace_iterator_record(r, tracer);
        }
        if let Some(c) = sent {
          trace_completion(c, tracer);
        }
      }
      Frame::Binary { left, target, .. } => {
        if let Some(v) = left {
          tracer.trace_value(*v);
        }
        if let Some(t) = target {
          t.trace(tracer);
        }
      }
      Frame::Call {
        func, this, args, ..
      } => {
        tracer.trace_value(*func);
        tracer.trace_value(*this);
        for a in args {
          tracer.trace_value(*a);
        }
      }
      Frame::ArrayLit {
        arr, spread_record, ..
      } => {
        if let Some(a) = arr {
          tracer.trace_value(Value::Object(*a));
        }
        if let Some(r) = spread_record {
          trace_iterator_record(r, tracer);
        }
      }
      Frame::ObjectLit {
        obj, pending_key, ..
      } => {
        if let Some(o) = obj {
          tracer.trace_value(Value::Object(*o));
        }
        if let Some(k) = pending_key {
          tracer.trace_value(*k);
        }
      }
      Frame::ComputedMember { object, .. } => {
        if let Some(o) = object {
          tracer.trace_value(*o);
        }
      }
    }
  }
}

pub(crate) fn trace_completion(c: &Completion, tracer: &mut Tracer<'_>) {
  match c {
    Completion::Normal(v) => {
      if let Some(v) = v {
        tracer.trace_value(*v);
      }
    }
    Completion::Throw(t) => tracer.trace_value(t.value),
    Completion::Return(v) => tracer.trace_value(*v),
    Completion::Break(_, v) | Completion::Continue(_, v) => {
      if let Some(v) = v {
        tracer.trace_value(*v);
      }
    }
  }
}

pub(crate) fn trace_iterator_record(r: &IteratorRecord, tracer: &mut Tracer<'_>) {
  tracer.trace_value(r.iterator);
  tracer.trace_value(r.next_method);
}

// ---------------------------------------------------------------------------
// ResumableBody
// ---------------------------------------------------------------------------

/// The heap-resident suspended state of a generator / async function activation.
pub(crate) struct ResumableBody {
  /// Suspended activation records; the creator pre-pushes the initial frame
  /// (`Frame::StmtList` for block bodies, `Frame::ImplicitReturn` for expression bodies).
  pub(crate) frames: Vec<Frame>,
  /// Environments captured at call time (FunctionDeclarationInstantiation already ran).
  /// `lexical_env` is updated at every suspension to the env current at the yield point.
  pub(crate) lexical_env: GcEnv,
  pub(crate) var_env: GcEnv,
  pub(crate) global: GcObject,
  pub(crate) this: Value,
  pub(crate) strict: bool,
  /// Keeps the retained AST (and thus all NodeRef/ListRef pointees) alive.
  #[allow(dead_code)]
  pub(crate) program: std::sync::Arc<crate::vm::ParsedProgram>,
  /// Source text for stack traces on resume.
  pub(crate) source: std::sync::Arc<crate::source::SourceText>,
}

impl Trace for ResumableBody {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    for f in &self.frames {
      f.trace(tracer);
    }
    tracer.trace_env(self.lexical_env);
    tracer.trace_env(self.var_env);
    tracer.trace_value(Value::Object(self.global));
    tracer.trace_value(self.this);
  }
}

// ---------------------------------------------------------------------------
// Suspend-point scanning
// ---------------------------------------------------------------------------

/// True if evaluating `expr` may hit a `yield`/`await` belonging to THIS function (nested
/// function/arrow/class-member bodies are boundaries and excluded).
pub(crate) fn expr_contains_suspend(expr: &Node<Expr>) -> bool {
  scan_expr(&expr.stx)
}

pub(crate) fn stmt_contains_suspend(stmt: &Node<Stmt>) -> bool {
  scan_stmt(&stmt.stx)
}

fn scan_expr(e: &Expr) -> bool {
  match e {
    Expr::Unary(u) => match u.stx.operator {
      OperatorName::Yield | OperatorName::YieldDelegated | OperatorName::Await => true,
      _ => scan_expr(&u.stx.argument.stx),
    },
    Expr::UnaryPostfix(u) => scan_expr(&u.stx.argument.stx),
    Expr::Binary(b) => scan_expr(&b.stx.left.stx) || scan_expr(&b.stx.right.stx),
    Expr::Cond(c) => {
      scan_expr(&c.stx.test.stx)
        || scan_expr(&c.stx.consequent.stx)
        || scan_expr(&c.stx.alternate.stx)
    }
    Expr::Call(c) => {
      scan_expr(&c.stx.callee.stx) || c.stx.arguments.iter().any(|a| scan_expr(&a.stx.value.stx))
    }
    Expr::Member(m) => scan_expr(&m.stx.left.stx),
    Expr::ComputedMember(m) => scan_expr(&m.stx.object.stx) || scan_expr(&m.stx.member.stx),
    Expr::LitArr(a) => a.stx.elements.iter().any(|el| match el {
      LitArrElem::Single(e) | LitArrElem::Rest(e) => scan_expr(&e.stx),
      LitArrElem::Empty => false,
    }),
    Expr::LitObj(o) => o.stx.members.iter().any(|m| {
      use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMemberType};
      match &m.stx.typ {
        ObjMemberType::Valued { key, val } => {
          let key_susp = match key {
            ClassOrObjKey::Computed(e) => scan_expr(&e.stx),
            ClassOrObjKey::Direct(_) => false,
          };
          let val_susp = match val {
            ClassOrObjVal::Prop(Some(e)) => scan_expr(&e.stx),
            // Getter/setter/method bodies are function boundaries.
            _ => false,
          };
          key_susp || val_susp
        }
        ObjMemberType::Shorthand { .. } => false,
        ObjMemberType::Rest { val } => scan_expr(&val.stx),
      }
    }),
    Expr::LitTemplate(t) => t.stx.parts.iter().any(|p| match p {
      LitTemplatePart::Substitution(e) => scan_expr(&e.stx),
      LitTemplatePart::String(_) => false,
    }),
    Expr::TaggedTemplate(t) => {
      scan_expr(&t.stx.function.stx)
        || t.stx.parts.iter().any(|p| match p {
          LitTemplatePart::Substitution(e) => scan_expr(&e.stx),
          LitTemplatePart::String(_) => false,
        })
    }
    // Function boundaries.
    Expr::Func(_) | Expr::ArrowFunc(_) | Expr::Class(_) => false,
    _ => false,
  }
}

fn scan_stmt(s: &Stmt) -> bool {
  match s {
    Stmt::Block(b) => b.stx.body.iter().any(stmt_contains_suspend),
    Stmt::Expr(e) => scan_expr(&e.stx.expr.stx),
    Stmt::If(i) => {
      scan_expr(&i.stx.test.stx)
        || scan_stmt(&i.stx.consequent.stx)
        || i.stx.alternate.as_ref().is_some_and(|a| scan_stmt(&a.stx))
    }
    Stmt::While(w) => scan_expr(&w.stx.condition.stx) || scan_stmt(&w.stx.body.stx),
    Stmt::DoWhile(d) => scan_expr(&d.stx.condition.stx) || scan_stmt(&d.stx.body.stx),
    Stmt::ForTriple(f) => {
      let init = match &f.stx.init {
        ForTripleStmtInit::None => false,
        ForTripleStmtInit::Expr(e) => scan_expr(&e.stx),
        ForTripleStmtInit::Decl(d) => var_decl_contains_suspend(&d.stx),
      };
      init
        || f.stx.cond.as_ref().is_some_and(|e| scan_expr(&e.stx))
        || f.stx.post.as_ref().is_some_and(|e| scan_expr(&e.stx))
        || f.stx.body.stx.body.iter().any(stmt_contains_suspend)
    }
    Stmt::ForIn(f) => {
      scan_expr(&f.stx.rhs.stx) || f.stx.body.stx.body.iter().any(stmt_contains_suspend)
    }
    Stmt::ForOf(f) => {
      // `for await` awaits every iteration: always a suspend point (routed to the frame
      // machine, which reports it as unimplemented rather than silently iterating sync).
      f.stx.await_
        || scan_expr(&f.stx.rhs.stx)
        || f.stx.body.stx.body.iter().any(stmt_contains_suspend)
    }
    Stmt::Return(r) => r.stx.value.as_ref().is_some_and(|e| scan_expr(&e.stx)),
    Stmt::Throw(t) => scan_expr(&t.stx.value.stx),
    Stmt::Try(t) => {
      t.stx.wrapped.stx.body.iter().any(stmt_contains_suspend)
        || t
          .stx
          .catch
          .as_ref()
          .is_some_and(|c| c.stx.body.iter().any(stmt_contains_suspend))
        || t
          .stx
          .finally
          .as_ref()
          .is_some_and(|f| f.stx.body.iter().any(stmt_contains_suspend))
    }
    Stmt::Label(l) => scan_stmt(&l.stx.statement.stx),
    Stmt::Switch(sw) => {
      scan_expr(&sw.stx.test.stx)
        || sw.stx.branches.iter().any(|b| {
          b.stx.case.as_ref().is_some_and(|e| scan_expr(&e.stx))
            || b.stx.body.iter().any(stmt_contains_suspend)
        })
    }
    Stmt::VarDecl(d) => var_decl_contains_suspend(&d.stx),
    Stmt::With(w) => scan_expr(&w.stx.object.stx) || scan_stmt(&w.stx.body.stx),
    _ => false,
  }
}

fn var_decl_contains_suspend(d: &VarDecl) -> bool {
  d.declarators
    .iter()
    .any(|decl| decl.initializer.as_ref().is_some_and(|e| scan_expr(&e.stx)))
}

// ---------------------------------------------------------------------------
// Step outcomes and driver
// ---------------------------------------------------------------------------

enum StepOutcome {
  /// State changed; re-enter step with this feedback.
  Continue(Feedback),
  /// Push a new child frame (applied by `drive` after the current borrow ends) and re-enter with
  /// `Feedback::Start`.
  Push(Frame),
  /// Perform outside the borrow; the result becomes the next feedback.
  Do(Action),
  Suspend(SuspendKind, Value),
  Done(Completion),
}

fn unsupported(what: &'static str) -> VmError {
  VmError::Unimplemented(what)
}

/// Drives `body` until it suspends or completes.
///
/// `resume` is the injected feedback: `Feedback::Start` on first entry, `Feedback::Value(v)` for
/// `next(v)` / await fulfilment, `Feedback::Completion(..)` for `throw(v)` / `return(v)`
/// injection / await rejection.
///
/// The caller must ensure the evaluator's lexical/variable environments are set to the body's
/// current environments before calling (see `Evaluator::with_resumable_env`).
pub(crate) fn drive(
  ev: &mut Evaluator<'_>,
  scope: &mut Scope<'_>,
  body: &Rc<RefCell<ResumableBody>>,
  resume: Feedback,
) -> Result<DriveOutcome, VmError> {
  if body.borrow().frames.is_empty() {
    return Err(VmError::InvariantViolation(
      "drive called on a resumable body with no frames",
    ));
  }

  let mut feedback = resume;
  loop {
    ev.tick_pub()?;

    let outcome = {
      let mut b = body.borrow_mut();
      step(ev, scope, &mut b, feedback)?
    };

    match outcome {
      StepOutcome::Continue(fb) => feedback = fb,
      StepOutcome::Push(frame) => {
        body.borrow_mut().frames.push(frame);
        feedback = Feedback::Start;
      }
      StepOutcome::Do(action) => {
        feedback = match perform(ev, scope, action) {
          Ok(fb) => fb,
          // JS-level throws become abrupt completions that unwind the frame stack (running
          // finally blocks / closing iterators). Host-level errors propagate as-is.
          Err(err) => match ev.error_to_thrown(scope, err) {
            Ok(thrown) => Feedback::Completion(Completion::Throw(thrown)),
            Err(host_err) => {
              // Persist the current lexical env before propagating so a later resume (if any)
              // does not observe a stale environment. The body is poisoned by the caller.
              let mut b = body.borrow_mut();
              b.lexical_env = ev.lexical_env_pub();
              drop(b);
              return Err(host_err);
            }
          },
        };
      }
      StepOutcome::Suspend(kind, value) => {
        // Persist the current lexical env so tracing/resume sees the correct scope chain.
        let mut b = body.borrow_mut();
        b.lexical_env = ev.lexical_env_pub();
        drop(b);
        return Ok(DriveOutcome::Suspended(kind, value));
      }
      StepOutcome::Done(completion) => {
        return Ok(DriveOutcome::Completed(completion));
      }
    }
  }
}

/// Performs an action with no borrow of the resumable body held.
fn perform(
  ev: &mut Evaluator<'_>,
  scope: &mut Scope<'_>,
  action: Action,
) -> Result<Feedback, VmError> {
  match action {
    Action::EvalExpr(e) => Ok(Feedback::Value(ev.eval_expr_pub(scope, e.get())?)),
    Action::EvalChain(e) => match ev.eval_chain_pub(scope, e.get())? {
      Some(v) => Ok(Feedback::Value(v)),
      None => Ok(Feedback::ShortCircuit),
    },
    Action::EvalStmt(s, labels) => Ok(Feedback::Completion(ev.eval_stmt_labelled_pub(
      scope,
      s.get(),
      &labels,
    )?)),
    Action::EvalVarDecl(d) => {
      ev.eval_var_decl_pub(scope, &d.get().stx)?;
      Ok(Feedback::Completion(Completion::empty()))
    }
    Action::EnterBlockEnv(list) => {
      let prev = ev.enter_block_env_pub(scope, list.get())?;
      Ok(Feedback::Env(Some(prev)))
    }
    Action::EnterPlainEnv => {
      let prev = ev.enter_plain_env_pub(scope)?;
      Ok(Feedback::Env(Some(prev)))
    }
    Action::BinaryOp(op, l, r) => Ok(Feedback::Value(ev.binary_value_op_pub(scope, op, l, r)?)),
    Action::PrivateIn(bin, right) => {
      let name = match &*bin.get().stx.left.stx {
        Expr::Id(id) => id.stx.name.as_str(),
        _ => {
          return Err(VmError::InvariantViolation(
            "PrivateIn action without private identifier lhs",
          ))
        }
      };
      Ok(Feedback::Value(ev.eval_private_in_pub(scope, name, right)?))
    }
    Action::UnaryOp(op, v) => Ok(Feedback::Value(ev.unary_value_op_pub(scope, op, v)?)),
    Action::ResolveTarget(e) => Ok(Feedback::Reference(
      ev.resolve_owned_reference_pub(scope, e.get())?,
    )),
    Action::LoadReference(r) => Ok(Feedback::Value(ev.owned_reference_get_pub(scope, &r)?)),
    Action::StoreReference(r, v) => {
      ev.owned_reference_put_pub(scope, &r, v)?;
      Ok(Feedback::Value(v))
    }
    Action::EvalCallee(e) => {
      let (func, this) = ev.eval_callee_pub(scope, e.get())?;
      Ok(Feedback::Callee { func, this })
    }
    Action::Call { func, this, args } => Ok(Feedback::Value(
      ev.call_function_value_pub(scope, func, this, &args)?,
    )),
    Action::GetIterator(v) => Ok(Feedback::Iterator(ev.get_iterator_pub(scope, v)?)),
    Action::GetAsyncIterator(v) => Ok(Feedback::Iterator(ev.get_async_iterator_pub(scope, v)?)),
    Action::IteratorNext(record) => Ok(Feedback::Value(ev.iterator_next_pub(scope, &record)?)),
    Action::IterStepValue(mut record) => {
      let v = ev.iterator_step_value_pub(scope, &mut record)?;
      Ok(Feedback::IterStep(record, v))
    }
    Action::IterClose(record) => {
      ev.iterator_close_quiet_pub(scope, &record);
      Ok(Feedback::Done)
    }
    Action::IterResultParts(v) => {
      let (value, done) = ev.iterator_result_parts_pub(scope, v)?;
      Ok(Feedback::IterParts(value, done))
    }
    Action::BindForOfLhs(stmt, value) => Ok(Feedback::Env(ev.bind_for_of_lhs_pub(
      scope,
      &stmt.get().stx,
      value,
    )?)),
    Action::EnterCatch(catch, thrown) => Ok(Feedback::Env(Some(ev.enter_catch_env_pub(
      scope,
      &catch.get().stx,
      thrown,
    )?))),
    Action::BindDeclarator(decl, idx, value) => {
      ev.bind_var_declarator_pub(scope, &decl.get().stx, idx, value)?;
      Ok(Feedback::Done)
    }
    Action::ArrayNew => Ok(Feedback::Array(ev.array_literal_new_pub(scope)?)),
    Action::ArrayDefine(arr, idx, v) => {
      ev.array_literal_define_pub(scope, arr, idx, v)?;
      Ok(Feedback::Done)
    }
    Action::ArrayFinalize(arr, len) => {
      ev.array_literal_finalize_pub(scope, arr, len)?;
      Ok(Feedback::Done)
    }
    Action::ObjectNew => Ok(Feedback::Object(ev.object_literal_new_pub(scope)?)),
    Action::ObjectApplyMember(obj, lit, idx) => {
      ev.object_literal_apply_member_pub(scope, obj, &lit.get().stx, idx)?;
      Ok(Feedback::Done)
    }
    Action::ObjectDefine(obj, key, value) => {
      ev.object_literal_define_pub(scope, obj, key, value)?;
      Ok(Feedback::Done)
    }
    Action::ObjectDefineDirect(obj, lit, idx, value) => {
      ev.object_literal_define_direct_pub(scope, obj, &lit.get().stx, idx, value)?;
      Ok(Feedback::Done)
    }
    Action::ObjectSpread(obj, source) => {
      ev.object_literal_spread_pub(scope, obj, source)?;
      Ok(Feedback::Done)
    }
    Action::GetComputed(base, key) => Ok(Feedback::Value(ev.get_computed_pub(scope, base, key)?)),
    Action::GetMethod(obj, name) => Ok(Feedback::Method(ev.get_method_pub(scope, obj, name)?)),
    Action::ThrowTypeError(msg) => Err(ev.make_type_error_pub(scope, msg)?),
    Action::EnterWithEnv(obj) => Ok(Feedback::Env(Some(ev.enter_with_env_pub(scope, obj)?))),
  }
}

// ---------------------------------------------------------------------------
// Frame construction
// ---------------------------------------------------------------------------

/// Request evaluation of an expression: delegate suspend-free subtrees to the recursive
/// evaluator, otherwise push a frame.
fn request_expr(node: &Node<Expr>) -> Result<StepOutcome, VmError> {
  if !expr_contains_suspend(node) {
    return Ok(StepOutcome::Do(Action::EvalExpr(NodeRef::new(node))));
  }
  Ok(StepOutcome::Push(make_expr_frame(node)?))
}

fn request_stmt(node: &Node<Stmt>, labels: &[String]) -> Result<StepOutcome, VmError> {
  if !stmt_contains_suspend(node) {
    return Ok(StepOutcome::Do(Action::EvalStmt(
      NodeRef::new(node),
      labels.to_vec(),
    )));
  }
  Ok(StepOutcome::Push(make_stmt_frame(node, labels)?))
}

fn make_expr_frame(node: &Node<Expr>) -> Result<Frame, VmError> {
  Ok(match &*node.stx {
    Expr::Unary(u) => {
      let operand = NodeRef::new(&u.stx.argument);
      match u.stx.operator {
        OperatorName::Yield => Frame::Yield {
          operand,
          started: false,
        },
        OperatorName::Await => Frame::Await {
          operand,
          started: false,
        },
        OperatorName::YieldDelegated => Frame::YieldStar {
          operand,
          phase: YieldStarPhase::Operand,
          record: None,
          sent: None,
        },
        OperatorName::Typeof
        | OperatorName::Void
        | OperatorName::LogicalNot
        | OperatorName::BitwiseNot
        | OperatorName::UnaryNegation
        | OperatorName::UnaryPlus => Frame::Unary {
          op: u.stx.operator,
          operand,
          started: false,
        },
        _ => return Err(unsupported("yield/await under this unary operator")),
      }
    }
    Expr::Binary(b) => Frame::Binary {
      node: NodeRef::new(b),
      phase: BinPhase::Left,
      left: None,
      target: None,
    },
    Expr::Cond(c) => Frame::Cond {
      node: NodeRef::new(c),
      started: false,
    },
    Expr::Call(c) => Frame::Call {
      node: NodeRef::new(c),
      phase: CallPhase::Callee,
      func: Value::Undefined,
      this: Value::Undefined,
      args: Vec::new(),
      arg_idx: 0,
    },
    Expr::LitArr(a) => Frame::ArrayLit {
      node: NodeRef::new(a),
      elem_idx: 0,
      arr: None,
      next_index: 0,
      finalizing: false,
      phase: ArrayLitPhase::Elements,
      spread_record: None,
    },
    Expr::LitObj(o) => Frame::ObjectLit {
      node: NodeRef::new(o),
      member_idx: 0,
      obj: None,
      phase: ObjectLitPhase::Members,
      pending_key: None,
    },
    Expr::ComputedMember(m) => Frame::ComputedMember {
      node: NodeRef::new(m),
      phase: ComputedMemberPhase::Object,
      object: None,
    },
    _ => return Err(unsupported("yield/await in this expression position")),
  })
}

fn make_stmt_frame(node: &Node<Stmt>, labels: &[String]) -> Result<Frame, VmError> {
  Ok(match &*node.stx {
    Stmt::Expr(e) => Frame::ExprStmt {
      node: NodeRef::new(e),
      started: false,
    },
    Stmt::Block(bl) => Frame::StmtList {
      list: ListRef::new(&bl.stx.body),
      idx: 0,
      last: None,
      needs_env: true,
      restore_env: None,
    },
    Stmt::If(i) => Frame::If {
      node: NodeRef::new(i),
      started: false,
    },
    Stmt::While(w) => Frame::While {
      node: NodeRef::new(w),
      labels: labels.to_vec(),
      phase: LoopPhase::Cond,
      v: None,
    },
    Stmt::DoWhile(d) => Frame::DoWhile {
      node: NodeRef::new(d),
      labels: labels.to_vec(),
      phase: LoopPhase::Body,
      v: None,
    },
    Stmt::ForTriple(f) => Frame::ForTriple {
      node: NodeRef::new(f),
      labels: labels.to_vec(),
      phase: ForTriplePhase::Init,
      v: None,
      restore_env: None,
      init_done: false,
      per_iteration_names: Vec::new(),
    },
    Stmt::ForOf(f) => Frame::ForOf {
      node: NodeRef::new(f),
      labels: labels.to_vec(),
      phase: ForOfPhase::Rhs,
      record: None,
      v: None,
      iter_restore: None,
      pending: None,
    },
    Stmt::Try(t) => Frame::Try {
      node: NodeRef::new(t),
      phase: TryPhase::Block,
      resume: None,
      catch_restore: None,
    },
    Stmt::Label(l) => Frame::Label {
      name: l.stx.name.clone(),
      node: NodeRef::new(l),
      labels: labels.to_vec(),
      started: false,
    },
    Stmt::Return(r) => Frame::Return {
      node: NodeRef::new(r),
      started: false,
    },
    Stmt::Throw(t) => Frame::Throw {
      node: NodeRef::new(t),
      started: false,
    },
    Stmt::VarDecl(d) => Frame::VarDecl {
      node: NodeRef::new(d),
      idx: 0,
      phase: VarDeclPhase::NextDecl,
    },
    Stmt::With(w) => Frame::With {
      node: NodeRef::new(w),
      phase: WithPhase::Object,
      restore_env: None,
    },
    Stmt::Switch(_) => return Err(unsupported("yield/await inside switch")),
    Stmt::ForIn(_) => return Err(unsupported("yield/await inside for-in")),
    _ => return Err(unsupported("yield/await in this statement position")),
  })
}

// ---------------------------------------------------------------------------
// The step function
// ---------------------------------------------------------------------------

/// One transition of the frame machine. Runs under a short borrow of the body; must not allocate
/// on the JS heap (all allocation goes through returned `Action`s).
fn step(
  ev: &mut Evaluator<'_>,
  scope: &mut Scope<'_>,
  b: &mut ResumableBody,
  feedback: Feedback,
) -> Result<StepOutcome, VmError> {
  let Some(top) = b.frames.last_mut() else {
    return Ok(match feedback {
      Feedback::Completion(c) => StepOutcome::Done(c),
      Feedback::Value(v) => StepOutcome::Done(Completion::Normal(Some(v))),
      _ => StepOutcome::Done(Completion::Normal(None)),
    });
  };

  match top {
    // ----------------------------- statement list -----------------------------
    Frame::StmtList {
      list,
      idx,
      last,
      needs_env,
      restore_env,
    } => {
      match feedback {
        Feedback::Start => {
          if *needs_env && restore_env.is_none() {
            let list = *list;
            return Ok(StepOutcome::Do(Action::EnterBlockEnv(list)));
          }
        }
        Feedback::Env(prev) => {
          *restore_env = prev;
        }
        Feedback::Completion(c) => {
          let c = c.update_empty(*last);
          match c {
            Completion::Normal(v) => {
              if v.is_some() {
                *last = v;
              }
            }
            abrupt => {
              let restore = *restore_env;
              b.frames.pop();
              if let Some(env) = restore {
                ev.set_lexical_env_pub(scope, env);
              }
              return Ok(StepOutcome::Continue(Feedback::Completion(abrupt)));
            }
          }
        }
        _ => return Err(unsupported("unexpected feedback for StmtList")),
      }

      let list = *list;
      let i = *idx;
      if i >= list.get().len() {
        let completion = Completion::Normal(*last);
        let restore = *restore_env;
        b.frames.pop();
        if let Some(env) = restore {
          ev.set_lexical_env_pub(scope, env);
        }
        return Ok(StepOutcome::Continue(Feedback::Completion(completion)));
      }
      *idx = i + 1;
      let node = &list.get()[i];
      request_stmt(node, &[])
    }

    // ----------------------------- simple statements -----------------------------
    Frame::ExprStmt { node, started } => match feedback {
      Feedback::Start if !*started => {
        *started = true;
        let expr = &node.get().stx.expr;
        request_expr(expr)
      }
      Feedback::Value(v) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(
          Completion::Normal(Some(v)),
        )))
      }
      Feedback::Completion(c) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      _ => Err(unsupported("unexpected feedback for ExprStmt")),
    },

    Frame::Return { node, started } => match feedback {
      Feedback::Start if !*started => {
        *started = true;
        match &node.get().stx.value {
          None => {
            b.frames.pop();
            Ok(StepOutcome::Continue(Feedback::Completion(
              Completion::Return(Value::Undefined),
            )))
          }
          Some(value) => request_expr(value),
        }
      }
      Feedback::Value(v) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(
          Completion::Return(v),
        )))
      }
      Feedback::Completion(c) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      _ => Err(unsupported("unexpected feedback for Return")),
    },

    Frame::ImplicitReturn { operand, started } => match feedback {
      Feedback::Start if !*started => {
        *started = true;
        let operand = *operand;
        request_expr(operand.get())
      }
      Feedback::Value(v) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(
          Completion::Return(v),
        )))
      }
      Feedback::Completion(c) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      _ => Err(unsupported("unexpected feedback for ImplicitReturn")),
    },

    Frame::Throw { node, started } => match feedback {
      Feedback::Start if !*started => {
        *started = true;
        let value = &node.get().stx.value;
        request_expr(value)
      }
      Feedback::Value(v) => {
        b.frames.pop();
        let thrown = ev.thrown_from_value_pub(v);
        Ok(StepOutcome::Continue(Feedback::Completion(
          Completion::Throw(thrown),
        )))
      }
      Feedback::Completion(c) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      _ => Err(unsupported("unexpected feedback for Throw")),
    },

    Frame::If { node, started } => match feedback {
      Feedback::Start if !*started => {
        *started = true;
        let test = &node.get().stx.test;
        request_expr(test)
      }
      Feedback::Value(v) => {
        let stmt_node = *node;
        let truthy = ev.to_boolean_pub(scope, v)?;
        let stmt = stmt_node.get();
        let branch: Option<&Node<Stmt>> = if truthy {
          Some(&stmt.stx.consequent)
        } else {
          stmt.stx.alternate.as_ref()
        };
        match branch {
          // Keep this If frame so the branch completion is UpdateEmpty'd with undefined.
          Some(branch_node) => request_stmt(branch_node, &[]),
          None => {
            b.frames.pop();
            Ok(StepOutcome::Continue(Feedback::Completion(
              Completion::empty().update_empty(Some(Value::Undefined)),
            )))
          }
        }
      }
      Feedback::Completion(c) => {
        b.frames.pop();
        // IfStatement: Return ? UpdateEmpty(stmtCompletion, undefined).
        Ok(StepOutcome::Continue(Feedback::Completion(
          c.update_empty(Some(Value::Undefined)),
        )))
      }
      _ => Err(unsupported("unexpected feedback for If")),
    },

    Frame::Label {
      name,
      node,
      labels,
      started,
    } => match feedback {
      Feedback::Start if !*started => {
        *started = true;
        let mut new_labels = labels.clone();
        new_labels.push(name.clone());
        let stmt = &node.get().stx.statement;
        request_stmt(stmt, &new_labels)
      }
      Feedback::Completion(c) => {
        let name = name.clone();
        b.frames.pop();
        let c = match c {
          Completion::Break(Some(target), value) if target == name => Completion::Normal(value),
          other => other,
        };
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      _ => Err(unsupported("unexpected feedback for Label")),
    },

    Frame::With {
      node,
      phase,
      restore_env,
    } => match (*phase, feedback) {
      (WithPhase::Object, Feedback::Start) => {
        let obj = &node.get().stx.object;
        request_expr(obj)
      }
      (WithPhase::Object, Feedback::Value(v)) => Ok(StepOutcome::Do(Action::EnterWithEnv(v))),
      (WithPhase::Object, Feedback::Env(prev)) => {
        *restore_env = prev;
        *phase = WithPhase::Body;
        let body = &node.get().stx.body;
        request_stmt(body, &[])
      }
      // Object-expression / ToObject abrupt: env not installed yet.
      (WithPhase::Object, Feedback::Completion(c)) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      (WithPhase::Body, Feedback::Completion(c)) => {
        let restore = *restore_env;
        b.frames.pop();
        if let Some(env) = restore {
          ev.set_lexical_env_pub(scope, env);
        }
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      _ => Err(unsupported("unexpected feedback for With")),
    },

    Frame::VarDecl { node, idx, phase } => {
      let decl_node = *node;
      match (feedback, *phase) {
        (Feedback::Start, VarDeclPhase::NextDecl) | (Feedback::Done, VarDeclPhase::Bound) => {
          let d = &decl_node.get().stx;
          let i = *idx;
          if i >= d.declarators.len() {
            b.frames.pop();
            return Ok(StepOutcome::Continue(Feedback::Completion(
              Completion::empty(),
            )));
          }
          *idx = i + 1;
          let declarator = &d.declarators[i];
          match &declarator.initializer {
            None => {
              *phase = VarDeclPhase::Bound;
              Ok(StepOutcome::Do(Action::BindDeclarator(
                decl_node,
                i,
                Value::Undefined,
              )))
            }
            Some(init) => {
              *phase = VarDeclPhase::Init;
              request_expr(init)
            }
          }
        }
        (Feedback::Value(v), VarDeclPhase::Init) => {
          *phase = VarDeclPhase::Bound;
          let i = *idx - 1;
          Ok(StepOutcome::Do(Action::BindDeclarator(decl_node, i, v)))
        }
        (Feedback::Completion(c), _) => {
          b.frames.pop();
          Ok(StepOutcome::Continue(Feedback::Completion(c)))
        }
        _ => Err(unsupported("unexpected feedback for VarDecl")),
      }
    }

    // ----------------------------- loops -----------------------------
    Frame::While {
      node,
      labels,
      phase,
      v,
    } => {
      let stmt = *node;
      match (feedback, *phase) {
        (Feedback::Start, LoopPhase::Cond) => request_expr(&stmt.get().stx.condition),
        (Feedback::Value(cond), LoopPhase::Cond) => {
          if ev.to_boolean_pub(scope, cond)? {
            *phase = LoopPhase::Body;
            request_stmt(&stmt.get().stx.body, &[])
          } else {
            let out = Completion::Normal(*v);
            b.frames.pop();
            Ok(StepOutcome::Continue(Feedback::Completion(out)))
          }
        }
        (Feedback::Completion(c), LoopPhase::Body) => {
          let label_set = labels.clone();
          if let Some(val) = c.value() {
            *v = Some(val);
          }
          if Evaluator::loop_continues_pub(&c, &label_set) {
            *phase = LoopPhase::Cond;
            request_expr(&stmt.get().stx.condition)
          } else {
            let out = normalize_loop_exit(c, &label_set, *v);
            b.frames.pop();
            Ok(StepOutcome::Continue(Feedback::Completion(out)))
          }
        }
        (Feedback::Completion(c), LoopPhase::Cond) => {
          b.frames.pop();
          Ok(StepOutcome::Continue(Feedback::Completion(c)))
        }
        _ => Err(unsupported("unexpected feedback for While")),
      }
    }

    Frame::DoWhile {
      node,
      labels,
      phase,
      v,
    } => {
      let stmt = *node;
      match (feedback, *phase) {
        (Feedback::Start, LoopPhase::Body) => request_stmt(&stmt.get().stx.body, &[]),
        (Feedback::Completion(c), LoopPhase::Body) => {
          let label_set = labels.clone();
          if let Some(val) = c.value() {
            *v = Some(val);
          }
          if Evaluator::loop_continues_pub(&c, &label_set) {
            *phase = LoopPhase::Cond;
            request_expr(&stmt.get().stx.condition)
          } else {
            let out = normalize_loop_exit(c, &label_set, *v);
            b.frames.pop();
            Ok(StepOutcome::Continue(Feedback::Completion(out)))
          }
        }
        (Feedback::Value(cond), LoopPhase::Cond) => {
          if ev.to_boolean_pub(scope, cond)? {
            *phase = LoopPhase::Body;
            request_stmt(&stmt.get().stx.body, &[])
          } else {
            let out = Completion::Normal(*v);
            b.frames.pop();
            Ok(StepOutcome::Continue(Feedback::Completion(out)))
          }
        }
        (Feedback::Completion(c), LoopPhase::Cond) => {
          b.frames.pop();
          Ok(StepOutcome::Continue(Feedback::Completion(c)))
        }
        _ => Err(unsupported("unexpected feedback for DoWhile")),
      }
    }

    Frame::ForTriple {
      node,
      labels,
      phase,
      v,
      restore_env,
      init_done,
      per_iteration_names,
    } => {
      let stmt = *node;
      match (feedback, *phase) {
        (Feedback::Start, ForTriplePhase::Init) => match &stmt.get().stx.init {
          ForTripleStmtInit::None => {
            *init_done = true;
            for_triple_request_cond(stmt, phase)
          }
          ForTripleStmtInit::Expr(e) => {
            if expr_contains_suspend(e) {
              return Err(unsupported("yield/await in for-loop init expression"));
            }
            Ok(StepOutcome::Do(Action::EvalExpr(NodeRef::new(e))))
          }
          ForTripleStmtInit::Decl(d) => {
            if var_decl_contains_suspend(&d.stx) {
              return Err(unsupported("yield/await in for-loop init declaration"));
            }
            let mode = d.stx.mode;
            if matches!(mode, VarDeclMode::Let | VarDeclMode::Const) {
              // Loop decls live in a fresh env owned by this frame.
              *per_iteration_names = Evaluator::collect_for_triple_per_iteration_names_pub(&d.stx);
              Ok(StepOutcome::Do(Action::EnterPlainEnv))
            } else {
              *init_done = true;
              Ok(StepOutcome::Do(Action::EvalVarDecl(NodeRef::new(d))))
            }
          }
        },
        (Feedback::Env(prev), ForTriplePhase::Init) => {
          *restore_env = prev;
          *init_done = true;
          let ForTripleStmtInit::Decl(d) = &stmt.get().stx.init else {
            return Err(unsupported("for-loop env without decl"));
          };
          Ok(StepOutcome::Do(Action::EvalVarDecl(NodeRef::new(d))))
        }
        (Feedback::Value(_), ForTriplePhase::Init)
        | (Feedback::Completion(Completion::Normal(_)), ForTriplePhase::Init) => {
          // ForBodyEvaluation step 2: CreatePerIterationEnvironment before first test.
          ev.create_per_iteration_environment_pub(scope, per_iteration_names)?;
          for_triple_request_cond(stmt, phase)
        }
        (Feedback::Value(cond), ForTriplePhase::Cond) => {
          if ev.to_boolean_pub(scope, cond)? {
            *phase = ForTriplePhase::Body;
            let body_list = ListRef::new(&stmt.get().stx.body.stx.body);
            b.frames.push(Frame::StmtList {
              list: body_list,
              idx: 0,
              last: None,
              needs_env: false,
              restore_env: None,
            });
            Ok(StepOutcome::Continue(Feedback::Start))
          } else {
            let out = Completion::Normal(*v);
            let restore = *restore_env;
            b.frames.pop();
            if let Some(env) = restore {
              ev.set_lexical_env_pub(scope, env);
            }
            Ok(StepOutcome::Continue(Feedback::Completion(out)))
          }
        }
        (Feedback::Completion(c), ForTriplePhase::Body) => {
          let label_set = labels.clone();
          if let Some(val) = c.value() {
            *v = Some(val);
          }
          if Evaluator::loop_continues_pub(&c, &label_set) {
            // ForBodyEvaluation step 3.e — before the increment.
            ev.create_per_iteration_environment_pub(scope, per_iteration_names)?;
            match &stmt.get().stx.post {
              Some(post) => {
                *phase = ForTriplePhase::Post;
                if expr_contains_suspend(post) {
                  let frame = make_expr_frame(post)?;
                  b.frames.push(frame);
                  Ok(StepOutcome::Continue(Feedback::Start))
                } else {
                  Ok(StepOutcome::Do(Action::EvalExpr(NodeRef::new(post))))
                }
              }
              None => for_triple_request_cond(stmt, phase),
            }
          } else {
            let out = normalize_loop_exit(c, &label_set, *v);
            let restore = *restore_env;
            b.frames.pop();
            if let Some(env) = restore {
              ev.set_lexical_env_pub(scope, env);
            }
            Ok(StepOutcome::Continue(Feedback::Completion(out)))
          }
        }
        (Feedback::Value(_), ForTriplePhase::Post) => for_triple_request_cond(stmt, phase),
        (Feedback::Completion(c), _) => {
          let restore = *restore_env;
          b.frames.pop();
          if let Some(env) = restore {
            ev.set_lexical_env_pub(scope, env);
          }
          Ok(StepOutcome::Continue(Feedback::Completion(c)))
        }
        _ => Err(unsupported("unexpected feedback for ForTriple")),
      }
    }

    Frame::ForOf {
      node,
      labels,
      phase,
      record,
      v,
      iter_restore,
      pending,
    } => {
      let stmt = *node;
      let is_await = stmt.get().stx.await_;
      match (*phase, feedback) {
        (ForOfPhase::Rhs, Feedback::Start) => request_expr(&stmt.get().stx.rhs),
        (ForOfPhase::Rhs, Feedback::Value(rhs)) => {
          *phase = ForOfPhase::GetIter;
          if is_await {
            Ok(StepOutcome::Do(Action::GetAsyncIterator(rhs)))
          } else {
            Ok(StepOutcome::Do(Action::GetIterator(rhs)))
          }
        }
        (ForOfPhase::GetIter, Feedback::Iterator(rec)) => {
          *record = Some(rec);
          *phase = ForOfPhase::Next;
          if is_await {
            Ok(StepOutcome::Do(Action::IteratorNext(rec)))
          } else {
            Ok(StepOutcome::Do(Action::IterStepValue(rec)))
          }
        }
        // Sync for-of: IterStepValue yields Option<Value> directly.
        (ForOfPhase::Next, Feedback::IterStep(rec, next)) if !is_await => {
          *record = Some(rec);
          match next {
            None => {
              let out = Completion::Normal(*v);
              b.frames.pop();
              Ok(StepOutcome::Continue(Feedback::Completion(out)))
            }
            Some(value) => {
              *phase = ForOfPhase::Bind;
              Ok(StepOutcome::Do(Action::BindForOfLhs(stmt, value)))
            }
          }
        }
        // Async for-await: `next()` returned a Promise (or thenable); await it.
        (ForOfPhase::Next, Feedback::Value(next_result)) if is_await => {
          *phase = ForOfPhase::AwaitNext;
          Ok(StepOutcome::Suspend(SuspendKind::Await, next_result))
        }
        (ForOfPhase::AwaitNext, Feedback::Value(result_obj)) => {
          *phase = ForOfPhase::AwaitNext; // stay until IterParts arrives
          Ok(StepOutcome::Do(Action::IterResultParts(result_obj)))
        }
        (ForOfPhase::AwaitNext, Feedback::IterParts(value, done)) => {
          if done {
            let out = Completion::Normal(*v);
            b.frames.pop();
            Ok(StepOutcome::Continue(Feedback::Completion(out)))
          } else {
            *phase = ForOfPhase::Bind;
            Ok(StepOutcome::Do(Action::BindForOfLhs(stmt, value)))
          }
        }
        (ForOfPhase::Bind, Feedback::Env(prev)) => {
          *iter_restore = prev;
          *phase = ForOfPhase::Body;
          let body_list = ListRef::new(&stmt.get().stx.body.stx.body);
          b.frames.push(Frame::StmtList {
            list: body_list,
            idx: 0,
            last: None,
            needs_env: false,
            restore_env: None,
          });
          Ok(StepOutcome::Continue(Feedback::Start))
        }
        (ForOfPhase::Body, Feedback::Completion(c)) => {
          if let Some(env) = iter_restore.take() {
            ev.set_lexical_env_pub(scope, env);
          }
          let label_set = labels.clone();
          if let Some(val) = c.value() {
            *v = Some(val);
          }
          if Evaluator::loop_continues_pub(&c, &label_set) {
            *phase = ForOfPhase::Next;
            let rec = record.expect("for-of record");
            if is_await {
              Ok(StepOutcome::Do(Action::IteratorNext(rec)))
            } else {
              Ok(StepOutcome::Do(Action::IterStepValue(rec)))
            }
          } else {
            let out = normalize_loop_exit(c, &label_set, *v);
            *pending = Some(out);
            *phase = ForOfPhase::Closing;
            let rec = record.expect("for-of record");
            Ok(StepOutcome::Do(Action::IterClose(rec)))
          }
        }
        (ForOfPhase::Closing, _) => {
          let out = pending.take().unwrap_or(Completion::Normal(None));
          b.frames.pop();
          Ok(StepOutcome::Continue(Feedback::Completion(out)))
        }
        (ForOfPhase::Bind, Feedback::Completion(c)) => {
          // Binding threw: close the iterator, then re-emit.
          *pending = Some(c);
          *phase = ForOfPhase::Closing;
          let rec = record.expect("for-of record");
          Ok(StepOutcome::Do(Action::IterClose(rec)))
        }
        (_, Feedback::Completion(c)) => {
          // Rhs/GetIter/Next threw: iterator not closed per spec (error came from the protocol).
          b.frames.pop();
          Ok(StepOutcome::Continue(Feedback::Completion(c)))
        }
        _ => Err(unsupported("unexpected feedback for ForOf")),
      }
    }

    // ----------------------------- try/catch/finally -----------------------------
    Frame::Try {
      node,
      phase,
      resume,
      catch_restore,
    } => {
      let stmt = *node;
      match (*phase, feedback) {
        (TryPhase::Block, Feedback::Start) => {
          let list = ListRef::new(&stmt.get().stx.wrapped.stx.body);
          b.frames.push(Frame::StmtList {
            list,
            idx: 0,
            last: None,
            needs_env: true,
            restore_env: None,
          });
          Ok(StepOutcome::Continue(Feedback::Start))
        }
        (TryPhase::Block, Feedback::Completion(c)) => match (&c, &stmt.get().stx.catch) {
          (Completion::Throw(thrown), Some(catch)) => {
            *phase = TryPhase::CatchEnter;
            let thrown_value = thrown.value;
            Ok(StepOutcome::Do(Action::EnterCatch(
              NodeRef::new(catch),
              thrown_value,
            )))
          }
          _ => finish_try_with_finally(ev, scope, b, c),
        },
        (TryPhase::CatchEnter, Feedback::Env(prev)) => {
          *catch_restore = prev;
          *phase = TryPhase::Catch;
          let catch = stmt.get().stx.catch.as_ref().expect("catch block");
          let list = ListRef::new(&catch.stx.body);
          b.frames.push(Frame::StmtList {
            list,
            idx: 0,
            last: None,
            needs_env: false,
            restore_env: None,
          });
          Ok(StepOutcome::Continue(Feedback::Start))
        }
        (TryPhase::CatchEnter, Feedback::Completion(c)) => {
          // Catch-parameter binding itself threw.
          finish_try_with_finally(ev, scope, b, c)
        }
        (TryPhase::Catch, Feedback::Completion(c)) => {
          if let Some(env) = catch_restore.take() {
            ev.set_lexical_env_pub(scope, env);
          }
          finish_try_with_finally(ev, scope, b, c)
        }
        (TryPhase::Finally, Feedback::Completion(fin_c)) => {
          let out = match fin_c {
            Completion::Normal(_) => resume.take().unwrap_or(Completion::Normal(None)),
            abrupt => abrupt,
          };
          b.frames.pop();
          Ok(StepOutcome::Continue(Feedback::Completion(out)))
        }
        _ => Err(unsupported("unexpected feedback for Try")),
      }
    }

    // ----------------------------- suspension expressions -----------------------------
    Frame::Yield { operand, started } => match feedback {
      Feedback::Start if !*started => {
        *started = true;
        let operand = *operand;
        request_expr(operand.get())
      }
      Feedback::Value(v) => {
        // Operand ready: pop self and suspend. Resume feedback reaches the parent frame (the
        // consumer of the yield expression), and injected throw/return unwinds through Try
        // frames, running finally blocks.
        b.frames.pop();
        Ok(StepOutcome::Suspend(SuspendKind::Yield, v))
      }
      Feedback::Completion(c) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      _ => Err(unsupported("unexpected feedback for Yield")),
    },

    Frame::Await { operand, started } => match feedback {
      Feedback::Start if !*started => {
        *started = true;
        let operand = *operand;
        request_expr(operand.get())
      }
      Feedback::Value(v) => {
        b.frames.pop();
        Ok(StepOutcome::Suspend(SuspendKind::Await, v))
      }
      Feedback::Completion(c) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      _ => Err(unsupported("unexpected feedback for Await")),
    },

    Frame::YieldStar {
      operand,
      phase,
      record,
      sent,
    } => match (*phase, feedback) {
      (YieldStarPhase::Operand, Feedback::Start) => {
        let operand = *operand;
        *phase = YieldStarPhase::GetIter;
        request_expr(operand.get())
      }
      (YieldStarPhase::GetIter, Feedback::Value(v)) => Ok(StepOutcome::Do(Action::GetIterator(v))),
      (YieldStarPhase::GetIter, Feedback::Iterator(rec)) => {
        *record = Some(rec);
        if matches!(rec.next_method, Value::Undefined) {
          // Engine fast-path records (arrays) have no reified `next`; step via the helper.
          *phase = YieldStarPhase::FastStep;
          return Ok(StepOutcome::Do(Action::IterStepValue(rec)));
        }
        *phase = YieldStarPhase::AwaitResult;
        Ok(StepOutcome::Do(Action::Call {
          func: rec.next_method,
          this: rec.iterator,
          args: vec![Value::Undefined],
        }))
      }
      (YieldStarPhase::FastStep, Feedback::IterStep(rec, next)) => {
        *record = Some(rec);
        match next {
          // Fast-path iterators (arrays) have no meaningful return value.
          None => {
            b.frames.pop();
            Ok(StepOutcome::Continue(Feedback::Value(Value::Undefined)))
          }
          Some(v) => {
            *phase = YieldStarPhase::Forwarding;
            Ok(StepOutcome::Suspend(SuspendKind::Yield, v))
          }
        }
      }
      (YieldStarPhase::AwaitResult, Feedback::Value(res)) => {
        *phase = YieldStarPhase::AwaitParts;
        Ok(StepOutcome::Do(Action::IterResultParts(res)))
      }
      (YieldStarPhase::AwaitParts, Feedback::IterParts(value, done)) => {
        if done {
          // yield* evaluates to the inner iterator's return value.
          b.frames.pop();
          Ok(StepOutcome::Continue(Feedback::Value(value)))
        } else {
          *phase = YieldStarPhase::Forwarding;
          Ok(StepOutcome::Suspend(SuspendKind::Yield, value))
        }
      }
      // -- resume while forwarding --
      (YieldStarPhase::Forwarding, Feedback::Value(v)) => {
        let rec = record.expect("yield* record");
        if matches!(rec.next_method, Value::Undefined) {
          // Fast-path record: `next(v)` argument is meaningless for arrays; keep stepping.
          *phase = YieldStarPhase::FastStep;
          return Ok(StepOutcome::Do(Action::IterStepValue(rec)));
        }
        *phase = YieldStarPhase::AwaitResult;
        Ok(StepOutcome::Do(Action::Call {
          func: rec.next_method,
          this: rec.iterator,
          args: vec![v],
        }))
      }
      (YieldStarPhase::Forwarding, Feedback::Completion(c)) => {
        let rec = record.expect("yield* record");
        match c {
          Completion::Throw(_) => {
            *sent = Some(c);
            *phase = YieldStarPhase::AwaitThrowMethod;
            Ok(StepOutcome::Do(Action::GetMethod(rec.iterator, "throw")))
          }
          Completion::Return(_) => {
            *sent = Some(c);
            *phase = YieldStarPhase::AwaitReturnMethod;
            Ok(StepOutcome::Do(Action::GetMethod(rec.iterator, "return")))
          }
          other => {
            b.frames.pop();
            Ok(StepOutcome::Continue(Feedback::Completion(other)))
          }
        }
      }
      (YieldStarPhase::AwaitThrowMethod, Feedback::Method(m)) => {
        let rec = record.expect("yield* record");
        match m {
          Value::Undefined | Value::Null => {
            *phase = YieldStarPhase::CloseThenTypeError;
            Ok(StepOutcome::Do(Action::IterClose(rec)))
          }
          method => {
            let arg = match sent.take() {
              Some(Completion::Throw(t)) => t.value,
              _ => Value::Undefined,
            };
            *phase = YieldStarPhase::AwaitResult;
            Ok(StepOutcome::Do(Action::Call {
              func: method,
              this: rec.iterator,
              args: vec![arg],
            }))
          }
        }
      }
      (YieldStarPhase::CloseThenTypeError, _) => Ok(StepOutcome::Do(Action::ThrowTypeError(
        "iterator does not provide a 'throw' method",
      ))),
      (YieldStarPhase::AwaitReturnMethod, Feedback::Method(m)) => {
        let rec = record.expect("yield* record");
        let injected = sent.take();
        let ret_value = match &injected {
          Some(Completion::Return(v)) => *v,
          _ => Value::Undefined,
        };
        match m {
          Value::Undefined | Value::Null => {
            b.frames.pop();
            Ok(StepOutcome::Continue(Feedback::Completion(
              Completion::Return(ret_value),
            )))
          }
          method => {
            *sent = injected;
            *phase = YieldStarPhase::AwaitReturnResult;
            Ok(StepOutcome::Do(Action::Call {
              func: method,
              this: rec.iterator,
              args: vec![ret_value],
            }))
          }
        }
      }
      (YieldStarPhase::AwaitReturnResult, Feedback::Value(res)) => {
        *phase = YieldStarPhase::AwaitReturnParts;
        Ok(StepOutcome::Do(Action::IterResultParts(res)))
      }
      (YieldStarPhase::AwaitReturnParts, Feedback::IterParts(value, done)) => {
        if done {
          b.frames.pop();
          Ok(StepOutcome::Continue(Feedback::Completion(
            Completion::Return(value),
          )))
        } else {
          // Inner iterator not done after `return`: keep forwarding.
          *phase = YieldStarPhase::Forwarding;
          Ok(StepOutcome::Suspend(SuspendKind::Yield, value))
        }
      }
      (_, Feedback::Completion(c)) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      _ => Err(unsupported("unexpected feedback for YieldStar")),
    },

    // ----------------------------- expressions -----------------------------
    Frame::Unary {
      op,
      operand,
      started,
    } => match feedback {
      Feedback::Start if !*started => {
        *started = true;
        let operand = *operand;
        request_expr(operand.get())
      }
      Feedback::Value(v) => {
        let op = *op;
        b.frames.pop();
        Ok(StepOutcome::Do(Action::UnaryOp(op, v)))
      }
      Feedback::Completion(c) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      _ => Err(unsupported("unexpected feedback for Unary")),
    },

    Frame::Binary {
      node,
      phase,
      left,
      target,
    } => {
      let expr = *node;
      let op = expr.get().stx.operator;
      match (*phase, feedback) {
        (BinPhase::Left, Feedback::Start) => {
          if op == OperatorName::Assignment || is_compound_assignment(op) {
            let lhs = &expr.get().stx.left;
            if expr_contains_suspend(lhs) {
              return Err(unsupported("yield/await in assignment target"));
            }
            if !is_simple_target(lhs) {
              return Err(unsupported("yield/await in destructuring assignment value"));
            }
            *phase = BinPhase::Target;
            Ok(StepOutcome::Do(Action::ResolveTarget(NodeRef::new(lhs))))
          } else if op == OperatorName::In
            && matches!(
              &*expr.get().stx.left.stx,
              Expr::Id(id) if id.stx.name.starts_with('#')
            )
          {
            // `#PrivateName in rhs` — do not evaluate the PrivateIdentifier as a value.
            *phase = BinPhase::Right;
            request_expr(&expr.get().stx.right)
          } else {
            request_expr(&expr.get().stx.left)
          }
        }
        (BinPhase::Target, Feedback::Reference(r)) => {
          if op == OperatorName::Assignment {
            *target = Some(r);
            *phase = BinPhase::Right;
            request_expr(&expr.get().stx.right)
          } else {
            // Compound / logical assignment: read current value first.
            *phase = BinPhase::Load;
            *target = Some(r.clone());
            Ok(StepOutcome::Do(Action::LoadReference(r)))
          }
        }
        (BinPhase::Load, Feedback::Value(current)) => {
          if is_logical_assignment(op) {
            let truthy = ev.to_boolean_pub(scope, current)?;
            let short_circuit = match op {
              OperatorName::AssignmentLogicalAnd => !truthy,
              OperatorName::AssignmentLogicalOr => truthy,
              OperatorName::AssignmentNullishCoalescing => {
                !matches!(current, Value::Undefined | Value::Null)
              }
              _ => false,
            };
            if short_circuit {
              b.frames.pop();
              return Ok(StepOutcome::Continue(Feedback::Value(current)));
            }
          } else {
            *left = Some(current);
          }
          *phase = BinPhase::Right;
          request_expr(&expr.get().stx.right)
        }
        (BinPhase::Left, Feedback::Value(l)) => match op {
          OperatorName::LogicalAnd => {
            if !ev.to_boolean_pub(scope, l)? {
              b.frames.pop();
              Ok(StepOutcome::Continue(Feedback::Value(l)))
            } else {
              *phase = BinPhase::Right;
              request_expr(&expr.get().stx.right)
            }
          }
          OperatorName::LogicalOr => {
            if ev.to_boolean_pub(scope, l)? {
              b.frames.pop();
              Ok(StepOutcome::Continue(Feedback::Value(l)))
            } else {
              *phase = BinPhase::Right;
              request_expr(&expr.get().stx.right)
            }
          }
          OperatorName::NullishCoalescing => {
            if !matches!(l, Value::Undefined | Value::Null) {
              b.frames.pop();
              Ok(StepOutcome::Continue(Feedback::Value(l)))
            } else {
              *phase = BinPhase::Right;
              request_expr(&expr.get().stx.right)
            }
          }
          OperatorName::Comma => {
            *left = None;
            *phase = BinPhase::Right;
            request_expr(&expr.get().stx.right)
          }
          _ => {
            *left = Some(l);
            *phase = BinPhase::Right;
            request_expr(&expr.get().stx.right)
          }
        },
        (BinPhase::Right, Feedback::Value(r)) => {
          if op == OperatorName::Assignment || is_logical_assignment(op) {
            let target = target.take().expect("assignment target");
            *phase = BinPhase::Store;
            Ok(StepOutcome::Do(Action::StoreReference(target, r)))
          } else if let Some(value_op) = compound_base_op(op) {
            let l = left.take().expect("compound assignment current value");
            *phase = BinPhase::Apply;
            Ok(StepOutcome::Do(Action::BinaryOp(value_op, l, r)))
          } else if matches!(
            op,
            OperatorName::LogicalAnd
              | OperatorName::LogicalOr
              | OperatorName::NullishCoalescing
              | OperatorName::Comma
          ) {
            b.frames.pop();
            Ok(StepOutcome::Continue(Feedback::Value(r)))
          } else if op == OperatorName::In
            && left.is_none()
            && matches!(
              &*expr.get().stx.left.stx,
              Expr::Id(id) if id.stx.name.starts_with('#')
            )
          {
            b.frames.pop();
            Ok(StepOutcome::Do(Action::PrivateIn(expr, r)))
          } else {
            let l = left.take().expect("binary lhs value");
            b.frames.pop();
            Ok(StepOutcome::Do(Action::BinaryOp(op, l, r)))
          }
        }
        (BinPhase::Apply, Feedback::Value(result)) => {
          let target = target.take().expect("assignment target");
          *phase = BinPhase::Store;
          Ok(StepOutcome::Do(Action::StoreReference(target, result)))
        }
        (BinPhase::Store, Feedback::Value(stored)) => {
          b.frames.pop();
          Ok(StepOutcome::Continue(Feedback::Value(stored)))
        }
        (_, Feedback::Completion(c)) => {
          b.frames.pop();
          Ok(StepOutcome::Continue(Feedback::Completion(c)))
        }
        _ => Err(unsupported("unexpected feedback for Binary")),
      }
    }

    Frame::Cond { node, started } => match feedback {
      Feedback::Start if !*started => {
        *started = true;
        let test = &node.get().stx.test;
        request_expr(test)
      }
      Feedback::Value(v) => {
        let expr = *node;
        let truthy = ev.to_boolean_pub(scope, v)?;
        b.frames.pop();
        let stx = &expr.get().stx;
        let branch = if truthy {
          &stx.consequent
        } else {
          &stx.alternate
        };
        request_expr(branch)
      }
      Feedback::Completion(c) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      _ => Err(unsupported("unexpected feedback for Cond")),
    },

    Frame::Call { node, phase, .. } => {
      let expr = *node;
      match (*phase, feedback) {
        (CallPhase::Callee, Feedback::Start) => {
          let callee = &expr.get().stx.callee;
          if expr_contains_suspend(callee) {
            return Err(unsupported("yield/await in call callee"));
          }
          Ok(StepOutcome::Do(Action::EvalCallee(NodeRef::new(callee))))
        }
        (CallPhase::Callee, Feedback::Callee { func: f, this: t }) => {
          // Optional call (`?.(`): short-circuit before evaluating arguments when callee is nullish.
          if expr.get().stx.optional_chaining && matches!(f, Value::Undefined | Value::Null) {
            b.frames.pop();
            return Ok(StepOutcome::Continue(Feedback::Value(Value::Undefined)));
          }
          if let Some(Frame::Call {
            func, this, phase, ..
          }) = b.frames.last_mut()
          {
            *func = f;
            *this = t;
            *phase = CallPhase::Args;
          }
          step_call_args(b)
        }
        (CallPhase::Args, Feedback::Value(v)) => {
          if let Some(Frame::Call { args, .. }) = b.frames.last_mut() {
            args.push(v);
          }
          step_call_args(b)
        }
        (CallPhase::Invoke, Feedback::Value(v)) => {
          b.frames.pop();
          Ok(StepOutcome::Continue(Feedback::Value(v)))
        }
        (_, Feedback::Completion(c)) => {
          b.frames.pop();
          Ok(StepOutcome::Continue(Feedback::Completion(c)))
        }
        _ => Err(unsupported("unexpected feedback for Call")),
      }
    }

    Frame::ArrayLit {
      finalizing, phase, ..
    } => match (*phase, feedback) {
      (ArrayLitPhase::Elements, Feedback::Start) => Ok(StepOutcome::Do(Action::ArrayNew)),
      (ArrayLitPhase::Elements, Feedback::Array(a)) => {
        if let Some(Frame::ArrayLit { arr, .. }) = b.frames.last_mut() {
          *arr = Some(a);
        }
        step_array_advance(b)
      }
      (ArrayLitPhase::Single, Feedback::Value(v)) => {
        let Some(Frame::ArrayLit {
          arr,
          next_index,
          elem_idx,
          phase,
          ..
        }) = b.frames.last_mut()
        else {
          return Err(unsupported("array frame vanished"));
        };
        let a = arr.expect("array literal object");
        let idx = *next_index;
        *next_index = idx + 1;
        *elem_idx += 1;
        *phase = ArrayLitPhase::Elements;
        Ok(StepOutcome::Do(Action::ArrayDefine(a, idx, v)))
      }
      (ArrayLitPhase::SpreadSource, Feedback::Value(v)) => {
        if let Some(Frame::ArrayLit { phase, .. }) = b.frames.last_mut() {
          *phase = ArrayLitPhase::SpreadGetIter;
        }
        Ok(StepOutcome::Do(Action::GetIterator(v)))
      }
      (ArrayLitPhase::SpreadGetIter, Feedback::Iterator(rec)) => {
        if let Some(Frame::ArrayLit {
          phase,
          spread_record,
          ..
        }) = b.frames.last_mut()
        {
          *spread_record = Some(rec);
          *phase = ArrayLitPhase::SpreadStep;
        }
        Ok(StepOutcome::Do(Action::IterStepValue(rec)))
      }
      (ArrayLitPhase::SpreadStep, Feedback::IterStep(rec, next)) => {
        let Some(Frame::ArrayLit {
          arr,
          next_index,
          elem_idx,
          phase,
          spread_record,
          ..
        }) = b.frames.last_mut()
        else {
          return Err(unsupported("array frame vanished"));
        };
        *spread_record = Some(rec);
        match next {
          Some(v) => {
            let a = arr.expect("array literal object");
            let idx = *next_index;
            *next_index = idx + 1;
            Ok(StepOutcome::Do(Action::ArrayDefine(a, idx, v)))
          }
          None => {
            *spread_record = None;
            *elem_idx += 1;
            *phase = ArrayLitPhase::Elements;
            step_array_advance(b)
          }
        }
      }
      (ArrayLitPhase::SpreadStep, Feedback::Done) => {
        let Some(Frame::ArrayLit { spread_record, .. }) = b.frames.last() else {
          return Err(unsupported("array frame vanished"));
        };
        let rec = spread_record.expect("spread iterator record");
        Ok(StepOutcome::Do(Action::IterStepValue(rec)))
      }
      (ArrayLitPhase::Elements, Feedback::Done) => {
        if *finalizing {
          let Some(Frame::ArrayLit { arr, .. }) = b.frames.last_mut() else {
            return Err(unsupported("array frame vanished"));
          };
          let a = arr.take().expect("array literal object");
          b.frames.pop();
          return Ok(StepOutcome::Continue(Feedback::Value(Value::Object(a))));
        }
        step_array_advance(b)
      }
      (_, Feedback::Completion(c)) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      _ => Err(unsupported("unexpected feedback for ArrayLit")),
    },

    Frame::ObjectLit { phase, .. } => match (*phase, feedback) {
      (ObjectLitPhase::Members, Feedback::Start) => Ok(StepOutcome::Do(Action::ObjectNew)),
      (ObjectLitPhase::Members, Feedback::Object(o)) => {
        if let Some(Frame::ObjectLit { obj, .. }) = b.frames.last_mut() {
          *obj = Some(o);
        }
        step_object_advance(b)
      }
      (ObjectLitPhase::Members, Feedback::Done) => step_object_advance(b),
      (ObjectLitPhase::PropKey, Feedback::Value(key)) => {
        if let Some(Frame::ObjectLit {
          phase, pending_key, ..
        }) = b.frames.last_mut()
        {
          *pending_key = Some(key);
          *phase = ObjectLitPhase::PropValueComputed;
        }
        let Some(Frame::ObjectLit {
          node, member_idx, ..
        }) = b.frames.last()
        else {
          return Err(unsupported("object frame vanished"));
        };
        let lit = *node;
        let idx = *member_idx;
        let ObjMemberType::Valued {
          val: ClassOrObjVal::Prop(Some(value_expr)),
          ..
        } = &lit.get().stx.members[idx].stx.typ
        else {
          return Err(unsupported("object prop value after computed key"));
        };
        request_expr(value_expr)
      }
      (ObjectLitPhase::PropValueDirect, Feedback::Value(v)) => {
        let Some(Frame::ObjectLit {
          node,
          member_idx,
          obj,
          phase,
          ..
        }) = b.frames.last_mut()
        else {
          return Err(unsupported("object frame vanished"));
        };
        let o = obj.expect("object literal object");
        let lit = *node;
        let idx = *member_idx;
        *member_idx += 1;
        *phase = ObjectLitPhase::Members;
        Ok(StepOutcome::Do(Action::ObjectDefineDirect(o, lit, idx, v)))
      }
      (ObjectLitPhase::PropValueComputed, Feedback::Value(v)) => {
        let Some(Frame::ObjectLit {
          member_idx,
          obj,
          phase,
          pending_key,
          ..
        }) = b.frames.last_mut()
        else {
          return Err(unsupported("object frame vanished"));
        };
        let o = obj.expect("object literal object");
        let key = pending_key.take().expect("computed key");
        *member_idx += 1;
        *phase = ObjectLitPhase::Members;
        Ok(StepOutcome::Do(Action::ObjectDefine(o, key, v)))
      }
      (ObjectLitPhase::SpreadSource, Feedback::Value(src)) => {
        let Some(Frame::ObjectLit {
          member_idx,
          obj,
          phase,
          ..
        }) = b.frames.last_mut()
        else {
          return Err(unsupported("object frame vanished"));
        };
        let o = obj.expect("object literal object");
        *member_idx += 1;
        *phase = ObjectLitPhase::Members;
        Ok(StepOutcome::Do(Action::ObjectSpread(o, src)))
      }
      (_, Feedback::Completion(c)) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      _ => Err(unsupported("unexpected feedback for ObjectLit")),
    },

    Frame::ComputedMember { phase, .. } => match (*phase, feedback) {
      (ComputedMemberPhase::Object, Feedback::Start) => {
        let Some(Frame::ComputedMember { node, .. }) = b.frames.last() else {
          return Err(unsupported("computed member frame vanished"));
        };
        let object = &node.get().stx.object;
        // Suspend-free optional-chain bases must use EvalChain so `a?.b.c` / `a?.b[x]` short-circuit
        // propagates (EvalExpr would collapse to `undefined` and then throw on the next link).
        if !expr_contains_suspend(object) && crate::exec::expr_contains_optional_link(object) {
          Ok(StepOutcome::Do(Action::EvalChain(NodeRef::new(object))))
        } else {
          request_expr(object)
        }
      }
      (ComputedMemberPhase::Object, Feedback::ShortCircuit) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Value(Value::Undefined)))
      }
      (ComputedMemberPhase::Object, Feedback::Value(base)) => {
        let (optional, member_node) = {
          let Some(Frame::ComputedMember { node, .. }) = b.frames.last() else {
            return Err(unsupported("computed member frame vanished"));
          };
          (
            node.get().stx.optional_chaining,
            NodeRef::new(&node.get().stx.member),
          )
        };
        if optional && matches!(base, Value::Undefined | Value::Null) {
          b.frames.pop();
          return Ok(StepOutcome::Continue(Feedback::Value(Value::Undefined)));
        }
        if let Some(Frame::ComputedMember { phase, object, .. }) = b.frames.last_mut() {
          *object = Some(base);
          *phase = ComputedMemberPhase::Key;
        }
        if !expr_contains_suspend(member_node.get()) {
          Ok(StepOutcome::Do(Action::EvalExpr(member_node)))
        } else {
          let frame = make_expr_frame(member_node.get())?;
          b.frames.push(frame);
          Ok(StepOutcome::Continue(Feedback::Start))
        }
      }
      (ComputedMemberPhase::Key, Feedback::Value(key)) => {
        let Some(Frame::ComputedMember { object, .. }) = b.frames.last_mut() else {
          return Err(unsupported("computed member frame vanished"));
        };
        let base = object.take().expect("computed member base");
        b.frames.pop();
        Ok(StepOutcome::Do(Action::GetComputed(base, key)))
      }
      (_, Feedback::Completion(c)) => {
        b.frames.pop();
        Ok(StepOutcome::Continue(Feedback::Completion(c)))
      }
      _ => Err(unsupported("unexpected feedback for ComputedMember")),
    },
  }
}

/// Route a try-block/catch completion through the finally block if present, else pop + re-emit.
fn finish_try_with_finally(
  _ev: &mut Evaluator<'_>,
  _scope: &mut Scope<'_>,
  b: &mut ResumableBody,
  c: Completion,
) -> Result<StepOutcome, VmError> {
  let Some(Frame::Try {
    node,
    phase,
    resume,
    ..
  }) = b.frames.last_mut()
  else {
    return Err(unsupported("finish_try on non-Try frame"));
  };
  let stmt = *node;
  match &stmt.get().stx.finally {
    Some(fin) => {
      *resume = Some(c);
      *phase = TryPhase::Finally;
      let list = ListRef::new(&fin.stx.body);
      b.frames.push(Frame::StmtList {
        list,
        idx: 0,
        last: None,
        needs_env: true,
        restore_env: None,
      });
      Ok(StepOutcome::Continue(Feedback::Start))
    }
    None => {
      b.frames.pop();
      Ok(StepOutcome::Continue(Feedback::Completion(c)))
    }
  }
}

fn for_triple_request_cond(
  stmt: NodeRef<ForTripleStmt>,
  phase: &mut ForTriplePhase,
) -> Result<StepOutcome, VmError> {
  *phase = ForTriplePhase::Cond;
  match &stmt.get().stx.cond {
    Some(cond) => {
      if !expr_contains_suspend(cond) {
        Ok(StepOutcome::Do(Action::EvalExpr(NodeRef::new(cond))))
      } else {
        Ok(StepOutcome::Push(make_expr_frame(cond)?))
      }
    }
    None => Ok(StepOutcome::Continue(Feedback::Value(Value::Bool(true)))),
  }
}

fn step_call_args(b: &mut ResumableBody) -> Result<StepOutcome, VmError> {
  let Some(Frame::Call {
    node,
    phase,
    func,
    this,
    args,
    arg_idx,
  }) = b.frames.last_mut()
  else {
    return Err(unsupported("call args on wrong frame"));
  };
  let expr = *node;
  let arguments = &expr.get().stx.arguments;
  if *arg_idx >= arguments.len() {
    *phase = CallPhase::Invoke;
    let f = *func;
    let t = *this;
    let a = std::mem::take(args);
    return Ok(StepOutcome::Do(Action::Call {
      func: f,
      this: t,
      args: a,
    }));
  }
  let arg = &arguments[*arg_idx];
  *arg_idx += 1;
  if arg.stx.spread {
    return Err(unsupported("yield/await alongside spread arguments"));
  }
  let value_node = &arg.stx.value;
  if !expr_contains_suspend(value_node) {
    Ok(StepOutcome::Do(Action::EvalExpr(NodeRef::new(value_node))))
  } else {
    let frame = make_expr_frame(value_node)?;
    b.frames.push(frame);
    Ok(StepOutcome::Continue(Feedback::Start))
  }
}

fn obj_member_contains_suspend(member: &ObjMemberType) -> bool {
  match member {
    ObjMemberType::Valued { key, val } => {
      let key_susp = match key {
        ClassOrObjKey::Computed(e) => expr_contains_suspend(e),
        ClassOrObjKey::Direct(_) => false,
      };
      let val_susp = match val {
        ClassOrObjVal::Prop(Some(e)) => expr_contains_suspend(e),
        // Getter/setter/method bodies are function boundaries.
        _ => false,
      };
      key_susp || val_susp
    }
    ObjMemberType::Shorthand { .. } => false,
    ObjMemberType::Rest { val } => expr_contains_suspend(val),
  }
}

fn step_object_advance(b: &mut ResumableBody) -> Result<StepOutcome, VmError> {
  let Some(Frame::ObjectLit {
    node,
    member_idx,
    obj,
    phase,
    pending_key,
  }) = b.frames.last_mut()
  else {
    return Err(unsupported("object advance on wrong frame"));
  };
  let lit = *node;
  let members = &lit.get().stx.members;
  if *member_idx >= members.len() {
    let o = obj.take().expect("object literal object");
    b.frames.pop();
    return Ok(StepOutcome::Continue(Feedback::Value(Value::Object(o))));
  }
  let idx = *member_idx;
  let member = &members[idx].stx.typ;
  if !obj_member_contains_suspend(member) {
    let o = obj.expect("object literal object");
    *phase = ObjectLitPhase::Members;
    *member_idx += 1;
    return Ok(StepOutcome::Do(Action::ObjectApplyMember(o, lit, idx)));
  }
  match member {
    ObjMemberType::Rest { val } => {
      *phase = ObjectLitPhase::SpreadSource;
      if !expr_contains_suspend(val) {
        Ok(StepOutcome::Do(Action::EvalExpr(NodeRef::new(val))))
      } else {
        let frame = make_expr_frame(val)?;
        b.frames.push(frame);
        Ok(StepOutcome::Continue(Feedback::Start))
      }
    }
    ObjMemberType::Valued {
      key: ClassOrObjKey::Direct(_),
      val: ClassOrObjVal::Prop(Some(value_expr)),
    } => {
      *phase = ObjectLitPhase::PropValueDirect;
      *pending_key = None;
      if !expr_contains_suspend(value_expr) {
        Ok(StepOutcome::Do(Action::EvalExpr(NodeRef::new(value_expr))))
      } else {
        let frame = make_expr_frame(value_expr)?;
        b.frames.push(frame);
        Ok(StepOutcome::Continue(Feedback::Start))
      }
    }
    ObjMemberType::Valued {
      key: ClassOrObjKey::Computed(key_expr),
      val: ClassOrObjVal::Prop(Some(_)),
    } => {
      *phase = ObjectLitPhase::PropKey;
      *pending_key = None;
      if !expr_contains_suspend(key_expr) {
        Ok(StepOutcome::Do(Action::EvalExpr(NodeRef::new(key_expr))))
      } else {
        let frame = make_expr_frame(key_expr)?;
        b.frames.push(frame);
        Ok(StepOutcome::Continue(Feedback::Start))
      }
    }
    _ => Err(unsupported(
      "yield/await in object literal method/accessor key position",
    )),
  }
}

fn step_array_advance(b: &mut ResumableBody) -> Result<StepOutcome, VmError> {
  let Some(Frame::ArrayLit {
    node,
    elem_idx,
    arr,
    next_index,
    finalizing,
    phase,
    ..
  }) = b.frames.last_mut()
  else {
    return Err(unsupported("array advance on wrong frame"));
  };
  let expr = *node;
  let elements = &expr.get().stx.elements;
  loop {
    if *elem_idx >= elements.len() {
      let a = arr.expect("array literal object");
      let len = *next_index;
      *finalizing = true;
      *phase = ArrayLitPhase::Elements;
      return Ok(StepOutcome::Do(Action::ArrayFinalize(a, len)));
    }
    match &elements[*elem_idx] {
      LitArrElem::Empty => {
        *next_index += 1;
        *elem_idx += 1;
      }
      LitArrElem::Rest(e) => {
        *phase = ArrayLitPhase::SpreadSource;
        if !expr_contains_suspend(e) {
          return Ok(StepOutcome::Do(Action::EvalExpr(NodeRef::new(e))));
        }
        let frame = make_expr_frame(e)?;
        b.frames.push(frame);
        return Ok(StepOutcome::Continue(Feedback::Start));
      }
      LitArrElem::Single(e) => {
        *phase = ArrayLitPhase::Single;
        if !expr_contains_suspend(e) {
          return Ok(StepOutcome::Do(Action::EvalExpr(NodeRef::new(e))));
        }
        let frame = make_expr_frame(e)?;
        b.frames.push(frame);
        return Ok(StepOutcome::Continue(Feedback::Start));
      }
    }
  }
}

/// Mirrors `LoopEvaluation`: an unlabelled `break` (or one targeting this loop's labels) is
/// consumed by the loop and becomes a normal completion.
fn normalize_loop_exit(c: Completion, label_set: &[String], v: Option<Value>) -> Completion {
  match c {
    Completion::Break(None, bv) => Completion::Normal(bv.or(v)),
    Completion::Break(Some(target), bv) if label_set.iter().any(|l| l == &target) => {
      Completion::Normal(bv.or(v))
    }
    other => other.update_empty(v),
  }
}

fn is_compound_assignment(op: OperatorName) -> bool {
  compound_base_op(op).is_some() || is_logical_assignment(op)
}

fn is_logical_assignment(op: OperatorName) -> bool {
  matches!(
    op,
    OperatorName::AssignmentLogicalAnd
      | OperatorName::AssignmentLogicalOr
      | OperatorName::AssignmentNullishCoalescing
  )
}

fn compound_base_op(op: OperatorName) -> Option<OperatorName> {
  Some(match op {
    OperatorName::AssignmentAddition => OperatorName::Addition,
    OperatorName::AssignmentSubtraction => OperatorName::Subtraction,
    OperatorName::AssignmentMultiplication => OperatorName::Multiplication,
    OperatorName::AssignmentDivision => OperatorName::Division,
    OperatorName::AssignmentRemainder => OperatorName::Remainder,
    OperatorName::AssignmentExponentiation => OperatorName::Exponentiation,
    OperatorName::AssignmentBitwiseAnd => OperatorName::BitwiseAnd,
    OperatorName::AssignmentBitwiseOr => OperatorName::BitwiseOr,
    OperatorName::AssignmentBitwiseXor => OperatorName::BitwiseXor,
    OperatorName::AssignmentBitwiseLeftShift => OperatorName::BitwiseLeftShift,
    OperatorName::AssignmentBitwiseRightShift => OperatorName::BitwiseRightShift,
    OperatorName::AssignmentBitwiseUnsignedRightShift => OperatorName::BitwiseUnsignedRightShift,
    _ => return None,
  })
}

fn is_simple_target(e: &Node<Expr>) -> bool {
  matches!(
    &*e.stx,
    Expr::Id(_) | Expr::IdPat(_) | Expr::Member(_) | Expr::ComputedMember(_)
  )
}
