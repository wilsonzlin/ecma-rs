use super::{OptCtx, Pass};
use parse_js::ast::class_or_object::{
  ClassMember, ClassOrObjKey, ClassOrObjVal, ObjMember, ObjMemberType,
};
use parse_js::ast::expr::jsx::{JsxAttr, JsxAttrVal, JsxElem, JsxElemChild};
use parse_js::ast::expr::lit::LitTemplatePart;
use parse_js::ast::expr::lit::{LitArrElem, LitBoolExpr, LitNullExpr, LitNumExpr, LitStrExpr};
use parse_js::ast::expr::pat::{ArrPat, ObjPat, Pat};
use parse_js::ast::expr::{BinaryExpr, Expr};
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::{Node, NodeAssocData};
use parse_js::ast::stmt::decl::{ParamDecl, VarDecl, VarDeclarator};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stmt::{
  CatchBlock, ForBody, ForInOfLhs, ForTripleStmtInit, SwitchBranch, TryStmt,
};
use parse_js::ast::stx::TopLevel;
use parse_js::char::{ECMASCRIPT_LINE_TERMINATORS, ECMASCRIPT_WHITESPACE};
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;
use std::cmp::Ordering;

pub(super) struct ConstFoldPass;

impl Pass for ConstFoldPass {
  fn name(&self) -> &'static str {
    "const-fold"
  }

  fn run(&mut self, _cx: &mut OptCtx, top: &mut Node<TopLevel>) -> bool {
    let mut changed = false;
    let body = std::mem::take(&mut top.stx.body);
    top.stx.body = fold_stmts(body, &mut changed);
    changed
  }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ExprCtx {
  Value,
  Condition,
}

#[derive(Clone, Copy, Debug)]
enum ConstVal<'a> {
  Undefined,
  Null,
  Bool(bool),
  Num(f64),
  Str(&'a str),
  BigInt(&'a str),
}

impl ConstVal<'_> {
  fn is_nullish(self) -> bool {
    matches!(self, ConstVal::Null | ConstVal::Undefined)
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

fn fold_stmts(stmts: Vec<Node<Stmt>>, changed: &mut bool) -> Vec<Node<Stmt>> {
  stmts
    .into_iter()
    .map(|stmt| fold_stmt(stmt, changed))
    .collect()
}

fn fold_stmt(stmt: Node<Stmt>, changed: &mut bool) -> Node<Stmt> {
  let Node { loc, assoc, stx } = stmt;
  match *stx {
    Stmt::Block(mut block) => {
      let body = std::mem::take(&mut block.stx.body);
      block.stx.body = fold_stmts(body, changed);
      new_node(loc, assoc, Stmt::Block(block))
    }
    Stmt::Expr(mut expr_stmt) => {
      expr_stmt.stx.expr = fold_expr(expr_stmt.stx.expr, ExprCtx::Value, changed);
      new_node(loc, assoc, Stmt::Expr(expr_stmt))
    }
    Stmt::If(mut if_stmt) => {
      if_stmt.stx.test = fold_expr(if_stmt.stx.test, ExprCtx::Condition, changed);
      if_stmt.stx.consequent = fold_stmt(if_stmt.stx.consequent, changed);
      if let Some(alt) = if_stmt.stx.alternate.take() {
        if_stmt.stx.alternate = Some(fold_stmt(alt, changed));
      }
      new_node(loc, assoc, Stmt::If(if_stmt))
    }
    Stmt::ForTriple(mut for_stmt) => {
      for_stmt.stx.init = match for_stmt.stx.init {
        ForTripleStmtInit::None => ForTripleStmtInit::None,
        ForTripleStmtInit::Expr(expr) => {
          ForTripleStmtInit::Expr(fold_expr(expr, ExprCtx::Value, changed))
        }
        ForTripleStmtInit::Decl(decl) => ForTripleStmtInit::Decl(fold_var_decl(decl, changed)),
      };
      if let Some(cond) = for_stmt.stx.cond.take() {
        for_stmt.stx.cond = Some(fold_expr(cond, ExprCtx::Condition, changed));
      }
      if let Some(post) = for_stmt.stx.post.take() {
        for_stmt.stx.post = Some(fold_expr(post, ExprCtx::Value, changed));
      }
      for_stmt.stx.body = fold_for_body(for_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::ForTriple(for_stmt))
    }
    Stmt::ForIn(mut for_stmt) => {
      for_stmt.stx.lhs = fold_for_in_of_lhs(for_stmt.stx.lhs, changed);
      for_stmt.stx.rhs = fold_expr(for_stmt.stx.rhs, ExprCtx::Value, changed);
      for_stmt.stx.body = fold_for_body(for_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::ForIn(for_stmt))
    }
    Stmt::ForOf(mut for_stmt) => {
      for_stmt.stx.lhs = fold_for_in_of_lhs(for_stmt.stx.lhs, changed);
      for_stmt.stx.rhs = fold_expr(for_stmt.stx.rhs, ExprCtx::Value, changed);
      for_stmt.stx.body = fold_for_body(for_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::ForOf(for_stmt))
    }
    Stmt::While(mut while_stmt) => {
      while_stmt.stx.condition = fold_expr(while_stmt.stx.condition, ExprCtx::Condition, changed);
      while_stmt.stx.body = fold_stmt(while_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::While(while_stmt))
    }
    Stmt::DoWhile(mut do_stmt) => {
      do_stmt.stx.body = fold_stmt(do_stmt.stx.body, changed);
      do_stmt.stx.condition = fold_expr(do_stmt.stx.condition, ExprCtx::Condition, changed);
      new_node(loc, assoc, Stmt::DoWhile(do_stmt))
    }
    Stmt::Switch(mut switch_stmt) => {
      switch_stmt.stx.test = fold_expr(switch_stmt.stx.test, ExprCtx::Value, changed);
      let branches = std::mem::take(&mut switch_stmt.stx.branches);
      switch_stmt.stx.branches = branches
        .into_iter()
        .map(|branch| fold_switch_branch(branch, changed))
        .collect();
      new_node(loc, assoc, Stmt::Switch(switch_stmt))
    }
    Stmt::Try(mut try_stmt) => {
      fold_try_stmt(&mut try_stmt, changed);
      new_node(loc, assoc, Stmt::Try(try_stmt))
    }
    Stmt::Throw(mut throw_stmt) => {
      throw_stmt.stx.value = fold_expr(throw_stmt.stx.value, ExprCtx::Value, changed);
      new_node(loc, assoc, Stmt::Throw(throw_stmt))
    }
    Stmt::Return(mut ret_stmt) => {
      if let Some(value) = ret_stmt.stx.value.take() {
        ret_stmt.stx.value = Some(fold_expr(value, ExprCtx::Value, changed));
      }
      new_node(loc, assoc, Stmt::Return(ret_stmt))
    }
    Stmt::With(mut with_stmt) => {
      with_stmt.stx.object = fold_expr(with_stmt.stx.object, ExprCtx::Value, changed);
      with_stmt.stx.body = fold_stmt(with_stmt.stx.body, changed);
      new_node(loc, assoc, Stmt::With(with_stmt))
    }
    Stmt::Label(mut label_stmt) => {
      label_stmt.stx.statement = fold_stmt(label_stmt.stx.statement, changed);
      new_node(loc, assoc, Stmt::Label(label_stmt))
    }
    Stmt::VarDecl(decl) => new_node(loc, assoc, Stmt::VarDecl(fold_var_decl(decl, changed))),
    Stmt::FunctionDecl(mut decl) => {
      fold_func(&mut decl.stx.function, changed);
      new_node(loc, assoc, Stmt::FunctionDecl(decl))
    }
    Stmt::ClassDecl(mut decl) => {
      for decorator in decl.stx.decorators.iter_mut() {
        let owned = std::mem::replace(&mut decorator.stx.expression, dummy_expr());
        decorator.stx.expression = fold_expr(owned, ExprCtx::Value, changed);
      }
      if let Some(extends) = decl.stx.extends.take() {
        decl.stx.extends = Some(fold_expr(extends, ExprCtx::Value, changed));
      }
      for imp in decl.stx.implements.iter_mut() {
        let owned = std::mem::replace(imp, dummy_expr());
        *imp = fold_expr(owned, ExprCtx::Value, changed);
      }
      for member in decl.stx.members.iter_mut() {
        fold_class_member(member, changed);
      }
      new_node(loc, assoc, Stmt::ClassDecl(decl))
    }
    Stmt::ExportDefaultExpr(mut expr) => {
      expr.stx.expression = fold_expr(expr.stx.expression, ExprCtx::Value, changed);
      new_node(loc, assoc, Stmt::ExportDefaultExpr(expr))
    }
    Stmt::Import(mut import) => {
      if let Some(attrs) = import.stx.attributes.take() {
        import.stx.attributes = Some(fold_expr(attrs, ExprCtx::Value, changed));
      }
      new_node(loc, assoc, Stmt::Import(import))
    }
    Stmt::ExportList(mut export_stmt) => {
      if let Some(attrs) = export_stmt.stx.attributes.take() {
        export_stmt.stx.attributes = Some(fold_expr(attrs, ExprCtx::Value, changed));
      }
      new_node(loc, assoc, Stmt::ExportList(export_stmt))
    }
    // No expressions to fold.
    other => new_node(loc, assoc, other),
  }
}

fn fold_switch_branch(branch: Node<SwitchBranch>, changed: &mut bool) -> Node<SwitchBranch> {
  let mut branch = branch;
  if let Some(case) = branch.stx.case.take() {
    branch.stx.case = Some(fold_expr(case, ExprCtx::Value, changed));
  }
  let body = std::mem::take(&mut branch.stx.body);
  branch.stx.body = fold_stmts(body, changed);
  branch
}

fn fold_try_stmt(try_stmt: &mut Node<TryStmt>, changed: &mut bool) {
  let wrapped = std::mem::take(&mut try_stmt.stx.wrapped.stx.body);
  try_stmt.stx.wrapped.stx.body = fold_stmts(wrapped, changed);

  if let Some(catch) = try_stmt.stx.catch.as_mut() {
    fold_catch_block(catch, changed);
  }

  if let Some(finally) = try_stmt.stx.finally.as_mut() {
    let body = std::mem::take(&mut finally.stx.body);
    finally.stx.body = fold_stmts(body, changed);
  }
}

fn fold_catch_block(catch: &mut Node<CatchBlock>, changed: &mut bool) {
  if let Some(param) = catch.stx.parameter.as_mut() {
    let pat = std::mem::replace(&mut param.stx.pat, dummy_pat());
    param.stx.pat = fold_pat(pat, changed);
  }
  let body = std::mem::take(&mut catch.stx.body);
  catch.stx.body = fold_stmts(body, changed);
}

fn fold_for_body(body: Node<ForBody>, changed: &mut bool) -> Node<ForBody> {
  let mut body = body;
  let stmts = std::mem::take(&mut body.stx.body);
  body.stx.body = fold_stmts(stmts, changed);
  body
}

fn fold_for_in_of_lhs(lhs: ForInOfLhs, changed: &mut bool) -> ForInOfLhs {
  match lhs {
    ForInOfLhs::Assign(pat) => ForInOfLhs::Assign(fold_pat(pat, changed)),
    ForInOfLhs::Decl((mode, mut pat_decl)) => {
      let pat = std::mem::replace(&mut pat_decl.stx.pat, dummy_pat());
      pat_decl.stx.pat = fold_pat(pat, changed);
      ForInOfLhs::Decl((mode, pat_decl))
    }
  }
}

fn fold_var_decl(mut decl: Node<VarDecl>, changed: &mut bool) -> Node<VarDecl> {
  for declarator in decl.stx.declarators.iter_mut() {
    fold_var_declarator(declarator, changed);
  }
  decl
}

fn fold_var_declarator(decl: &mut VarDeclarator, changed: &mut bool) {
  let pat = std::mem::replace(&mut decl.pattern.stx.pat, dummy_pat());
  decl.pattern.stx.pat = fold_pat(pat, changed);
  if let Some(init) = decl.initializer.take() {
    decl.initializer = Some(fold_expr(init, ExprCtx::Value, changed));
  }
}

fn fold_pat(pat: Node<Pat>, changed: &mut bool) -> Node<Pat> {
  let Node { loc, assoc, stx } = pat;
  match *stx {
    Pat::Id(id) => new_node(loc, assoc, Pat::Id(id)),
    Pat::AssignTarget(expr) => new_node(
      loc,
      assoc,
      Pat::AssignTarget(fold_expr(expr, ExprCtx::Value, changed)),
    ),
    Pat::Arr(arr) => new_node(loc, assoc, Pat::Arr(fold_arr_pat(arr, changed))),
    Pat::Obj(obj) => new_node(loc, assoc, Pat::Obj(fold_obj_pat(obj, changed))),
  }
}

fn fold_arr_pat(mut pat: Node<ArrPat>, changed: &mut bool) -> Node<ArrPat> {
  for elem in pat.stx.elements.iter_mut() {
    let Some(elem) = elem.as_mut() else {
      continue;
    };
    let target = std::mem::replace(&mut elem.target, dummy_pat());
    elem.target = fold_pat(target, changed);
    if let Some(default) = elem.default_value.take() {
      elem.default_value = Some(fold_expr(default, ExprCtx::Value, changed));
    }
  }
  if let Some(rest) = pat.stx.rest.as_mut() {
    let owned = std::mem::replace(rest, dummy_pat());
    *rest = fold_pat(owned, changed);
  }
  pat
}

fn fold_obj_pat(mut pat: Node<ObjPat>, changed: &mut bool) -> Node<ObjPat> {
  for prop in pat.stx.properties.iter_mut() {
    match &mut prop.stx.key {
      ClassOrObjKey::Computed(expr) => {
        let owned = std::mem::replace(expr, dummy_expr());
        *expr = fold_expr(owned, ExprCtx::Value, changed);
      }
      ClassOrObjKey::Direct(_) => {}
    }
    let target = std::mem::replace(&mut prop.stx.target, dummy_pat());
    prop.stx.target = fold_pat(target, changed);
    if let Some(default) = prop.stx.default_value.take() {
      prop.stx.default_value = Some(fold_expr(default, ExprCtx::Value, changed));
    }
  }
  if let Some(rest) = pat.stx.rest.as_mut() {
    let owned = std::mem::replace(rest, dummy_pat());
    *rest = fold_pat(owned, changed);
  }
  pat
}

fn fold_class_member(member: &mut Node<ClassMember>, changed: &mut bool) {
  for decorator in member.stx.decorators.iter_mut() {
    let owned = std::mem::replace(&mut decorator.stx.expression, dummy_expr());
    decorator.stx.expression = fold_expr(owned, ExprCtx::Value, changed);
  }
  match &mut member.stx.key {
    ClassOrObjKey::Computed(expr) => {
      let owned = std::mem::replace(expr, dummy_expr());
      *expr = fold_expr(owned, ExprCtx::Value, changed);
    }
    ClassOrObjKey::Direct(_) => {}
  }
  fold_class_or_obj_val(&mut member.stx.val, changed);
}

fn fold_obj_member(member: &mut Node<ObjMember>, changed: &mut bool) {
  match &mut member.stx.typ {
    ObjMemberType::Valued { key, val } => {
      match key {
        ClassOrObjKey::Computed(expr) => {
          let owned = std::mem::replace(expr, dummy_expr());
          *expr = fold_expr(owned, ExprCtx::Value, changed);
        }
        ClassOrObjKey::Direct(_) => {}
      }
      fold_class_or_obj_val(val, changed);
    }
    ObjMemberType::Shorthand { .. } => {}
    ObjMemberType::Rest { val } => {
      let owned = std::mem::replace(val, dummy_expr());
      *val = fold_expr(owned, ExprCtx::Value, changed);
    }
  }
}

fn fold_class_or_obj_val(val: &mut ClassOrObjVal, changed: &mut bool) {
  match val {
    ClassOrObjVal::Getter(get) => fold_func(&mut get.stx.func, changed),
    ClassOrObjVal::Setter(set) => fold_func(&mut set.stx.func, changed),
    ClassOrObjVal::Method(method) => fold_func(&mut method.stx.func, changed),
    ClassOrObjVal::Prop(init) => {
      if let Some(init) = init.as_mut() {
        let owned = std::mem::replace(init, dummy_expr());
        *init = fold_expr(owned, ExprCtx::Value, changed);
      }
    }
    ClassOrObjVal::StaticBlock(block) => {
      let body = std::mem::take(&mut block.stx.body);
      block.stx.body = fold_stmts(body, changed);
    }
    ClassOrObjVal::IndexSignature(_) => {}
  }
}

fn fold_func(func: &mut Node<Func>, changed: &mut bool) {
  for param in func.stx.parameters.iter_mut() {
    fold_param(param, changed);
  }
  if let Some(body) = func.stx.body.take() {
    func.stx.body = Some(match body {
      FuncBody::Block(stmts) => FuncBody::Block(fold_stmts(stmts, changed)),
      FuncBody::Expression(expr) => FuncBody::Expression(fold_expr(expr, ExprCtx::Value, changed)),
    });
  }
}

fn fold_param(param: &mut Node<ParamDecl>, changed: &mut bool) {
  let pat = std::mem::replace(&mut param.stx.pattern.stx.pat, dummy_pat());
  param.stx.pattern.stx.pat = fold_pat(pat, changed);
  if let Some(default) = param.stx.default_value.take() {
    param.stx.default_value = Some(fold_expr(default, ExprCtx::Value, changed));
  }
  for decorator in param.stx.decorators.iter_mut() {
    let owned = std::mem::replace(&mut decorator.stx.expression, dummy_expr());
    decorator.stx.expression = fold_expr(owned, ExprCtx::Value, changed);
  }
}

fn fold_expr(expr: Node<Expr>, ctx: ExprCtx, changed: &mut bool) -> Node<Expr> {
  let Node { loc, assoc, stx } = expr;
  match *stx {
    Expr::Binary(mut bin) => {
      let op = bin.stx.operator;
      let child_ctx = if ctx == ExprCtx::Condition
        && matches!(op, OperatorName::LogicalAnd | OperatorName::LogicalOr)
      {
        ExprCtx::Condition
      } else {
        ExprCtx::Value
      };
      bin.stx.left = fold_expr(bin.stx.left, child_ctx, changed);
      bin.stx.right = fold_expr(bin.stx.right, child_ctx, changed);

      if let Some(folded) = fold_binary_expr(&mut bin.stx, ctx, changed, loc) {
        return folded;
      }
      new_node(loc, assoc, Expr::Binary(bin))
    }
    Expr::Unary(mut unary) => {
      unary.stx.argument = fold_expr(unary.stx.argument, ExprCtx::Value, changed);
      if unary.stx.operator == OperatorName::LogicalNot {
        if let Some(value) = const_truthiness(&unary.stx.argument) {
          *changed = true;
          return new_node(
            loc,
            assoc,
            Expr::LitBool(Node::new(loc, LitBoolExpr { value: !value })),
          );
        }
      }
      if unary.stx.operator == OperatorName::Typeof {
        if let Some(arg) = const_val(&unary.stx.argument) {
          *changed = true;
          return new_node(
            loc,
            assoc,
            Expr::LitStr(Node::new(
              loc,
              LitStrExpr {
                value: const_typeof(arg).to_string(),
              },
            )),
          );
        }
      }
      new_node(loc, assoc, Expr::Unary(unary))
    }
    Expr::Cond(mut cond) => {
      cond.stx.test = fold_expr(cond.stx.test, ExprCtx::Condition, changed);
      cond.stx.consequent = fold_expr(cond.stx.consequent, ctx, changed);
      cond.stx.alternate = fold_expr(cond.stx.alternate, ctx, changed);
      if let Some(value) = const_truthiness(&cond.stx.test) {
        *changed = true;
        return if value {
          cond.stx.consequent
        } else {
          cond.stx.alternate
        };
      }
      new_node(loc, assoc, Expr::Cond(cond))
    }
    Expr::Call(mut call) => {
      call.stx.callee = fold_expr(call.stx.callee, ExprCtx::Value, changed);
      let args = std::mem::take(&mut call.stx.arguments);
      call.stx.arguments = args
        .into_iter()
        .map(|mut arg| {
          arg.stx.value = fold_expr(arg.stx.value, ExprCtx::Value, changed);
          arg
        })
        .collect();
      new_node(loc, assoc, Expr::Call(call))
    }
    Expr::ArrowFunc(mut arrow) => {
      fold_func(&mut arrow.stx.func, changed);
      new_node(loc, assoc, Expr::ArrowFunc(arrow))
    }
    Expr::Func(mut func) => {
      fold_func(&mut func.stx.func, changed);
      new_node(loc, assoc, Expr::Func(func))
    }
    Expr::Class(mut class) => {
      if let Some(extends) = class.stx.extends.take() {
        class.stx.extends = Some(fold_expr(extends, ExprCtx::Value, changed));
      }
      for decorator in class.stx.decorators.iter_mut() {
        let owned = std::mem::replace(&mut decorator.stx.expression, dummy_expr());
        decorator.stx.expression = fold_expr(owned, ExprCtx::Value, changed);
      }
      for member in class.stx.members.iter_mut() {
        fold_class_member(member, changed);
      }
      new_node(loc, assoc, Expr::Class(class))
    }
    Expr::ComputedMember(mut member) => {
      member.stx.object = fold_expr(member.stx.object, ExprCtx::Value, changed);
      member.stx.member = fold_expr(member.stx.member, ExprCtx::Value, changed);
      new_node(loc, assoc, Expr::ComputedMember(member))
    }
    Expr::Member(mut member) => {
      member.stx.left = fold_expr(member.stx.left, ExprCtx::Value, changed);
      new_node(loc, assoc, Expr::Member(member))
    }
    Expr::TaggedTemplate(mut tagged) => {
      tagged.stx.function = fold_expr(tagged.stx.function, ExprCtx::Value, changed);
      for part in tagged.stx.parts.iter_mut() {
        if let LitTemplatePart::Substitution(expr) = part {
          let owned = std::mem::replace(expr, dummy_expr());
          *expr = fold_expr(owned, ExprCtx::Value, changed);
        }
      }
      new_node(loc, assoc, Expr::TaggedTemplate(tagged))
    }
    Expr::LitArr(mut arr) => {
      for elem in arr.stx.elements.iter_mut() {
        match elem {
          LitArrElem::Single(expr) | LitArrElem::Rest(expr) => {
            let owned = std::mem::replace(expr, dummy_expr());
            *expr = fold_expr(owned, ExprCtx::Value, changed);
          }
          LitArrElem::Empty => {}
        }
      }
      new_node(loc, assoc, Expr::LitArr(arr))
    }
    Expr::LitObj(mut obj) => {
      for member in obj.stx.members.iter_mut() {
        fold_obj_member(member, changed);
      }
      new_node(loc, assoc, Expr::LitObj(obj))
    }
    Expr::LitTemplate(mut tpl) => {
      for part in tpl.stx.parts.iter_mut() {
        if let LitTemplatePart::Substitution(expr) = part {
          let owned = std::mem::replace(expr, dummy_expr());
          *expr = fold_expr(owned, ExprCtx::Value, changed);
        }
      }
      new_node(loc, assoc, Expr::LitTemplate(tpl))
    }
    Expr::JsxElem(mut elem) => {
      elem = fold_jsx_elem(elem, changed);
      new_node(loc, assoc, Expr::JsxElem(elem))
    }
    Expr::JsxExprContainer(mut container) => {
      container.stx.value = fold_expr(container.stx.value, ExprCtx::Value, changed);
      new_node(loc, assoc, Expr::JsxExprContainer(container))
    }
    Expr::JsxSpreadAttr(mut spread) => {
      spread.stx.value = fold_expr(spread.stx.value, ExprCtx::Value, changed);
      new_node(loc, assoc, Expr::JsxSpreadAttr(spread))
    }
    Expr::Import(mut import) => {
      import.stx.module = fold_expr(import.stx.module, ExprCtx::Value, changed);
      if let Some(attrs) = import.stx.attributes.take() {
        import.stx.attributes = Some(fold_expr(attrs, ExprCtx::Value, changed));
      }
      new_node(loc, assoc, Expr::Import(import))
    }
    // Pattern expressions.
    Expr::ArrPat(pat) => new_node(loc, assoc, Expr::ArrPat(fold_arr_pat(pat, changed))),
    Expr::ObjPat(pat) => new_node(loc, assoc, Expr::ObjPat(fold_obj_pat(pat, changed))),
    // Everything else is already a leaf, or TS-only syntax that should be
    // erased before we reach this pass.
    other => new_node(loc, assoc, other),
  }
}

fn fold_jsx_elem(mut elem: Node<JsxElem>, changed: &mut bool) -> Node<JsxElem> {
  for attr in elem.stx.attributes.iter_mut() {
    match attr {
      JsxAttr::Named { value, .. } => match value {
        Some(JsxAttrVal::Expression(expr)) => {
          let owned = std::mem::replace(&mut expr.stx.value, dummy_expr());
          expr.stx.value = fold_expr(owned, ExprCtx::Value, changed);
        }
        Some(JsxAttrVal::Element(el)) => {
          let owned = std::mem::replace(el, dummy_jsx_elem());
          *el = fold_jsx_elem(owned, changed);
        }
        _ => {}
      },
      JsxAttr::Spread { value } => {
        let owned = std::mem::replace(&mut value.stx.value, dummy_expr());
        value.stx.value = fold_expr(owned, ExprCtx::Value, changed);
      }
    }
  }
  for child in elem.stx.children.iter_mut() {
    match child {
      JsxElemChild::Element(el) => {
        let owned = std::mem::replace(el, dummy_jsx_elem());
        *el = fold_jsx_elem(owned, changed);
      }
      JsxElemChild::Expr(expr) => {
        let owned = std::mem::replace(&mut expr.stx.value, dummy_expr());
        expr.stx.value = fold_expr(owned, ExprCtx::Value, changed);
      }
      JsxElemChild::Text(_) => {}
    }
  }
  elem
}

fn fold_binary_expr(
  bin: &mut BinaryExpr,
  ctx: ExprCtx,
  changed: &mut bool,
  loc: Loc,
) -> Option<Node<Expr>> {
  use OperatorName::*;

  match bin.operator {
    Addition => {
      if let (Some(ConstVal::Num(l)), Some(ConstVal::Num(r))) =
        (const_val(&bin.left), const_val(&bin.right))
      {
        *changed = true;
        return Some(Node::new(
          loc,
          Expr::LitNum(Node::new(
            loc,
            LitNumExpr {
              value: JsNumber(l + r),
            },
          )),
        ));
      }

      if let (Some(l), Some(r)) = (const_val(&bin.left), const_val(&bin.right)) {
        // JS `+` becomes string concatenation if either operand is a string.
        // This fold is conservative: we only handle known primitive constants.
        if let (ConstVal::Str(l), other) = (l, r) {
          *changed = true;
          return Some(Node::new(
            loc,
            Expr::LitStr(Node::new(
              loc,
              LitStrExpr {
                value: format!("{l}{}", const_to_string(other)?),
              },
            )),
          ));
        }
        if let (other, ConstVal::Str(r)) = (l, r) {
          *changed = true;
          return Some(Node::new(
            loc,
            Expr::LitStr(Node::new(
              loc,
              LitStrExpr {
                value: format!("{}{r}", const_to_string(other)?),
              },
            )),
          ));
        }
      }

      if let (Some(ConstVal::Str(l)), Some(ConstVal::Str(r))) =
        (const_val(&bin.left), const_val(&bin.right))
      {
        *changed = true;
        return Some(Node::new(
          loc,
          Expr::LitStr(Node::new(
            loc,
            LitStrExpr {
              value: format!("{l}{r}"),
            },
          )),
        ));
      }
    }
    Subtraction | Multiplication | Division | Remainder | Exponentiation => {
      if let (Some(ConstVal::Num(l)), Some(ConstVal::Num(r))) =
        (const_val(&bin.left), const_val(&bin.right))
      {
        let result = match bin.operator {
          Subtraction => l - r,
          Multiplication => l * r,
          Division => l / r,
          Remainder => l % r,
          Exponentiation => l.powf(r),
          _ => unreachable!(),
        };
        *changed = true;
        return Some(Node::new(
          loc,
          Expr::LitNum(Node::new(
            loc,
            LitNumExpr {
              value: JsNumber(result),
            },
          )),
        ));
      }
    }
    BitwiseAnd
    | BitwiseOr
    | BitwiseXor
    | BitwiseLeftShift
    | BitwiseRightShift
    | BitwiseUnsignedRightShift => {
      if let (Some(ConstVal::Num(l)), Some(ConstVal::Num(r))) =
        (const_val(&bin.left), const_val(&bin.right))
      {
        let result = match bin.operator {
          BitwiseAnd => (js_to_int32(l) & js_to_int32(r)) as f64,
          BitwiseOr => (js_to_int32(l) | js_to_int32(r)) as f64,
          BitwiseXor => (js_to_int32(l) ^ js_to_int32(r)) as f64,
          BitwiseLeftShift => {
            let shift = (js_to_uint32(r) & 0x1f) as u32;
            js_to_int32(l).wrapping_shl(shift) as f64
          }
          BitwiseRightShift => {
            let shift = (js_to_uint32(r) & 0x1f) as u32;
            js_to_int32(l).wrapping_shr(shift) as f64
          }
          BitwiseUnsignedRightShift => {
            let shift = (js_to_uint32(r) & 0x1f) as u32;
            js_to_uint32(l).wrapping_shr(shift) as f64
          }
          _ => unreachable!(),
        };
        *changed = true;
        return Some(Node::new(
          loc,
          Expr::LitNum(Node::new(
            loc,
            LitNumExpr {
              value: JsNumber(result),
            },
          )),
        ));
      }
    }
    LessThan | LessThanOrEqual | GreaterThan | GreaterThanOrEqual => {
      if let (Some(l), Some(r)) = (const_val(&bin.left), const_val(&bin.right)) {
        if matches!(l, ConstVal::BigInt(_)) || matches!(r, ConstVal::BigInt(_)) {
          return None;
        }
        let result = if let (ConstVal::Str(l), ConstVal::Str(r)) = (l, r) {
          let ord = js_str_cmp(l, r);
          match bin.operator {
            LessThan => ord.is_lt(),
            LessThanOrEqual => ord.is_le(),
            GreaterThan => ord.is_gt(),
            GreaterThanOrEqual => ord.is_ge(),
            _ => unreachable!(),
          }
        } else {
          let l = const_to_number(l)?;
          let r = const_to_number(r)?;
          match bin.operator {
            LessThan => l < r,
            LessThanOrEqual => l <= r,
            GreaterThan => l > r,
            GreaterThanOrEqual => l >= r,
            _ => unreachable!(),
          }
        };
        *changed = true;
        return Some(Node::new(
          loc,
          Expr::LitBool(Node::new(loc, LitBoolExpr { value: result })),
        ));
      }
    }
    StrictEquality | StrictInequality | Equality | Inequality => {
      if let (Some(l), Some(r)) = (const_val(&bin.left), const_val(&bin.right)) {
        let eq = match bin.operator {
          StrictEquality | StrictInequality => Some(js_strict_eq(l, r)),
          Equality | Inequality => js_loose_eq(l, r),
          _ => None,
        }?;
        let value = match bin.operator {
          StrictInequality | Inequality => !eq,
          _ => eq,
        };
        *changed = true;
        return Some(Node::new(
          loc,
          Expr::LitBool(Node::new(loc, LitBoolExpr { value })),
        ));
      }
    }
    NullishCoalescing => {
      if let Some(l) = const_val(&bin.left) {
        *changed = true;
        return Some(if l.is_nullish() {
          std::mem::replace(&mut bin.right, dummy_expr())
        } else {
          std::mem::replace(&mut bin.left, dummy_expr())
        });
      }
    }
    LogicalAnd => {
      if let Some(left_truthy) = const_truthiness(&bin.left) {
        *changed = true;
        return Some(if left_truthy {
          std::mem::replace(&mut bin.right, dummy_expr())
        } else {
          std::mem::replace(&mut bin.left, dummy_expr())
        });
      }
      if ctx == ExprCtx::Condition && is_lit_true(&bin.right) {
        *changed = true;
        return Some(std::mem::replace(&mut bin.left, dummy_expr()));
      }
    }
    LogicalOr => {
      if let Some(left_truthy) = const_truthiness(&bin.left) {
        *changed = true;
        return Some(if left_truthy {
          std::mem::replace(&mut bin.left, dummy_expr())
        } else {
          std::mem::replace(&mut bin.right, dummy_expr())
        });
      }
      if ctx == ExprCtx::Condition && is_lit_false(&bin.right) {
        *changed = true;
        return Some(std::mem::replace(&mut bin.left, dummy_expr()));
      }
    }
    _ => {}
  }
  None
}

fn const_truthiness(expr: &Node<Expr>) -> Option<bool> {
  let v = const_val(expr)?;
  Some(match v {
    ConstVal::Undefined | ConstVal::Null => false,
    ConstVal::Bool(b) => b,
    ConstVal::Num(n) => n != 0.0 && !n.is_nan(),
    ConstVal::Str(s) => !s.is_empty(),
    ConstVal::BigInt(b) => b != "0",
  })
}

fn is_lit_true(expr: &Node<Expr>) -> bool {
  matches!(expr.stx.as_ref(), Expr::LitBool(b) if b.stx.value)
}

fn is_lit_false(expr: &Node<Expr>) -> bool {
  matches!(expr.stx.as_ref(), Expr::LitBool(b) if !b.stx.value)
}

fn dummy_pat() -> Node<Pat> {
  Node::new(Loc(0, 0), Pat::Id(dummy_id_pat()))
}

fn dummy_id_pat() -> Node<parse_js::ast::expr::pat::IdPat> {
  Node::new(
    Loc(0, 0),
    parse_js::ast::expr::pat::IdPat {
      name: String::new(),
    },
  )
}

fn dummy_expr() -> Node<Expr> {
  Node::new(
    Loc(0, 0),
    Expr::LitNull(Node::new(Loc(0, 0), LitNullExpr {})),
  )
}

fn dummy_jsx_elem() -> Node<JsxElem> {
  Node::new(
    Loc(0, 0),
    JsxElem {
      name: None,
      attributes: Vec::new(),
      children: Vec::new(),
    },
  )
}

fn const_val(expr: &Node<Expr>) -> Option<ConstVal<'_>> {
  match expr.stx.as_ref() {
    Expr::LitNull(_) => Some(ConstVal::Null),
    Expr::LitBool(b) => Some(ConstVal::Bool(b.stx.value)),
    Expr::LitNum(n) => Some(ConstVal::Num(n.stx.value.0)),
    Expr::LitStr(s) => Some(ConstVal::Str(s.stx.value.as_str())),
    Expr::LitBigInt(b) => Some(ConstVal::BigInt(b.stx.value.as_str())),
    Expr::Unary(unary)
      if unary.stx.operator == OperatorName::Void && is_safe_void_arg(&unary.stx.argument) =>
    {
      Some(ConstVal::Undefined)
    }
    _ => None,
  }
}

fn is_safe_void_arg(expr: &Node<Expr>) -> bool {
  match expr.stx.as_ref() {
    Expr::LitNull(_)
    | Expr::LitBool(_)
    | Expr::LitNum(_)
    | Expr::LitStr(_)
    | Expr::LitBigInt(_) => true,
    _ => false,
  }
}

fn const_typeof(val: ConstVal<'_>) -> &'static str {
  match val {
    ConstVal::Undefined => "undefined",
    ConstVal::Null => "object",
    ConstVal::Bool(_) => "boolean",
    ConstVal::Num(_) => "number",
    ConstVal::Str(_) => "string",
    ConstVal::BigInt(_) => "bigint",
  }
}

fn js_strict_eq(a: ConstVal<'_>, b: ConstVal<'_>) -> bool {
  match (a, b) {
    (ConstVal::Undefined, ConstVal::Undefined) => true,
    (ConstVal::Null, ConstVal::Null) => true,
    (ConstVal::Bool(a), ConstVal::Bool(b)) => a == b,
    (ConstVal::Num(a), ConstVal::Num(b)) => !a.is_nan() && !b.is_nan() && a == b,
    (ConstVal::Str(a), ConstVal::Str(b)) => a == b,
    (ConstVal::BigInt(a), ConstVal::BigInt(b)) => a == b,
    _ => false,
  }
}

fn js_loose_eq(a: ConstVal<'_>, b: ConstVal<'_>) -> Option<bool> {
  // Keep this conservative; only fold cases we can model for primitives without
  // throwing (notably excluding BigInt comparisons for now).
  match (a, b) {
    (ConstVal::BigInt(_), _) | (_, ConstVal::BigInt(_)) => None,
    (ConstVal::Undefined, ConstVal::Null) | (ConstVal::Null, ConstVal::Undefined) => Some(true),
    // Same-type comparisons fall back to strict equality semantics.
    (a, b) if matches!((a, b), (ConstVal::Undefined, ConstVal::Undefined))
      || matches!((a, b), (ConstVal::Null, ConstVal::Null))
      || matches!((a, b), (ConstVal::Bool(_), ConstVal::Bool(_)))
      || matches!((a, b), (ConstVal::Num(_), ConstVal::Num(_)))
      || matches!((a, b), (ConstVal::Str(_), ConstVal::Str(_))) =>
    {
      Some(js_strict_eq(a, b))
    }
    (ConstVal::Num(l), ConstVal::Str(r)) => Some(l == coerce_str_to_num(r)),
    (ConstVal::Str(l), ConstVal::Num(r)) => Some(coerce_str_to_num(l) == r),
    (ConstVal::Bool(l), r) => js_loose_eq(ConstVal::Num(if l { 1.0 } else { 0.0 }), r),
    (l, ConstVal::Bool(r)) => js_loose_eq(l, ConstVal::Num(if r { 1.0 } else { 0.0 })),
    // All remaining primitive pairs in our supported subset are false.
    _ => Some(false),
  }
}

fn const_to_number(val: ConstVal<'_>) -> Option<f64> {
  Some(match val {
    ConstVal::Undefined => f64::NAN,
    ConstVal::Null => 0.0,
    ConstVal::Bool(b) => {
      if b {
        1.0
      } else {
        0.0
      }
    }
    ConstVal::Num(n) => n,
    ConstVal::Str(s) => coerce_str_to_num(s),
    ConstVal::BigInt(_) => return None,
  })
}

fn const_to_string(val: ConstVal<'_>) -> Option<String> {
  Some(match val {
    ConstVal::Undefined => "undefined".to_string(),
    ConstVal::Null => "null".to_string(),
    ConstVal::Bool(b) => {
      if b {
        "true".to_string()
      } else {
        "false".to_string()
      }
    }
    ConstVal::Num(n) => js_number_to_string(n),
    ConstVal::Str(s) => s.to_string(),
    ConstVal::BigInt(s) => s.to_string(),
  })
}

fn js_to_uint32(n: f64) -> u32 {
  if !n.is_finite() || n == 0.0 {
    return 0;
  }
  let int = n.trunc();
  let wrapped = int.rem_euclid(4294967296.0);
  wrapped as u32
}

fn js_to_int32(n: f64) -> i32 {
  js_to_uint32(n) as i32
}

fn js_str_cmp(a: &str, b: &str) -> Ordering {
  let mut a = a.encode_utf16();
  let mut b = b.encode_utf16();
  loop {
    match (a.next(), b.next()) {
      (Some(a), Some(b)) => match a.cmp(&b) {
        Ordering::Equal => {}
        other => return other,
      },
      (None, Some(_)) => return Ordering::Less,
      (Some(_), None) => return Ordering::Greater,
      (None, None) => return Ordering::Equal,
    }
  }
}

fn is_ecmascript_whitespace(ch: char) -> bool {
  ECMASCRIPT_WHITESPACE.contains(&ch) || ECMASCRIPT_LINE_TERMINATORS.contains(&ch)
}

fn trim_js_whitespace(raw: &str) -> &str {
  raw.trim_matches(is_ecmascript_whitespace)
}

fn parse_int_digits_to_f64(digits: &str, radix: u32) -> Option<f64> {
  use num_bigint::BigUint;

  if digits.is_empty() || digits.contains('_') {
    return None;
  }
  if !digits.chars().all(|ch| ch.to_digit(radix).is_some()) {
    return None;
  }
  let bigint = BigUint::parse_bytes(digits.as_bytes(), radix)?;
  let decimal = bigint.to_str_radix(10);
  Some(decimal.parse::<f64>().unwrap_or(f64::NAN))
}

// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number#number_coercion
fn coerce_str_to_num(raw: &str) -> f64 {
  let raw = trim_js_whitespace(raw);
  if raw.is_empty() {
    return 0.0;
  };
  let mut sign = 1.0_f64;
  let mut had_sign = false;
  let mut body = raw;
  if let Some(rest) = body.strip_prefix('+') {
    had_sign = true;
    body = rest;
  } else if let Some(rest) = body.strip_prefix('-') {
    had_sign = true;
    sign = -1.0;
    body = rest;
  };
  if body.is_empty() {
    return f64::NAN;
  };
  if body == "Infinity" {
    return sign * f64::INFINITY;
  };

  let parse_int = |digits: &str, radix: u32| parse_int_digits_to_f64(digits, radix);

  if body.starts_with("0x") || body.starts_with("0X") {
    if had_sign {
      return f64::NAN;
    }
    return parse_int(&body[2..], 16).unwrap_or(f64::NAN);
  }
  if body.starts_with("0b") || body.starts_with("0B") {
    if had_sign {
      return f64::NAN;
    }
    return parse_int(&body[2..], 2).unwrap_or(f64::NAN);
  }
  if body.starts_with("0o") || body.starts_with("0O") {
    if had_sign {
      return f64::NAN;
    }
    return parse_int(&body[2..], 8).unwrap_or(f64::NAN);
  }

  if body.contains('_') {
    return f64::NAN;
  }

  // Validate the decimal/exponent grammar; Rust's float parser accepts strings
  // that JS treats as NaN (e.g. "inf").
  let mut saw_digit_before_exp = false;
  let mut saw_dot = false;
  let mut saw_exp = false;
  let mut iter = body.chars().peekable();
  while let Some(ch) = iter.next() {
    match ch {
      '0'..='9' => {
        if !saw_exp {
          saw_digit_before_exp = true;
        }
      }
      '.' => {
        if saw_dot || saw_exp {
          return f64::NAN;
        }
        saw_dot = true;
      }
      'e' | 'E' => {
        if saw_exp || !saw_digit_before_exp {
          return f64::NAN;
        }
        saw_exp = true;
        if matches!(iter.peek(), Some('+' | '-')) {
          iter.next();
        }
        let mut exp_digits = 0;
        while matches!(iter.peek(), Some('0'..='9')) {
          exp_digits += 1;
          iter.next();
        }
        if exp_digits == 0 {
          return f64::NAN;
        }
      }
      _ => return f64::NAN,
    }
  }
  if !saw_digit_before_exp {
    return f64::NAN;
  }

  body.parse::<f64>().map(|v| sign * v).unwrap_or(f64::NAN)
}

// https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-tostring
fn js_number_to_string(n: f64) -> String {
  if n.is_nan() {
    return "NaN".to_string();
  }
  if n == 0.0 {
    // Covers both +0 and -0.
    return "0".to_string();
  }
  if n.is_infinite() {
    if n.is_sign_negative() {
      return "-Infinity".to_string();
    } else {
      return "Infinity".to_string();
    }
  }

  let sign = if n.is_sign_negative() { "-" } else { "" };
  let abs = n.abs();
  // `JsNumber` uses ryu for the digit+exponent decomposition we need.
  let raw = JsNumber(abs).to_string();
  let (digits, exp) = parse_ryu_to_decimal(&raw);
  let k = exp + digits.len() as i32;

  let mut out = String::new();
  out.push_str(sign);

  if k > 0 && k <= 21 {
    let k = k as usize;
    if k >= digits.len() {
      out.push_str(&digits);
      out.extend(std::iter::repeat('0').take(k - digits.len()));
    } else {
      out.push_str(&digits[..k]);
      out.push('.');
      out.push_str(&digits[k..]);
    }
    return out;
  }

  if k <= 0 && k > -6 {
    out.push_str("0.");
    out.extend(std::iter::repeat('0').take((-k) as usize));
    out.push_str(&digits);
    return out;
  }

  // Exponential form.
  let first = digits.as_bytes()[0] as char;
  out.push(first);
  if digits.len() > 1 {
    out.push('.');
    out.push_str(&digits[1..]);
  }
  out.push('e');
  let exp = k - 1;
  if exp >= 0 {
    out.push('+');
    out.push_str(&exp.to_string());
  } else {
    out.push('-');
    out.push_str(&(-exp).to_string());
  }
  out
}

fn parse_ryu_to_decimal(raw: &str) -> (String, i32) {
  // `raw` is expected to be ASCII and contain either:
  // - digits with optional decimal point
  // - digits with optional decimal point and a trailing `e[+-]?\d+`
  //
  // Returns `(digits, exp)` such that `value = digits × 10^exp` and `digits`
  // contains no leading zeros.
  let (mantissa, exp_part) = match raw.split_once('e') {
    Some((mantissa, exp)) => (mantissa, Some(exp)),
    None => (raw, None),
  };

  let mut exp: i32 = exp_part.map_or(0, |e| e.parse().unwrap_or(0));

  let mut digits = String::with_capacity(mantissa.len());
  if let Some((int_part, frac_part)) = mantissa.split_once('.') {
    digits.push_str(int_part);
    digits.push_str(frac_part);
    exp -= frac_part.len() as i32;
  } else {
    digits.push_str(mantissa);
  }

  // Strip leading zeros introduced by `0.xxx` forms.
  let trimmed = digits.trim_start_matches('0');
  // `raw` comes from a non-zero number, so we should always have digits.
  (trimmed.to_string(), exp)
}
