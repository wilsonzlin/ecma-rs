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
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;

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
      if let (Some(l), Some(r)) = (as_num(&bin.left), as_num(&bin.right)) {
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
      if let (Some(l), Some(r)) = (as_str(&bin.left), as_str(&bin.right)) {
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
      if let (Some(l), Some(r)) = (as_num(&bin.left), as_num(&bin.right)) {
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
  match expr.stx.as_ref() {
    Expr::LitBool(b) => Some(b.stx.value),
    Expr::LitNull(_) => Some(false),
    Expr::LitNum(n) => Some(n.stx.value.0 != 0.0 && !n.stx.value.0.is_nan()),
    Expr::LitStr(s) => Some(!s.stx.value.is_empty()),
    Expr::LitBigInt(b) => Some(b.stx.value != "0"),
    _ => None,
  }
}

fn as_num(expr: &Node<Expr>) -> Option<f64> {
  match expr.stx.as_ref() {
    Expr::LitNum(n) => Some(n.stx.value.0),
    _ => None,
  }
}

fn as_str(expr: &Node<Expr>) -> Option<&str> {
  match expr.stx.as_ref() {
    Expr::LitStr(s) => Some(s.stx.value.as_str()),
    _ => None,
  }
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
