use crate::Diagnostic;
use derive_visitor::{Drive, DriveMut};
use diagnostics::{FileId, Span};
use parse_js::ast::class_or_object::{
  ClassMember, ClassOrObjKey, ClassOrObjVal, ObjMember, ObjMemberType,
};
use parse_js::ast::expr::jsx::*;
use parse_js::ast::expr::lit::LitNullExpr;
use parse_js::ast::expr::lit::{LitArrElem, LitTemplatePart};
use parse_js::ast::expr::pat::{ArrPat, IdPat, ObjPat, Pat};
use parse_js::ast::expr::*;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::import_export::{ExportNames, ImportNames};
use parse_js::ast::node::{Node, NodeAssocData};
use parse_js::ast::stmt::decl::{ClassDecl, FuncDecl, ParamDecl, VarDecl, VarDeclarator};
use parse_js::ast::stmt::*;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::EnumDecl;
use parse_js::loc::Loc;

const ERR_TS_UNSUPPORTED: &str = "MINIFYTS0001";

fn new_node<T: Drive + DriveMut>(loc: Loc, assoc: NodeAssocData, stx: T) -> Node<T> {
  Node {
    loc,
    assoc,
    stx: Box::new(stx),
  }
}

fn dummy_expr() -> Node<Expr> {
  Node::new(
    Loc(0, 0),
    Expr::LitNull(Node::new(Loc(0, 0), LitNullExpr {})),
  )
}

fn dummy_pat() -> Node<Pat> {
  Node::new(
    Loc(0, 0),
    Pat::Id(Node::new(
      Loc(0, 0),
      IdPat {
        name: String::new(),
      },
    )),
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

fn take_expr(expr: &mut Node<Expr>) -> Node<Expr> {
  std::mem::replace(expr, dummy_expr())
}

fn take_pat(pat: &mut Node<Pat>) -> Node<Pat> {
  std::mem::replace(pat, dummy_pat())
}

fn take_jsx_elem(elem: &mut Node<JsxElem>) -> Node<JsxElem> {
  std::mem::replace(elem, dummy_jsx_elem())
}

pub fn erase_types(file: FileId, top_level: &mut Node<TopLevel>) -> Result<(), Vec<Diagnostic>> {
  let mut diagnostics = Vec::new();
  strip_stmts(&mut top_level.stx.body, file, &mut diagnostics);
  if diagnostics.is_empty() {
    Ok(())
  } else {
    Err(diagnostics)
  }
}

fn strip_stmts(stmts: &mut Vec<Node<Stmt>>, file: FileId, diagnostics: &mut Vec<Diagnostic>) {
  let mut new_stmts = Vec::with_capacity(stmts.len());
  for stmt in stmts.drain(..) {
    if let Some(stripped) = strip_stmt(stmt, file, diagnostics) {
      new_stmts.push(stripped);
    }
  }
  *stmts = new_stmts;
}

fn strip_stmt(
  stmt: Node<Stmt>,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> Option<Node<Stmt>> {
  let loc = stmt.loc;
  let assoc = stmt.assoc;
  match *stmt.stx {
    Stmt::Block(block) => {
      let mut block = block;
      strip_stmts(&mut block.stx.body, file, diagnostics);
      Some(new_node(loc, assoc, Stmt::Block(block)))
    }
    Stmt::Expr(expr_stmt) => {
      let mut expr_stmt = expr_stmt;
      expr_stmt.stx.expr = strip_expr(expr_stmt.stx.expr, file, diagnostics);
      Some(new_node(loc, assoc, Stmt::Expr(expr_stmt)))
    }
    Stmt::If(mut if_stmt) => {
      if_stmt.stx.test = strip_expr(if_stmt.stx.test, file, diagnostics);
      if_stmt.stx.consequent = strip_stmt(if_stmt.stx.consequent, file, diagnostics)?;
      if let Some(alt) = if_stmt.stx.alternate.take() {
        if_stmt.stx.alternate = strip_stmt(alt, file, diagnostics);
      }
      Some(new_node(loc, assoc, Stmt::If(if_stmt)))
    }
    Stmt::ForTriple(mut for_stmt) => {
      match &mut for_stmt.stx.init {
        ForTripleStmtInit::Expr(expr) => {
          let owned = take_expr(expr);
          *expr = strip_expr(owned, file, diagnostics);
        }
        ForTripleStmtInit::Decl(decl) => strip_var_decl(&mut decl.stx, file, diagnostics),
        ForTripleStmtInit::None => {}
      }
      if let Some(cond) = for_stmt.stx.cond.take() {
        for_stmt.stx.cond = Some(strip_expr(cond, file, diagnostics));
      }
      if let Some(post) = for_stmt.stx.post.take() {
        for_stmt.stx.post = Some(strip_expr(post, file, diagnostics));
      }
      strip_for_body(&mut for_stmt.stx.body, file, diagnostics);
      Some(new_node(loc, assoc, Stmt::ForTriple(for_stmt)))
    }
    Stmt::ForIn(mut for_stmt) => {
      strip_for_in_of_lhs(&mut for_stmt.stx.lhs, file, diagnostics);
      for_stmt.stx.rhs = strip_expr(for_stmt.stx.rhs, file, diagnostics);
      strip_for_body(&mut for_stmt.stx.body, file, diagnostics);
      Some(new_node(loc, assoc, Stmt::ForIn(for_stmt)))
    }
    Stmt::ForOf(mut for_stmt) => {
      strip_for_in_of_lhs(&mut for_stmt.stx.lhs, file, diagnostics);
      for_stmt.stx.rhs = strip_expr(for_stmt.stx.rhs, file, diagnostics);
      strip_for_body(&mut for_stmt.stx.body, file, diagnostics);
      Some(new_node(loc, assoc, Stmt::ForOf(for_stmt)))
    }
    Stmt::While(mut while_stmt) => {
      while_stmt.stx.condition = strip_expr(while_stmt.stx.condition, file, diagnostics);
      while_stmt.stx.body = strip_stmt(while_stmt.stx.body, file, diagnostics)?;
      Some(new_node(loc, assoc, Stmt::While(while_stmt)))
    }
    Stmt::DoWhile(mut do_stmt) => {
      do_stmt.stx.body = strip_stmt(do_stmt.stx.body, file, diagnostics)?;
      do_stmt.stx.condition = strip_expr(do_stmt.stx.condition, file, diagnostics);
      Some(new_node(loc, assoc, Stmt::DoWhile(do_stmt)))
    }
    Stmt::Switch(mut switch_stmt) => {
      switch_stmt.stx.test = strip_expr(switch_stmt.stx.test, file, diagnostics);
      let mut new_branches = Vec::with_capacity(switch_stmt.stx.branches.len());
      for branch in switch_stmt.stx.branches.drain(..) {
        new_branches.push(strip_switch_branch(branch, file, diagnostics));
      }
      switch_stmt.stx.branches = new_branches;
      Some(new_node(loc, assoc, Stmt::Switch(switch_stmt)))
    }
    Stmt::Try(mut try_stmt) => {
      try_stmt.stx.wrapped = strip_block(try_stmt.stx.wrapped, file, diagnostics);
      if let Some(catch) = try_stmt.stx.catch.take() {
        try_stmt.stx.catch = Some(strip_catch(catch, file, diagnostics));
      }
      if let Some(finally) = try_stmt.stx.finally.take() {
        try_stmt.stx.finally = Some(strip_block(finally, file, diagnostics));
      }
      Some(new_node(loc, assoc, Stmt::Try(try_stmt)))
    }
    Stmt::Throw(mut throw_stmt) => {
      throw_stmt.stx.value = strip_expr(throw_stmt.stx.value, file, diagnostics);
      Some(new_node(loc, assoc, Stmt::Throw(throw_stmt)))
    }
    Stmt::Return(mut ret_stmt) => {
      if let Some(value) = ret_stmt.stx.value.take() {
        ret_stmt.stx.value = Some(strip_expr(value, file, diagnostics));
      }
      Some(new_node(loc, assoc, Stmt::Return(ret_stmt)))
    }
    Stmt::Break(_) | Stmt::Continue(_) | Stmt::Debugger(_) | Stmt::Empty(_) => {
      Some(new_node(loc, assoc, *stmt.stx))
    }
    Stmt::With(mut with_stmt) => {
      with_stmt.stx.object = strip_expr(with_stmt.stx.object, file, diagnostics);
      with_stmt.stx.body = strip_stmt(with_stmt.stx.body, file, diagnostics)?;
      Some(new_node(loc, assoc, Stmt::With(with_stmt)))
    }
    Stmt::Label(mut label_stmt) => {
      label_stmt.stx.statement = strip_stmt(label_stmt.stx.statement, file, diagnostics)?;
      Some(new_node(loc, assoc, Stmt::Label(label_stmt)))
    }
    Stmt::VarDecl(mut decl) => {
      strip_var_decl(&mut decl.stx, file, diagnostics);
      Some(new_node(loc, assoc, Stmt::VarDecl(decl)))
    }
    Stmt::FunctionDecl(func_decl) => strip_func_decl(func_decl, loc, assoc, file, diagnostics),
    Stmt::ClassDecl(class_decl) => strip_class_decl(class_decl, loc, assoc, file, diagnostics),
    Stmt::Import(import_stmt) => strip_import(import_stmt, loc, assoc, file, diagnostics),
    Stmt::ExportList(export_stmt) => strip_export_list(export_stmt, loc, assoc),
    Stmt::ExportDefaultExpr(mut expr) => {
      expr.stx.expression = strip_expr(expr.stx.expression, file, diagnostics);
      Some(new_node(loc, assoc, Stmt::ExportDefaultExpr(expr)))
    }
    Stmt::InterfaceDecl(_)
    | Stmt::TypeAliasDecl(_)
    | Stmt::ImportTypeDecl(_)
    | Stmt::ExportTypeDecl(_)
    | Stmt::AmbientVarDecl(_)
    | Stmt::AmbientFunctionDecl(_)
    | Stmt::AmbientClassDecl(_)
    | Stmt::GlobalDecl(_) => None,
    Stmt::EnumDecl(decl) => strip_enum_decl(decl, loc, assoc, file, diagnostics),
    Stmt::NamespaceDecl(decl) => {
      if decl.stx.declare {
        None
      } else {
        unsupported_ts(
          file,
          loc,
          "namespaces with runtime bodies are not supported",
          diagnostics,
        );
        None
      }
    }
    Stmt::ModuleDecl(decl) => {
      if decl.stx.declare {
        None
      } else {
        unsupported_ts(
          file,
          loc,
          "modules with runtime bodies are not supported",
          diagnostics,
        );
        None
      }
    }
    Stmt::ImportEqualsDecl(decl) => {
      if decl.stx.export {
        unsupported_ts(
          file,
          loc,
          "import= assignments with exports are not supported",
          diagnostics,
        );
      } else {
        unsupported_ts(
          file,
          loc,
          "import= assignments are not supported",
          diagnostics,
        );
      }
      None
    }
    Stmt::ExportAssignmentDecl(_) => {
      unsupported_ts(
        file,
        loc,
        "export = assignments are not supported",
        diagnostics,
      );
      None
    }
  }
}

fn strip_func_decl(
  func_decl: Node<FuncDecl>,
  loc: Loc,
  assoc: NodeAssocData,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> Option<Node<Stmt>> {
  let mut func_decl = func_decl;
  if !strip_func(&mut func_decl.stx.function.stx, file, diagnostics) {
    return None;
  }
  Some(new_node(loc, assoc, Stmt::FunctionDecl(func_decl)))
}

fn strip_class_decl(
  class_decl: Node<ClassDecl>,
  loc: Loc,
  assoc: NodeAssocData,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> Option<Node<Stmt>> {
  let mut class_decl = class_decl;
  if class_decl.stx.declare {
    return None;
  }
  class_decl.stx.abstract_ = false;
  class_decl.stx.type_parameters = None;
  class_decl.stx.implements.clear();
  if let Some(extends) = class_decl.stx.extends.take() {
    class_decl.stx.extends = Some(strip_expr(extends, file, diagnostics));
  }
  for decorator in &mut class_decl.stx.decorators {
    let expr = take_expr(&mut decorator.stx.expression);
    decorator.stx.expression = strip_expr(expr, file, diagnostics);
  }
  strip_class_members(&mut class_decl.stx.members, file, diagnostics);
  Some(new_node(loc, assoc, Stmt::ClassDecl(class_decl)))
}

fn strip_import(
  import_stmt: Node<ImportStmt>,
  loc: Loc,
  assoc: NodeAssocData,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> Option<Node<Stmt>> {
  let mut import_stmt = import_stmt;
  if import_stmt.stx.type_only {
    return None;
  }
  if let Some(names) = import_stmt.stx.names.as_mut() {
    match names {
      ImportNames::Specific(list) => {
        list.retain(|entry| !entry.stx.type_only);
        for entry in list.iter_mut() {
          entry.stx.type_only = false;
          let pat = take_pat(&mut entry.stx.alias.stx.pat);
          entry.stx.alias.stx.pat = strip_pat(pat, file, diagnostics);
        }
        if list.is_empty() {
          import_stmt.stx.names = None;
        }
      }
      ImportNames::All(pat) => {
        let pat_node = take_pat(&mut pat.stx.pat);
        pat.stx.pat = strip_pat(pat_node, file, diagnostics);
      }
    }
  }
  if let Some(default) = import_stmt.stx.default.as_mut() {
    let pat = take_pat(&mut default.stx.pat);
    default.stx.pat = strip_pat(pat, file, diagnostics);
  }
  if import_stmt.stx.default.is_none() && import_stmt.stx.names.is_none() {
    None
  } else {
    Some(new_node(loc, assoc, Stmt::Import(import_stmt)))
  }
}

fn strip_export_list(
  export_stmt: Node<ExportListStmt>,
  loc: Loc,
  assoc: NodeAssocData,
) -> Option<Node<Stmt>> {
  let mut export_stmt = export_stmt;
  if export_stmt.stx.type_only {
    return None;
  }
  match &mut export_stmt.stx.names {
    ExportNames::Specific(names) => {
      names.retain(|name| !name.stx.type_only);
      for name in names.iter_mut() {
        name.stx.type_only = false;
      }
      if names.is_empty() {
        return None;
      }
    }
    ExportNames::All(_) => {}
  }
  Some(new_node(loc, assoc, Stmt::ExportList(export_stmt)))
}

fn strip_enum_decl(
  decl: Node<EnumDecl>,
  loc: Loc,
  _assoc: NodeAssocData,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> Option<Node<Stmt>> {
  if decl.stx.declare || decl.stx.const_ {
    None
  } else {
    unsupported_ts(
      file,
      loc,
      "runtime enums are not supported in JS erasure",
      diagnostics,
    );
    None
  }
}

fn strip_switch_branch(
  branch: Node<SwitchBranch>,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> Node<SwitchBranch> {
  let mut branch = branch;
  if let Some(case) = branch.stx.case.take() {
    branch.stx.case = Some(strip_expr(case, file, diagnostics));
  }
  strip_stmts(&mut branch.stx.body, file, diagnostics);
  branch
}

fn strip_catch(
  mut catch: Node<CatchBlock>,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> Node<CatchBlock> {
  catch.stx.type_annotation = None;
  if let Some(param) = catch.stx.parameter.as_mut() {
    let pat = take_pat(&mut param.stx.pat);
    param.stx.pat = strip_pat(pat, file, diagnostics);
  }
  strip_stmts(&mut catch.stx.body, file, diagnostics);
  catch
}

fn strip_for_body(body: &mut Node<ForBody>, file: FileId, diagnostics: &mut Vec<Diagnostic>) {
  strip_stmts(&mut body.stx.body, file, diagnostics);
}

fn strip_block(
  block: Node<BlockStmt>,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> Node<BlockStmt> {
  let mut block = block;
  strip_stmts(&mut block.stx.body, file, diagnostics);
  block
}

fn strip_for_in_of_lhs(lhs: &mut ForInOfLhs, file: FileId, diagnostics: &mut Vec<Diagnostic>) {
  match lhs {
    ForInOfLhs::Assign(pat) => {
      let owned = take_pat(pat);
      *pat = strip_pat(owned, file, diagnostics);
    }
    ForInOfLhs::Decl((_, pat)) => {
      let owned = take_pat(&mut pat.stx.pat);
      pat.stx.pat = strip_pat(owned, file, diagnostics);
    }
  }
}

fn strip_var_decl(decl: &mut VarDecl, file: FileId, diagnostics: &mut Vec<Diagnostic>) {
  for declarator in decl.declarators.iter_mut() {
    strip_var_declarator(declarator, file, diagnostics);
  }
}

fn strip_var_declarator(decl: &mut VarDeclarator, file: FileId, diagnostics: &mut Vec<Diagnostic>) {
  decl.type_annotation = None;
  decl.definite_assignment = false;
  let pat = take_pat(&mut decl.pattern.stx.pat);
  decl.pattern.stx.pat = strip_pat(pat, file, diagnostics);
  if let Some(init) = decl.initializer.take() {
    decl.initializer = Some(strip_expr(init, file, diagnostics));
  }
}

fn strip_func(func: &mut Func, file: FileId, diagnostics: &mut Vec<Diagnostic>) -> bool {
  func.type_parameters = None;
  func.return_type = None;
  func
    .parameters
    .iter_mut()
    .for_each(|param| strip_param(param, file, diagnostics));
  match func.body.take() {
    Some(FuncBody::Block(body)) => {
      let mut block = body;
      strip_stmts(&mut block, file, diagnostics);
      func.body = Some(FuncBody::Block(block));
      true
    }
    Some(FuncBody::Expression(expr)) => {
      func.body = Some(FuncBody::Expression(strip_expr(expr, file, diagnostics)));
      true
    }
    None => false,
  }
}

fn strip_param(param: &mut Node<ParamDecl>, file: FileId, diagnostics: &mut Vec<Diagnostic>) {
  param.stx.optional = false;
  param.stx.accessibility = None;
  param.stx.readonly = false;
  param.stx.type_annotation = None;
  let pat = take_pat(&mut param.stx.pattern.stx.pat);
  param.stx.pattern.stx.pat = strip_pat(pat, file, diagnostics);
  if let Some(default) = param.stx.default_value.take() {
    param.stx.default_value = Some(strip_expr(default, file, diagnostics));
  }
  for decorator in &mut param.stx.decorators {
    let expr = take_expr(&mut decorator.stx.expression);
    decorator.stx.expression = strip_expr(expr, file, diagnostics);
  }
}

fn strip_pat(pat: Node<Pat>, file: FileId, diagnostics: &mut Vec<Diagnostic>) -> Node<Pat> {
  let Node { loc, assoc, stx } = pat;
  match *stx {
    Pat::Arr(arr) => new_node(loc, assoc, Pat::Arr(strip_arr_pat(arr, file, diagnostics))),
    Pat::Obj(obj) => new_node(loc, assoc, Pat::Obj(strip_obj_pat(obj, file, diagnostics))),
    Pat::AssignTarget(expr) => new_node(
      loc,
      assoc,
      Pat::AssignTarget(strip_expr(expr, file, diagnostics)),
    ),
    Pat::Id(_) => Node { loc, assoc, stx },
  }
}

fn strip_arr_pat(
  pat: Node<ArrPat>,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> Node<ArrPat> {
  let mut pat = pat;
  for elem in pat.stx.elements.iter_mut() {
    if let Some(elem) = elem {
      let target = take_pat(&mut elem.target);
      elem.target = strip_pat(target, file, diagnostics);
      if let Some(default) = elem.default_value.take() {
        elem.default_value = Some(strip_expr(default, file, diagnostics));
      }
    }
  }
  if let Some(rest) = pat.stx.rest.as_mut() {
    let rest_pat = take_pat(rest);
    *rest = strip_pat(rest_pat, file, diagnostics);
  }
  pat
}

fn strip_obj_pat(
  pat: Node<ObjPat>,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> Node<ObjPat> {
  let mut pat = pat;
  for prop in pat.stx.properties.iter_mut() {
    let target = take_pat(&mut prop.stx.target);
    prop.stx.target = strip_pat(target, file, diagnostics);
    if let Some(default) = prop.stx.default_value.take() {
      prop.stx.default_value = Some(strip_expr(default, file, diagnostics));
    }
  }
  if let Some(rest) = pat.stx.rest.as_mut() {
    let rest_pat = take_pat(rest);
    *rest = strip_pat(rest_pat, file, diagnostics);
  }
  pat
}

fn strip_expr(expr: Node<Expr>, file: FileId, diagnostics: &mut Vec<Diagnostic>) -> Node<Expr> {
  let loc = expr.loc;
  let assoc = expr.assoc;
  match *expr.stx {
    Expr::ArrowFunc(func) => {
      let mut func = func;
      strip_func(&mut func.stx.func.stx, file, diagnostics);
      new_node(loc, assoc, Expr::ArrowFunc(func))
    }
    Expr::Binary(mut bin) => {
      bin.stx.left = strip_expr(bin.stx.left, file, diagnostics);
      bin.stx.right = strip_expr(bin.stx.right, file, diagnostics);
      new_node(loc, assoc, Expr::Binary(bin))
    }
    Expr::Call(mut call) => {
      call.stx.callee = strip_expr(call.stx.callee, file, diagnostics);
      for arg in call.stx.arguments.iter_mut() {
        let value = take_expr(&mut arg.stx.value);
        arg.stx.value = strip_expr(value, file, diagnostics);
      }
      new_node(loc, assoc, Expr::Call(call))
    }
    Expr::Class(class) => new_node(
      loc,
      assoc,
      Expr::Class(strip_class_expr(class, file, diagnostics)),
    ),
    Expr::ComputedMember(mut member) => {
      member.stx.object = strip_expr(member.stx.object, file, diagnostics);
      member.stx.member = strip_expr(member.stx.member, file, diagnostics);
      new_node(loc, assoc, Expr::ComputedMember(member))
    }
    Expr::Cond(mut cond) => {
      cond.stx.test = strip_expr(cond.stx.test, file, diagnostics);
      cond.stx.consequent = strip_expr(cond.stx.consequent, file, diagnostics);
      cond.stx.alternate = strip_expr(cond.stx.alternate, file, diagnostics);
      new_node(loc, assoc, Expr::Cond(cond))
    }
    Expr::Func(mut func) => {
      strip_func(&mut func.stx.func.stx, file, diagnostics);
      new_node(loc, assoc, Expr::Func(func))
    }
    Expr::Id(_)
    | Expr::ImportMeta(_)
    | Expr::NewTarget(_)
    | Expr::Super(_)
    | Expr::This(_)
    | Expr::JsxName(_)
    | Expr::JsxText(_)
    | Expr::LitBool(_)
    | Expr::LitNull(_)
    | Expr::LitNum(_)
    | Expr::LitBigInt(_)
    | Expr::LitRegex(_)
    | Expr::LitStr(_)
    | Expr::IdPat(_)
    | Expr::JsxMember(_) => new_node(loc, assoc, *expr.stx),
    Expr::Import(mut import) => {
      import.stx.module = strip_expr(import.stx.module, file, diagnostics);
      if let Some(attrs) = import.stx.attributes.take() {
        import.stx.attributes = Some(strip_expr(attrs, file, diagnostics));
      }
      new_node(loc, assoc, Expr::Import(import))
    }
    Expr::Member(mut member) => {
      member.stx.left = strip_expr(member.stx.left, file, diagnostics);
      new_node(loc, assoc, Expr::Member(member))
    }
    Expr::TaggedTemplate(mut tagged) => {
      tagged.stx.function = strip_expr(tagged.stx.function, file, diagnostics);
      for part in tagged.stx.parts.iter_mut() {
        if let LitTemplatePart::Substitution(expr) = part {
          let inner = take_expr(expr);
          *expr = strip_expr(inner, file, diagnostics);
        }
      }
      new_node(loc, assoc, Expr::TaggedTemplate(tagged))
    }
    Expr::Unary(mut unary) => {
      unary.stx.argument = strip_expr(unary.stx.argument, file, diagnostics);
      new_node(loc, assoc, Expr::Unary(unary))
    }
    Expr::UnaryPostfix(mut unary) => {
      unary.stx.argument = strip_expr(unary.stx.argument, file, diagnostics);
      new_node(loc, assoc, Expr::UnaryPostfix(unary))
    }
    Expr::JsxElem(elem) => new_node(
      loc,
      assoc,
      Expr::JsxElem(strip_jsx_elem(elem, file, diagnostics)),
    ),
    Expr::JsxExprContainer(mut expr) => {
      expr.stx.value = strip_expr(expr.stx.value, file, diagnostics);
      new_node(loc, assoc, Expr::JsxExprContainer(expr))
    }
    Expr::JsxSpreadAttr(mut spread) => {
      spread.stx.value = strip_expr(spread.stx.value, file, diagnostics);
      new_node(loc, assoc, Expr::JsxSpreadAttr(spread))
    }
    Expr::LitArr(mut arr) => {
      for elem in arr.stx.elements.iter_mut() {
        if let LitArrElem::Single(expr) | LitArrElem::Rest(expr) = elem {
          let value = take_expr(expr);
          *expr = strip_expr(value, file, diagnostics);
        }
      }
      new_node(loc, assoc, Expr::LitArr(arr))
    }
    Expr::LitObj(mut obj) => {
      for member in obj.stx.members.iter_mut() {
        strip_obj_member(member, file, diagnostics);
      }
      new_node(loc, assoc, Expr::LitObj(obj))
    }
    Expr::LitTemplate(mut tpl) => {
      for part in tpl.stx.parts.iter_mut() {
        if let LitTemplatePart::Substitution(expr) = part {
          let inner = take_expr(expr);
          *expr = strip_expr(inner, file, diagnostics);
        }
      }
      new_node(loc, assoc, Expr::LitTemplate(tpl))
    }
    Expr::ArrPat(pat) => new_node(
      loc,
      assoc,
      Expr::ArrPat(strip_arr_pat(pat, file, diagnostics)),
    ),
    Expr::ObjPat(pat) => new_node(
      loc,
      assoc,
      Expr::ObjPat(strip_obj_pat(pat, file, diagnostics)),
    ),
    Expr::TypeAssertion(assert) => strip_expr(*assert.stx.expression, file, diagnostics),
    Expr::NonNullAssertion(assert) => strip_expr(*assert.stx.expression, file, diagnostics),
    Expr::SatisfiesExpr(assert) => strip_expr(*assert.stx.expression, file, diagnostics),
  }
}

fn strip_class_expr(
  class: Node<ClassExpr>,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> Node<ClassExpr> {
  let mut class = class;
  class.stx.type_parameters = None;
  class.stx.implements.clear();
  if let Some(extends) = class.stx.extends.take() {
    class.stx.extends = Some(strip_expr(extends, file, diagnostics));
  }
  for decorator in &mut class.stx.decorators {
    let expr = take_expr(&mut decorator.stx.expression);
    decorator.stx.expression = strip_expr(expr, file, diagnostics);
  }
  strip_class_members(&mut class.stx.members, file, diagnostics);
  class
}

fn strip_class_members(
  members: &mut Vec<Node<ClassMember>>,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) {
  let mut new_members = Vec::with_capacity(members.len());
  for member in members.drain(..) {
    if let Some(stripped) = strip_class_member(member, file, diagnostics) {
      new_members.push(stripped);
    }
  }
  *members = new_members;
}

fn strip_class_member(
  member: Node<ClassMember>,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> Option<Node<ClassMember>> {
  let mut member = member;
  match &mut member.stx.val {
    ClassOrObjVal::IndexSignature(_) => return None,
    ClassOrObjVal::Getter(get) => {
      if !strip_func(&mut get.stx.func.stx, file, diagnostics) {
        return None;
      }
    }
    ClassOrObjVal::Setter(set) => {
      if !strip_func(&mut set.stx.func.stx, file, diagnostics) {
        return None;
      }
    }
    ClassOrObjVal::Method(method) => {
      if !strip_func(&mut method.stx.func.stx, file, diagnostics) {
        return None;
      }
    }
    ClassOrObjVal::Prop(init) => {
      if let Some(init) = init {
        let value = take_expr(init);
        *init = strip_expr(value, file, diagnostics);
      }
    }
    ClassOrObjVal::StaticBlock(block) => strip_stmts(&mut block.stx.body, file, diagnostics),
  }
  member.stx.type_annotation = None;
  member.stx.optional = false;
  member.stx.definite_assignment = false;
  member.stx.abstract_ = false;
  member.stx.readonly = false;
  member.stx.accessor = false;
  member.stx.override_ = false;
  member.stx.accessibility = None;
  match &mut member.stx.key {
    ClassOrObjKey::Computed(expr) => {
      let expr_node = take_expr(expr);
      *expr = strip_expr(expr_node, file, diagnostics);
    }
    ClassOrObjKey::Direct(_) => {}
  }
  for decorator in &mut member.stx.decorators {
    let expr = take_expr(&mut decorator.stx.expression);
    decorator.stx.expression = strip_expr(expr, file, diagnostics);
  }
  Some(member)
}

fn strip_obj_member(member: &mut Node<ObjMember>, file: FileId, diagnostics: &mut Vec<Diagnostic>) {
  match &mut member.stx.typ {
    ObjMemberType::Valued { key, val } => {
      match key {
        ClassOrObjKey::Computed(expr) => {
          let expr_node = take_expr(expr);
          *expr = strip_expr(expr_node, file, diagnostics);
        }
        ClassOrObjKey::Direct(_) => {}
      }
      match val {
        ClassOrObjVal::Method(method) => {
          strip_func(&mut method.stx.func.stx, file, diagnostics);
        }
        ClassOrObjVal::Getter(get) => {
          strip_func(&mut get.stx.func.stx, file, diagnostics);
        }
        ClassOrObjVal::Setter(set) => {
          strip_func(&mut set.stx.func.stx, file, diagnostics);
        }
        ClassOrObjVal::Prop(init) => {
          if let Some(init) = init {
            let value = take_expr(init);
            *init = strip_expr(value, file, diagnostics);
          }
        }
        ClassOrObjVal::StaticBlock(block) => strip_stmts(&mut block.stx.body, file, diagnostics),
        ClassOrObjVal::IndexSignature(_) => {}
      }
    }
    ObjMemberType::Shorthand { .. } => {}
    ObjMemberType::Rest { val } => {
      let value = take_expr(val);
      *val = strip_expr(value, file, diagnostics);
    }
  }
}

fn strip_jsx_elem(
  elem: Node<JsxElem>,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> Node<JsxElem> {
  let mut elem = elem;
  for attr in elem.stx.attributes.iter_mut() {
    match attr {
      JsxAttr::Named { value, .. } => {
        if let Some(JsxAttrVal::Expression(expr)) = value {
          let inner = take_expr(&mut expr.stx.value);
          expr.stx.value = strip_expr(inner, file, diagnostics);
        } else if let Some(JsxAttrVal::Element(elem)) = value {
          let owned = take_jsx_elem(elem);
          *elem = strip_jsx_elem(owned, file, diagnostics);
        }
      }
      JsxAttr::Spread { value } => {
        let inner = take_expr(&mut value.stx.value);
        value.stx.value = strip_expr(inner, file, diagnostics);
      }
    }
  }
  for child in elem.stx.children.iter_mut() {
    match child {
      JsxElemChild::Element(elem) => {
        let owned = take_jsx_elem(elem);
        *elem = strip_jsx_elem(owned, file, diagnostics);
      }
      JsxElemChild::Expr(expr) => {
        let value = take_expr(&mut expr.stx.value);
        expr.stx.value = strip_expr(value, file, diagnostics);
      }
      JsxElemChild::Text(_) => {}
    }
  }
  elem
}

fn unsupported_ts(
  file: FileId,
  loc: Loc,
  message: impl Into<String>,
  diagnostics: &mut Vec<Diagnostic>,
) {
  diagnostics.push(Diagnostic::error(
    ERR_TS_UNSUPPORTED,
    message.into(),
    Span {
      file,
      range: loc.to_diagnostics_range(),
    },
  ));
}
