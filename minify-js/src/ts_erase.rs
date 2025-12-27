use crate::{Diagnostic, TopLevelMode};
use derive_visitor::{Drive, DriveMut};
use diagnostics::{FileId, Span};
use parse_js::ast::class_or_object::{
  ClassMember, ClassOrObjKey, ClassOrObjVal, ObjMember, ObjMemberType,
};
use parse_js::ast::expr::jsx::*;
use parse_js::ast::expr::lit::LitNullExpr;
use parse_js::ast::expr::lit::{LitArrElem, LitStrExpr, LitTemplatePart};
use parse_js::ast::expr::pat::{ArrPat, IdPat, ObjPat, Pat};
use parse_js::ast::expr::*;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::import_export::{ExportNames, ImportNames};
use parse_js::ast::node::{Node, NodeAssocData};
use parse_js::ast::stmt::decl::{
  ClassDecl, FuncDecl, ParamDecl, PatDecl, VarDecl, VarDeclMode, VarDeclarator,
};
use parse_js::ast::stmt::*;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::{EnumDecl, ImportEqualsDecl, ImportEqualsRhs};
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;

const ERR_TS_UNSUPPORTED: &str = "MINIFYTS0001";

struct StripContext<'a> {
  file: FileId,
  top_level_mode: TopLevelMode,
  source: &'a str,
  diagnostics: Vec<Diagnostic>,
}

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

pub fn erase_types(
  file: FileId,
  top_level_mode: TopLevelMode,
  source: &str,
  top_level: &mut Node<TopLevel>,
) -> Result<(), Vec<Diagnostic>> {
  let mut ctx = StripContext {
    file,
    top_level_mode,
    source,
    diagnostics: Vec::new(),
  };
  strip_stmts(&mut ctx, &mut top_level.stx.body, true);
  if ctx.diagnostics.is_empty() {
    Ok(())
  } else {
    Err(ctx.diagnostics)
  }
}

fn strip_stmts(
  ctx: &mut StripContext<'_>,
  stmts: &mut Vec<Node<Stmt>>,
  is_top_level: bool,
) {
  let mut new_stmts = Vec::with_capacity(stmts.len());
  for stmt in stmts.drain(..) {
    if let Some(stripped) = strip_stmt(ctx, stmt, is_top_level) {
      new_stmts.push(stripped);
    }
  }
  *stmts = new_stmts;
}

fn strip_stmt(
  ctx: &mut StripContext<'_>,
  stmt: Node<Stmt>,
  is_top_level: bool,
) -> Option<Node<Stmt>> {
  let loc = stmt.loc;
  let assoc = stmt.assoc;
  match *stmt.stx {
    Stmt::Block(block) => {
      let mut block = block;
      strip_stmts(ctx, &mut block.stx.body, false);
      Some(new_node(loc, assoc, Stmt::Block(block)))
    }
    Stmt::Expr(expr_stmt) => {
      let mut expr_stmt = expr_stmt;
      expr_stmt.stx.expr = strip_expr(ctx, expr_stmt.stx.expr);
      Some(new_node(loc, assoc, Stmt::Expr(expr_stmt)))
    }
    Stmt::If(mut if_stmt) => {
      if_stmt.stx.test = strip_expr(ctx, if_stmt.stx.test);
      if_stmt.stx.consequent = strip_stmt(ctx, if_stmt.stx.consequent, false)?;
      if let Some(alt) = if_stmt.stx.alternate.take() {
        if_stmt.stx.alternate = strip_stmt(ctx, alt, false);
      }
      Some(new_node(loc, assoc, Stmt::If(if_stmt)))
    }
    Stmt::ForTriple(mut for_stmt) => {
      match &mut for_stmt.stx.init {
        ForTripleStmtInit::Expr(expr) => {
          let owned = take_expr(expr);
          *expr = strip_expr(ctx, owned);
        }
        ForTripleStmtInit::Decl(decl) => strip_var_decl(ctx, &mut decl.stx),
        ForTripleStmtInit::None => {}
      }
      if let Some(cond) = for_stmt.stx.cond.take() {
        for_stmt.stx.cond = Some(strip_expr(ctx, cond));
      }
      if let Some(post) = for_stmt.stx.post.take() {
        for_stmt.stx.post = Some(strip_expr(ctx, post));
      }
      strip_for_body(ctx, &mut for_stmt.stx.body);
      Some(new_node(loc, assoc, Stmt::ForTriple(for_stmt)))
    }
    Stmt::ForIn(mut for_stmt) => {
      strip_for_in_of_lhs(ctx, &mut for_stmt.stx.lhs);
      for_stmt.stx.rhs = strip_expr(ctx, for_stmt.stx.rhs);
      strip_for_body(ctx, &mut for_stmt.stx.body);
      Some(new_node(loc, assoc, Stmt::ForIn(for_stmt)))
    }
    Stmt::ForOf(mut for_stmt) => {
      strip_for_in_of_lhs(ctx, &mut for_stmt.stx.lhs);
      for_stmt.stx.rhs = strip_expr(ctx, for_stmt.stx.rhs);
      strip_for_body(ctx, &mut for_stmt.stx.body);
      Some(new_node(loc, assoc, Stmt::ForOf(for_stmt)))
    }
    Stmt::While(mut while_stmt) => {
      while_stmt.stx.condition = strip_expr(ctx, while_stmt.stx.condition);
      while_stmt.stx.body = strip_stmt(ctx, while_stmt.stx.body, false)?;
      Some(new_node(loc, assoc, Stmt::While(while_stmt)))
    }
    Stmt::DoWhile(mut do_stmt) => {
      do_stmt.stx.body = strip_stmt(ctx, do_stmt.stx.body, false)?;
      do_stmt.stx.condition = strip_expr(ctx, do_stmt.stx.condition);
      Some(new_node(loc, assoc, Stmt::DoWhile(do_stmt)))
    }
    Stmt::Switch(mut switch_stmt) => {
      switch_stmt.stx.test = strip_expr(ctx, switch_stmt.stx.test);
      let mut new_branches = Vec::with_capacity(switch_stmt.stx.branches.len());
      for branch in switch_stmt.stx.branches.drain(..) {
        new_branches.push(strip_switch_branch(ctx, branch));
      }
      switch_stmt.stx.branches = new_branches;
      Some(new_node(loc, assoc, Stmt::Switch(switch_stmt)))
    }
    Stmt::Try(mut try_stmt) => {
      try_stmt.stx.wrapped = strip_block(ctx, try_stmt.stx.wrapped);
      if let Some(catch) = try_stmt.stx.catch.take() {
        try_stmt.stx.catch = Some(strip_catch(ctx, catch));
      }
      if let Some(finally) = try_stmt.stx.finally.take() {
        try_stmt.stx.finally = Some(strip_block(ctx, finally));
      }
      Some(new_node(loc, assoc, Stmt::Try(try_stmt)))
    }
    Stmt::Throw(mut throw_stmt) => {
      throw_stmt.stx.value = strip_expr(ctx, throw_stmt.stx.value);
      Some(new_node(loc, assoc, Stmt::Throw(throw_stmt)))
    }
    Stmt::Return(mut ret_stmt) => {
      if let Some(value) = ret_stmt.stx.value.take() {
        ret_stmt.stx.value = Some(strip_expr(ctx, value));
      }
      Some(new_node(loc, assoc, Stmt::Return(ret_stmt)))
    }
    Stmt::Break(_) | Stmt::Continue(_) | Stmt::Debugger(_) | Stmt::Empty(_) => {
      Some(new_node(loc, assoc, *stmt.stx))
    }
    Stmt::With(mut with_stmt) => {
      with_stmt.stx.object = strip_expr(ctx, with_stmt.stx.object);
      with_stmt.stx.body = strip_stmt(ctx, with_stmt.stx.body, false)?;
      Some(new_node(loc, assoc, Stmt::With(with_stmt)))
    }
    Stmt::Label(mut label_stmt) => {
      label_stmt.stx.statement = strip_stmt(ctx, label_stmt.stx.statement, false)?;
      Some(new_node(loc, assoc, Stmt::Label(label_stmt)))
    }
    Stmt::VarDecl(mut decl) => {
      strip_var_decl(ctx, &mut decl.stx);
      Some(new_node(loc, assoc, Stmt::VarDecl(decl)))
    }
    Stmt::FunctionDecl(func_decl) => strip_func_decl(ctx, func_decl, loc, assoc),
    Stmt::ClassDecl(class_decl) => strip_class_decl(ctx, class_decl, loc, assoc),
    Stmt::Import(import_stmt) => strip_import(ctx, import_stmt, loc, assoc),
    Stmt::ExportList(export_stmt) => strip_export_list(export_stmt, loc, assoc),
    Stmt::ExportDefaultExpr(mut expr) => {
      expr.stx.expression = strip_expr(ctx, expr.stx.expression);
      Some(new_node(loc, assoc, Stmt::ExportDefaultExpr(expr)))
    }
    Stmt::InterfaceDecl(_)
    | Stmt::TypeAliasDecl(_)
    | Stmt::ImportTypeDecl(_)
    | Stmt::ExportTypeDecl(_)
    | Stmt::ExportAsNamespaceDecl(_)
    | Stmt::AmbientVarDecl(_)
    | Stmt::AmbientFunctionDecl(_)
    | Stmt::AmbientClassDecl(_)
    | Stmt::GlobalDecl(_) => None,
    Stmt::EnumDecl(decl) => strip_enum_decl(ctx, decl, loc, assoc),
    Stmt::NamespaceDecl(decl) => {
      if decl.stx.declare {
        None
      } else {
        unsupported_ts(
          ctx,
          loc,
          "namespaces with runtime bodies are not supported",
        );
        None
      }
    }
    Stmt::ModuleDecl(decl) => {
      if decl.stx.declare {
        None
      } else {
        unsupported_ts(
          ctx,
          loc,
          "modules with runtime bodies are not supported",
        );
        None
      }
    }
    Stmt::ImportEqualsDecl(decl) => {
      lower_import_equals_decl(ctx, decl, loc, assoc, is_top_level)
    }
    Stmt::ExportAssignmentDecl(decl) => {
      let expr = strip_expr(ctx, decl.stx.expression);
      lower_export_assignment(ctx, loc, assoc, expr, is_top_level)
    }
  }
}

fn trim_leading_trivia(mut text: &str) -> &str {
  loop {
    let trimmed = text.trim_start_matches(|c: char| c.is_whitespace());
    if let Some(without_line_comment) = trimmed.strip_prefix("//") {
      match without_line_comment.find('\n') {
        Some(pos) => {
          text = &without_line_comment[pos + 1..];
          continue;
        }
        None => return "",
      }
    }
    if let Some(without_block_comment) = trimmed.strip_prefix("/*") {
      match without_block_comment.find("*/") {
        Some(pos) => {
          text = &without_block_comment[pos + 2..];
          continue;
        }
        None => return "",
      }
    }
    return trimmed;
  }
}

fn import_equals_is_type_only(ctx: &StripContext<'_>, loc: Loc) -> bool {
  let Some(slice) = ctx.source.get(loc.0..loc.1) else {
    return false;
  };
  let mut view = trim_leading_trivia(slice);
  if let Some(after_export) = view.strip_prefix("export") {
    view = trim_leading_trivia(after_export);
  }
  let Some(after_import) = view.strip_prefix("import") else {
    return false;
  };
  let view = trim_leading_trivia(after_import);
  if let Some(rest) = view.strip_prefix("type") {
    let next = rest.chars().next();
    return next.map_or(true, |ch| !ch.is_ascii_alphanumeric() && ch != '_');
  }
  false
}

fn lower_import_equals_decl(
  ctx: &mut StripContext<'_>,
  decl: Node<ImportEqualsDecl>,
  loc: Loc,
  assoc: NodeAssocData,
  is_top_level: bool,
) -> Option<Node<Stmt>> {
  if import_equals_is_type_only(ctx, loc) {
    return None;
  }
  if !is_top_level {
    unsupported_ts(ctx, loc, "import= assignments must be at top level");
    return None;
  }
  let initializer = match &decl.stx.rhs {
    ImportEqualsRhs::Require { module } => Some(require_call(loc, module.clone())),
    ImportEqualsRhs::EntityName { path } => qualified_path_expr(loc, path),
  };
  let initializer = match initializer {
    Some(expr) => expr,
    None => {
      unsupported_ts(
        ctx,
        loc,
        "import= assignments must target require(\"...\") or qualified names",
      );
      return None;
    }
  };
  let pattern = Node::new(
    loc,
    PatDecl {
      pat: Node::new(loc, Pat::Id(Node::new(loc, IdPat { name: decl.stx.name }))),
    },
  );
  let declarator = VarDeclarator {
    pattern,
    definite_assignment: false,
    type_annotation: None,
    initializer: Some(initializer),
  };
  let var_decl = VarDecl {
    export: decl.stx.export,
    mode: match ctx.top_level_mode {
      TopLevelMode::Module => VarDeclMode::Const,
      TopLevelMode::Global => VarDeclMode::Var,
    },
    declarators: vec![declarator],
  };
  Some(new_node(
    loc,
    assoc,
    Stmt::VarDecl(Node::new(loc, var_decl)),
  ))
}

fn lower_export_assignment(
  ctx: &mut StripContext<'_>,
  loc: Loc,
  assoc: NodeAssocData,
  expr: Node<Expr>,
  is_top_level: bool,
) -> Option<Node<Stmt>> {
  if !is_top_level {
    unsupported_ts(ctx, loc, "export = assignments must be at top level");
    return None;
  }
  let target = Node::new(
    loc,
    Expr::Member(Node::new(
      loc,
      MemberExpr {
        optional_chaining: false,
        left: Node::new(loc, Expr::Id(Node::new(loc, IdExpr { name: "module".into() }))),
        right: "exports".into(),
      },
    )),
  );
  let assignment = Node::new(
    loc,
    Expr::Binary(Node::new(
      loc,
      BinaryExpr {
        operator: OperatorName::Assignment,
        left: target,
        right: expr,
      },
    )),
  );
  Some(new_node(
    loc,
    assoc,
    Stmt::Expr(Node::new(loc, ExprStmt { expr: assignment })),
  ))
}

fn require_call(loc: Loc, module: String) -> Node<Expr> {
  Node::new(
    loc,
    Expr::Call(Node::new(
      loc,
      CallExpr {
        optional_chaining: false,
        callee: Node::new(loc, Expr::Id(Node::new(loc, IdExpr { name: "require".into() }))),
        arguments: vec![Node::new(
          loc,
          CallArg {
            spread: false,
            value: Node::new(loc, Expr::LitStr(Node::new(loc, LitStrExpr { value: module }))),
          },
        )],
      },
    )),
  )
}

fn qualified_path_expr(loc: Loc, path: &[String]) -> Option<Node<Expr>> {
  let mut segments = path.iter();
  let first = segments.next()?;
  let mut expr = Node::new(loc, Expr::Id(Node::new(loc, IdExpr { name: first.clone() })));
  for part in segments {
    expr = Node::new(
      loc,
      Expr::Member(Node::new(
        loc,
        MemberExpr {
          optional_chaining: false,
          left: expr,
          right: part.clone(),
        },
      )),
    );
  }
  Some(expr)
}

fn strip_func_decl(
  ctx: &mut StripContext<'_>,
  func_decl: Node<FuncDecl>,
  loc: Loc,
  assoc: NodeAssocData,
) -> Option<Node<Stmt>> {
  let mut func_decl = func_decl;
  if !strip_func(ctx, &mut func_decl.stx.function.stx) {
    return None;
  }
  Some(new_node(loc, assoc, Stmt::FunctionDecl(func_decl)))
}

fn strip_class_decl(
  ctx: &mut StripContext<'_>,
  class_decl: Node<ClassDecl>,
  loc: Loc,
  assoc: NodeAssocData,
) -> Option<Node<Stmt>> {
  let mut class_decl = class_decl;
  if class_decl.stx.declare {
    return None;
  }
  class_decl.stx.abstract_ = false;
  class_decl.stx.type_parameters = None;
  class_decl.stx.implements.clear();
  if let Some(extends) = class_decl.stx.extends.take() {
    class_decl.stx.extends = Some(strip_expr(ctx, extends));
  }
  for decorator in &mut class_decl.stx.decorators {
    let expr = take_expr(&mut decorator.stx.expression);
    decorator.stx.expression = strip_expr(ctx, expr);
  }
  strip_class_members(ctx, &mut class_decl.stx.members);
  Some(new_node(loc, assoc, Stmt::ClassDecl(class_decl)))
}

fn strip_import(
  ctx: &mut StripContext<'_>,
  import_stmt: Node<ImportStmt>,
  loc: Loc,
  assoc: NodeAssocData,
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
          entry.stx.alias.stx.pat = strip_pat(ctx, pat);
        }
        if list.is_empty() {
          import_stmt.stx.names = None;
        }
      }
      ImportNames::All(pat) => {
        let pat_node = take_pat(&mut pat.stx.pat);
        pat.stx.pat = strip_pat(ctx, pat_node);
      }
    }
  }
  if let Some(default) = import_stmt.stx.default.as_mut() {
    let pat = take_pat(&mut default.stx.pat);
    default.stx.pat = strip_pat(ctx, pat);
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
  ctx: &mut StripContext<'_>,
  decl: Node<EnumDecl>,
  loc: Loc,
  _assoc: NodeAssocData,
) -> Option<Node<Stmt>> {
  if decl.stx.declare || decl.stx.const_ {
    None
  } else {
    unsupported_ts(
      ctx,
      loc,
      "runtime enums are not supported in JS erasure",
    );
    None
  }
}

fn strip_switch_branch(
  ctx: &mut StripContext<'_>,
  branch: Node<SwitchBranch>,
) -> Node<SwitchBranch> {
  let mut branch = branch;
  if let Some(case) = branch.stx.case.take() {
    branch.stx.case = Some(strip_expr(ctx, case));
  }
  strip_stmts(ctx, &mut branch.stx.body, false);
  branch
}

fn strip_catch(
  ctx: &mut StripContext<'_>,
  mut catch: Node<CatchBlock>,
) -> Node<CatchBlock> {
  catch.stx.type_annotation = None;
  if let Some(param) = catch.stx.parameter.as_mut() {
    let pat = take_pat(&mut param.stx.pat);
    param.stx.pat = strip_pat(ctx, pat);
  }
  strip_stmts(ctx, &mut catch.stx.body, false);
  catch
}

fn strip_for_body(ctx: &mut StripContext<'_>, body: &mut Node<ForBody>) {
  strip_stmts(ctx, &mut body.stx.body, false);
}

fn strip_block(
  ctx: &mut StripContext<'_>,
  block: Node<BlockStmt>,
) -> Node<BlockStmt> {
  let mut block = block;
  strip_stmts(ctx, &mut block.stx.body, false);
  block
}

fn strip_for_in_of_lhs(ctx: &mut StripContext<'_>, lhs: &mut ForInOfLhs) {
  match lhs {
    ForInOfLhs::Assign(pat) => {
      let owned = take_pat(pat);
      *pat = strip_pat(ctx, owned);
    }
    ForInOfLhs::Decl((_, pat)) => {
      let owned = take_pat(&mut pat.stx.pat);
      pat.stx.pat = strip_pat(ctx, owned);
    }
  }
}

fn strip_var_decl(ctx: &mut StripContext<'_>, decl: &mut VarDecl) {
  for declarator in decl.declarators.iter_mut() {
    strip_var_declarator(ctx, declarator);
  }
}

fn strip_var_declarator(ctx: &mut StripContext<'_>, decl: &mut VarDeclarator) {
  decl.type_annotation = None;
  decl.definite_assignment = false;
  let pat = take_pat(&mut decl.pattern.stx.pat);
  decl.pattern.stx.pat = strip_pat(ctx, pat);
  if let Some(init) = decl.initializer.take() {
    decl.initializer = Some(strip_expr(ctx, init));
  }
}

fn strip_func(ctx: &mut StripContext<'_>, func: &mut Func) -> bool {
  func.type_parameters = None;
  func.return_type = None;
  func
    .parameters
    .iter_mut()
    .for_each(|param| strip_param(ctx, param));
  match func.body.take() {
    Some(FuncBody::Block(body)) => {
      let mut block = body;
      strip_stmts(ctx, &mut block, false);
      func.body = Some(FuncBody::Block(block));
      true
    }
    Some(FuncBody::Expression(expr)) => {
      func.body = Some(FuncBody::Expression(strip_expr(ctx, expr)));
      true
    }
    None => false,
  }
}

fn strip_param(ctx: &mut StripContext<'_>, param: &mut Node<ParamDecl>) {
  param.stx.optional = false;
  param.stx.accessibility = None;
  param.stx.readonly = false;
  param.stx.type_annotation = None;
  let pat = take_pat(&mut param.stx.pattern.stx.pat);
  param.stx.pattern.stx.pat = strip_pat(ctx, pat);
  if let Some(default) = param.stx.default_value.take() {
    param.stx.default_value = Some(strip_expr(ctx, default));
  }
  for decorator in &mut param.stx.decorators {
    let expr = take_expr(&mut decorator.stx.expression);
    decorator.stx.expression = strip_expr(ctx, expr);
  }
}

fn strip_pat(ctx: &mut StripContext<'_>, pat: Node<Pat>) -> Node<Pat> {
  let Node { loc, assoc, stx } = pat;
  match *stx {
    Pat::Arr(arr) => new_node(loc, assoc, Pat::Arr(strip_arr_pat(ctx, arr))),
    Pat::Obj(obj) => new_node(loc, assoc, Pat::Obj(strip_obj_pat(ctx, obj))),
    Pat::AssignTarget(expr) => new_node(
      loc,
      assoc,
      Pat::AssignTarget(strip_expr(ctx, expr)),
    ),
    Pat::Id(_) => Node { loc, assoc, stx },
  }
}

fn strip_arr_pat(
  ctx: &mut StripContext<'_>,
  pat: Node<ArrPat>,
) -> Node<ArrPat> {
  let mut pat = pat;
  for elem in pat.stx.elements.iter_mut() {
    if let Some(elem) = elem {
      let target = take_pat(&mut elem.target);
      elem.target = strip_pat(ctx, target);
      if let Some(default) = elem.default_value.take() {
        elem.default_value = Some(strip_expr(ctx, default));
      }
    }
  }
  if let Some(rest) = pat.stx.rest.as_mut() {
    let rest_pat = take_pat(rest);
    *rest = strip_pat(ctx, rest_pat);
  }
  pat
}

fn strip_obj_pat(
  ctx: &mut StripContext<'_>,
  pat: Node<ObjPat>,
) -> Node<ObjPat> {
  let mut pat = pat;
  for prop in pat.stx.properties.iter_mut() {
    let target = take_pat(&mut prop.stx.target);
    prop.stx.target = strip_pat(ctx, target);
    if let Some(default) = prop.stx.default_value.take() {
      prop.stx.default_value = Some(strip_expr(ctx, default));
    }
  }
  if let Some(rest) = pat.stx.rest.as_mut() {
    let rest_pat = take_pat(rest);
    *rest = strip_pat(ctx, rest_pat);
  }
  pat
}

fn strip_expr(ctx: &mut StripContext<'_>, expr: Node<Expr>) -> Node<Expr> {
  let loc = expr.loc;
  let assoc = expr.assoc;
  match *expr.stx {
    Expr::ArrowFunc(func) => {
      let mut func = func;
      strip_func(ctx, &mut func.stx.func.stx);
      new_node(loc, assoc, Expr::ArrowFunc(func))
    }
    Expr::Binary(mut bin) => {
      bin.stx.left = strip_expr(ctx, bin.stx.left);
      bin.stx.right = strip_expr(ctx, bin.stx.right);
      new_node(loc, assoc, Expr::Binary(bin))
    }
    Expr::Call(mut call) => {
      call.stx.callee = strip_expr(ctx, call.stx.callee);
      for arg in call.stx.arguments.iter_mut() {
        let value = take_expr(&mut arg.stx.value);
        arg.stx.value = strip_expr(ctx, value);
      }
      new_node(loc, assoc, Expr::Call(call))
    }
    Expr::Class(class) => new_node(
      loc,
      assoc,
      Expr::Class(strip_class_expr(ctx, class)),
    ),
    Expr::ComputedMember(mut member) => {
      member.stx.object = strip_expr(ctx, member.stx.object);
      member.stx.member = strip_expr(ctx, member.stx.member);
      new_node(loc, assoc, Expr::ComputedMember(member))
    }
    Expr::Cond(mut cond) => {
      cond.stx.test = strip_expr(ctx, cond.stx.test);
      cond.stx.consequent = strip_expr(ctx, cond.stx.consequent);
      cond.stx.alternate = strip_expr(ctx, cond.stx.alternate);
      new_node(loc, assoc, Expr::Cond(cond))
    }
    Expr::Func(mut func) => {
      strip_func(ctx, &mut func.stx.func.stx);
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
      import.stx.module = strip_expr(ctx, import.stx.module);
      if let Some(attrs) = import.stx.attributes.take() {
        import.stx.attributes = Some(strip_expr(ctx, attrs));
      }
      new_node(loc, assoc, Expr::Import(import))
    }
    Expr::Member(mut member) => {
      member.stx.left = strip_expr(ctx, member.stx.left);
      new_node(loc, assoc, Expr::Member(member))
    }
    Expr::TaggedTemplate(mut tagged) => {
      tagged.stx.function = strip_expr(ctx, tagged.stx.function);
      for part in tagged.stx.parts.iter_mut() {
        if let LitTemplatePart::Substitution(expr) = part {
          let inner = take_expr(expr);
          *expr = strip_expr(ctx, inner);
        }
      }
      new_node(loc, assoc, Expr::TaggedTemplate(tagged))
    }
    Expr::Unary(mut unary) => {
      unary.stx.argument = strip_expr(ctx, unary.stx.argument);
      new_node(loc, assoc, Expr::Unary(unary))
    }
    Expr::UnaryPostfix(mut unary) => {
      unary.stx.argument = strip_expr(ctx, unary.stx.argument);
      new_node(loc, assoc, Expr::UnaryPostfix(unary))
    }
    Expr::JsxElem(elem) => new_node(
      loc,
      assoc,
      Expr::JsxElem(strip_jsx_elem(ctx, elem)),
    ),
    Expr::JsxExprContainer(mut expr) => {
      expr.stx.value = strip_expr(ctx, expr.stx.value);
      new_node(loc, assoc, Expr::JsxExprContainer(expr))
    }
    Expr::JsxSpreadAttr(mut spread) => {
      spread.stx.value = strip_expr(ctx, spread.stx.value);
      new_node(loc, assoc, Expr::JsxSpreadAttr(spread))
    }
    Expr::LitArr(mut arr) => {
      for elem in arr.stx.elements.iter_mut() {
        if let LitArrElem::Single(expr) | LitArrElem::Rest(expr) = elem {
          let value = take_expr(expr);
          *expr = strip_expr(ctx, value);
        }
      }
      new_node(loc, assoc, Expr::LitArr(arr))
    }
    Expr::LitObj(mut obj) => {
      for member in obj.stx.members.iter_mut() {
        strip_obj_member(ctx, member);
      }
      new_node(loc, assoc, Expr::LitObj(obj))
    }
    Expr::LitTemplate(mut tpl) => {
      for part in tpl.stx.parts.iter_mut() {
        if let LitTemplatePart::Substitution(expr) = part {
          let inner = take_expr(expr);
          *expr = strip_expr(ctx, inner);
        }
      }
      new_node(loc, assoc, Expr::LitTemplate(tpl))
    }
    Expr::ArrPat(pat) => new_node(
      loc,
      assoc,
      Expr::ArrPat(strip_arr_pat(ctx, pat)),
    ),
    Expr::ObjPat(pat) => new_node(
      loc,
      assoc,
      Expr::ObjPat(strip_obj_pat(ctx, pat)),
    ),
    Expr::TypeAssertion(assert) => strip_expr(ctx, *assert.stx.expression),
    Expr::NonNullAssertion(assert) => strip_expr(ctx, *assert.stx.expression),
    Expr::SatisfiesExpr(assert) => strip_expr(ctx, *assert.stx.expression),
  }
}

fn strip_class_expr(
  ctx: &mut StripContext<'_>,
  class: Node<ClassExpr>,
) -> Node<ClassExpr> {
  let mut class = class;
  class.stx.type_parameters = None;
  class.stx.implements.clear();
  if let Some(extends) = class.stx.extends.take() {
    class.stx.extends = Some(strip_expr(ctx, extends));
  }
  for decorator in &mut class.stx.decorators {
    let expr = take_expr(&mut decorator.stx.expression);
    decorator.stx.expression = strip_expr(ctx, expr);
  }
  strip_class_members(ctx, &mut class.stx.members);
  class
}

fn strip_class_members(
  ctx: &mut StripContext<'_>,
  members: &mut Vec<Node<ClassMember>>,
) {
  let mut new_members = Vec::with_capacity(members.len());
  for member in members.drain(..) {
    if let Some(stripped) = strip_class_member(ctx, member) {
      new_members.push(stripped);
    }
  }
  *members = new_members;
}

fn strip_class_member(
  ctx: &mut StripContext<'_>,
  member: Node<ClassMember>,
) -> Option<Node<ClassMember>> {
  let mut member = member;
  match &mut member.stx.val {
    ClassOrObjVal::IndexSignature(_) => return None,
    ClassOrObjVal::Getter(get) => {
      if !strip_func(ctx, &mut get.stx.func.stx) {
        return None;
      }
    }
    ClassOrObjVal::Setter(set) => {
      if !strip_func(ctx, &mut set.stx.func.stx) {
        return None;
      }
    }
    ClassOrObjVal::Method(method) => {
      if !strip_func(ctx, &mut method.stx.func.stx) {
        return None;
      }
    }
    ClassOrObjVal::Prop(init) => {
      if let Some(init) = init {
        let value = take_expr(init);
        *init = strip_expr(ctx, value);
      }
    }
    ClassOrObjVal::StaticBlock(block) => strip_stmts(ctx, &mut block.stx.body, false),
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
      *expr = strip_expr(ctx, expr_node);
    }
    ClassOrObjKey::Direct(_) => {}
  }
  for decorator in &mut member.stx.decorators {
    let expr = take_expr(&mut decorator.stx.expression);
    decorator.stx.expression = strip_expr(ctx, expr);
  }
  Some(member)
}

fn strip_obj_member(ctx: &mut StripContext<'_>, member: &mut Node<ObjMember>) {
  match &mut member.stx.typ {
    ObjMemberType::Valued { key, val } => {
      match key {
        ClassOrObjKey::Computed(expr) => {
          let expr_node = take_expr(expr);
          *expr = strip_expr(ctx, expr_node);
        }
        ClassOrObjKey::Direct(_) => {}
      }
      match val {
        ClassOrObjVal::Method(method) => {
          strip_func(ctx, &mut method.stx.func.stx);
        }
        ClassOrObjVal::Getter(get) => {
          strip_func(ctx, &mut get.stx.func.stx);
        }
        ClassOrObjVal::Setter(set) => {
          strip_func(ctx, &mut set.stx.func.stx);
        }
        ClassOrObjVal::Prop(init) => {
          if let Some(init) = init {
            let value = take_expr(init);
            *init = strip_expr(ctx, value);
          }
        }
        ClassOrObjVal::StaticBlock(block) => strip_stmts(ctx, &mut block.stx.body, false),
        ClassOrObjVal::IndexSignature(_) => {}
      }
    }
    ObjMemberType::Shorthand { .. } => {}
    ObjMemberType::Rest { val } => {
      let value = take_expr(val);
      *val = strip_expr(ctx, value);
    }
  }
}

fn strip_jsx_elem(
  ctx: &mut StripContext<'_>,
  elem: Node<JsxElem>,
) -> Node<JsxElem> {
  let mut elem = elem;
  for attr in elem.stx.attributes.iter_mut() {
    match attr {
      JsxAttr::Named { value, .. } => {
        if let Some(JsxAttrVal::Expression(expr)) = value {
          let inner = take_expr(&mut expr.stx.value);
          expr.stx.value = strip_expr(ctx, inner);
        } else if let Some(JsxAttrVal::Element(elem)) = value {
          let owned = take_jsx_elem(elem);
          *elem = strip_jsx_elem(ctx, owned);
        }
      }
      JsxAttr::Spread { value } => {
        let inner = take_expr(&mut value.stx.value);
        value.stx.value = strip_expr(ctx, inner);
      }
    }
  }
  for child in elem.stx.children.iter_mut() {
    match child {
      JsxElemChild::Element(elem) => {
        let owned = take_jsx_elem(elem);
        *elem = strip_jsx_elem(ctx, owned);
      }
      JsxElemChild::Expr(expr) => {
        let value = take_expr(&mut expr.stx.value);
        expr.stx.value = strip_expr(ctx, value);
      }
      JsxElemChild::Text(_) => {}
    }
  }
  elem
}

fn unsupported_ts(
  ctx: &mut StripContext<'_>,
  loc: Loc,
  message: impl Into<String>,
) {
  ctx.diagnostics.push(Diagnostic::error(
    ERR_TS_UNSUPPORTED,
    message.into(),
    Span {
      file: ctx.file,
      range: loc.to_diagnostics_range(),
    },
  ));
}
