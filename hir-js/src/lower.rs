use crate::hir::Body;
use crate::hir::BodyKind;
use crate::hir::DefData;
use crate::hir::Expr;
use crate::hir::ExprKind;
use crate::hir::HirFile;
use crate::hir::LowerResult;
use crate::hir::Pat;
use crate::hir::PatKind;
use crate::hir::Stmt;
use crate::hir::StmtKind;
use crate::ids::BodyId;
use crate::ids::DefId;
use crate::ids::DefKind;
use crate::ids::DefPath;
use crate::ids::ExprId;
use crate::ids::NameId;
use crate::ids::PatId;
use crate::ids::StmtId;
use crate::intern::NameInterner;
use crate::span_map::SpanMap;
use diagnostics::FileId;
use diagnostics::TextRange;
use parse_js::ast::expr::pat::ArrPat;
use parse_js::ast::expr::pat::ClassOrFuncName;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::pat::ObjPat;
use parse_js::ast::expr::pat::Pat as AstPat;
use parse_js::ast::expr::ArrowFuncExpr;
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::expr::FuncExpr;
use parse_js::ast::func::Func;
use parse_js::ast::func::FuncBody;
use parse_js::ast::import_export::*;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::FuncDecl;
use parse_js::ast::stmt::decl::VarDeclarator;
use parse_js::ast::stmt::CatchBlock;
use parse_js::ast::stmt::ForBody;
use parse_js::ast::stmt::ForInOfLhs;
use parse_js::ast::stmt::ForTripleStmtInit;
use parse_js::ast::stmt::Stmt as AstStmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::*;
use parse_js::loc::Loc;
use std::collections::BTreeMap;
use std::sync::Arc;

/// Convert a parser `Loc` into a `TextRange` used by HIR.
fn to_range(loc: Loc) -> TextRange {
  TextRange::new(loc.0 as u32, loc.1 as u32)
}

#[derive(Debug)]
struct DefDescriptor<'a> {
  kind: DefKind,
  name: NameId,
  name_text: String,
  span: TextRange,
  is_item: bool,
  source: DefSource<'a>,
}

#[derive(Debug)]
enum DefSource<'a> {
  None,
  Function(&'a Node<FuncDecl>),
  ArrowFunction(&'a Node<ArrowFuncExpr>),
  FuncExpr(&'a Node<FuncExpr>),
  Var(&'a VarDeclarator),
}

impl<'a> DefDescriptor<'a> {
  fn new(
    kind: DefKind,
    name: NameId,
    name_text: String,
    span: TextRange,
    is_item: bool,
    source: DefSource<'a>,
  ) -> Self {
    Self {
      kind,
      name,
      name_text,
      span,
      is_item,
      source,
    }
  }
}

/// Lower a parsed file into HIR structures.
pub fn lower_file(file: FileId, ast: &Node<TopLevel>) -> LowerResult {
  let mut names = NameInterner::default();
  let mut descriptors = Vec::new();
  collect_top_level(file, ast, &mut descriptors, &mut names);

  descriptors.sort_by(|a, b| {
    (a.kind, a.name_text.as_str(), a.span.start).cmp(&(b.kind, b.name_text.as_str(), b.span.start))
  });

  let mut span_map = SpanMap::new();
  let mut defs = Vec::with_capacity(descriptors.len());
  let mut bodies = Vec::new();
  let mut body_ids = Vec::new();
  let mut items = Vec::new();
  let mut disambiguators: BTreeMap<(DefKind, NameId), u32> = BTreeMap::new();

  for (idx, desc) in descriptors.into_iter().enumerate() {
    let def_id = DefId(idx as u32);
    if desc.is_item {
      items.push(def_id);
    }

    let dis = disambiguators.entry((desc.kind, desc.name)).or_insert(0);
    let def_path = DefPath::new(file, desc.kind, desc.name, *dis);
    *dis += 1;

    span_map.add_def(desc.span, def_id);

    let mut def_data = DefData {
      id: def_id,
      path: def_path,
      span: desc.span,
      body: None,
    };

    if let Some(body) = lower_body_from_source(def_id, &desc.source, &mut names, &mut span_map) {
      let body_id = BodyId(bodies.len() as u32);
      def_data.body = Some(body_id);
      body_ids.push(body_id);
      bodies.push(Arc::new(body));
    }

    defs.push(def_data);
  }

  span_map.finalize();

  LowerResult {
    hir: Arc::new(HirFile::new(file, items, body_ids, span_map)),
    defs,
    bodies,
    names: Arc::new(names),
  }
}

fn lower_body_from_source(
  owner: DefId,
  source: &DefSource,
  names: &mut NameInterner,
  span_map: &mut SpanMap,
) -> Option<Body> {
  match source {
    DefSource::Function(decl) => lower_function_body(owner, &decl.stx.function, names, span_map),
    DefSource::ArrowFunction(func) => lower_function_body(owner, &func.stx.func, names, span_map),
    DefSource::FuncExpr(func) => lower_function_body(owner, &func.stx.func, names, span_map),
    DefSource::Var(decl) => lower_var_body(owner, decl, names, span_map),
    DefSource::None => None,
  }
}

fn lower_var_body(
  owner: DefId,
  decl: &VarDeclarator,
  names: &mut NameInterner,
  span_map: &mut SpanMap,
) -> Option<Body> {
  let mut builder = BodyBuilder::new(owner, BodyKind::Initializer, names, span_map);
  lower_pat(&decl.pattern.stx.pat, &mut builder);
  if let Some(init) = &decl.initializer {
    let expr_id = lower_expr(init, &mut builder);
    builder.alloc_stmt(to_range(init.loc), StmtKind::Expr(expr_id));
  }
  Some(builder.finish())
}

fn lower_function_body(
  owner: DefId,
  func: &Node<Func>,
  names: &mut NameInterner,
  span_map: &mut SpanMap,
) -> Option<Body> {
  let mut builder = BodyBuilder::new(owner, BodyKind::Function, names, span_map);
  for param in func.stx.parameters.iter() {
    lower_pat(&param.stx.pattern.stx.pat, &mut builder);
    if let Some(default) = &param.stx.default_value {
      lower_expr(default, &mut builder);
    }
  }

  match &func.stx.body {
    Some(FuncBody::Block(stmts)) => {
      for stmt in stmts.iter() {
        lower_stmt(stmt, &mut builder);
      }
    }
    Some(FuncBody::Expression(expr)) => {
      let expr_id = lower_expr(expr, &mut builder);
      builder.alloc_stmt(to_range(expr.loc), StmtKind::Return(Some(expr_id)));
    }
    None => {}
  }

  Some(builder.finish())
}

fn lower_stmt(stmt: &Node<AstStmt>, builder: &mut BodyBuilder<'_>) -> StmtId {
  let span = to_range(stmt.loc);
  let kind = match &*stmt.stx {
    AstStmt::Expr(expr_stmt) => {
      let expr_id = lower_expr(&expr_stmt.stx.expr, builder);
      StmtKind::Expr(expr_id)
    }
    AstStmt::Return(ret) => {
      let value = ret.stx.value.as_ref().map(|v| lower_expr(v, builder));
      StmtKind::Return(value)
    }
    AstStmt::Block(block) => {
      let mut stmts = Vec::new();
      for s in block.stx.body.iter() {
        stmts.push(lower_stmt(s, builder));
      }
      StmtKind::Block(stmts)
    }
    AstStmt::If(if_stmt) => {
      lower_expr(&if_stmt.stx.test, builder);
      lower_stmt(&if_stmt.stx.consequent, builder);
      if let Some(alt) = &if_stmt.stx.alternate {
        lower_stmt(alt, builder);
      }
      StmtKind::Other
    }
    AstStmt::While(wh) => {
      lower_expr(&wh.stx.condition, builder);
      lower_stmt(&wh.stx.body, builder);
      StmtKind::Other
    }
    AstStmt::DoWhile(dw) => {
      lower_expr(&dw.stx.condition, builder);
      lower_stmt(&dw.stx.body, builder);
      StmtKind::Other
    }
    AstStmt::ForTriple(for_stmt) => {
      match &for_stmt.stx.init {
        ForTripleStmtInit::Expr(e) => {
          lower_expr(e, builder);
        }
        ForTripleStmtInit::Decl(decl) => {
          lower_var_decl(decl, builder);
        }
        ForTripleStmtInit::None => {}
      }
      if let Some(cond) = &for_stmt.stx.cond {
        lower_expr(cond, builder);
      }
      if let Some(post) = &for_stmt.stx.post {
        lower_expr(post, builder);
      }
      lower_for_body(&for_stmt.stx.body, builder);
      StmtKind::Other
    }
    AstStmt::ForIn(for_in) => {
      lower_for_lhs(&for_in.stx.lhs, builder);
      lower_expr(&for_in.stx.rhs, builder);
      lower_for_body(&for_in.stx.body, builder);
      StmtKind::Other
    }
    AstStmt::ForOf(for_of) => {
      lower_for_lhs(&for_of.stx.lhs, builder);
      lower_expr(&for_of.stx.rhs, builder);
      lower_for_body(&for_of.stx.body, builder);
      StmtKind::Other
    }
    AstStmt::Switch(sw) => {
      lower_expr(&sw.stx.test, builder);
      for branch in sw.stx.branches.iter() {
        if let Some(case) = &branch.stx.case {
          lower_expr(case, builder);
        }
        for stmt in branch.stx.body.iter() {
          lower_stmt(stmt, builder);
        }
      }
      StmtKind::Other
    }
    AstStmt::Try(tr) => {
      lower_block_stmt(&tr.stx.wrapped, builder);
      if let Some(catch) = &tr.stx.catch {
        lower_catch(catch, builder);
      }
      if let Some(finally) = &tr.stx.finally {
        lower_block_stmt(finally, builder);
      }
      StmtKind::Other
    }
    AstStmt::Throw(th) => {
      lower_expr(&th.stx.value, builder);
      StmtKind::Other
    }
    AstStmt::Label(label) => {
      lower_stmt(&label.stx.statement, builder);
      StmtKind::Other
    }
    AstStmt::With(w) => {
      lower_expr(&w.stx.object, builder);
      lower_stmt(&w.stx.body, builder);
      StmtKind::Other
    }
    AstStmt::VarDecl(decl) => {
      lower_var_decl(decl, builder);
      StmtKind::Other
    }
    _ => StmtKind::Other,
  };

  builder.alloc_stmt(span, kind)
}

fn lower_for_body(body: &Node<ForBody>, builder: &mut BodyBuilder<'_>) {
  for stmt in body.stx.body.iter() {
    lower_stmt(stmt, builder);
  }
}

fn lower_for_lhs(lhs: &ForInOfLhs, builder: &mut BodyBuilder<'_>) {
  match lhs {
    ForInOfLhs::Assign(pat) => {
      lower_pat(pat, builder);
    }
    ForInOfLhs::Decl((_, pat_decl)) => {
      lower_pat(&pat_decl.stx.pat, builder);
    }
  }
}

fn lower_var_decl(decl: &Node<parse_js::ast::stmt::decl::VarDecl>, builder: &mut BodyBuilder<'_>) {
  for declarator in decl.stx.declarators.iter() {
    lower_pat(&declarator.pattern.stx.pat, builder);
    if let Some(init) = &declarator.initializer {
      lower_expr(init, builder);
    }
  }
}

fn lower_block_stmt(block: &Node<parse_js::ast::stmt::BlockStmt>, builder: &mut BodyBuilder<'_>) {
  for stmt in block.stx.body.iter() {
    lower_stmt(stmt, builder);
  }
}

fn lower_catch(catch: &Node<CatchBlock>, builder: &mut BodyBuilder<'_>) {
  if let Some(param) = &catch.stx.parameter {
    lower_pat(&param.stx.pat, builder);
  }
  for stmt in catch.stx.body.iter() {
    lower_stmt(stmt, builder);
  }
}

fn lower_expr(expr: &Node<AstExpr>, builder: &mut BodyBuilder<'_>) -> ExprId {
  let span = to_range(expr.loc);
  let kind = match &*expr.stx {
    AstExpr::Id(id) => ExprKind::Ident(builder.intern_name(&id.stx.name)),
    AstExpr::Binary(bin) => {
      let left = lower_expr(&bin.stx.left, builder);
      let right = lower_expr(&bin.stx.right, builder);
      ExprKind::Binary { left, right }
    }
    AstExpr::Call(call) => {
      let callee = lower_expr(&call.stx.callee, builder);
      let args = call
        .stx
        .arguments
        .iter()
        .map(|arg| lower_expr(&arg.stx.value, builder))
        .collect();
      ExprKind::Call {
        callee,
        args,
        optional: call.stx.optional_chaining,
      }
    }
    AstExpr::Member(mem) => {
      let object = lower_expr(&mem.stx.left, builder);
      let property = builder.intern_name(&mem.stx.right);
      ExprKind::Member {
        object,
        property,
        optional: mem.stx.optional_chaining,
      }
    }
    AstExpr::ComputedMember(mem) => {
      lower_expr(&mem.stx.object, builder);
      lower_expr(&mem.stx.member, builder);
      ExprKind::Other
    }
    AstExpr::Cond(cond) => {
      let test = lower_expr(&cond.stx.test, builder);
      let cons = lower_expr(&cond.stx.consequent, builder);
      let alt = lower_expr(&cond.stx.alternate, builder);
      ExprKind::Conditional {
        test,
        consequent: cons,
        alternate: alt,
      }
    }
    AstExpr::Func(_) | AstExpr::ArrowFunc(_) | AstExpr::Class(_) => ExprKind::Other,
    AstExpr::IdPat(id_pat) => {
      let name = builder.intern_name(&id_pat.stx.name);
      let _ = builder.alloc_pat(span, PatKind::Ident(name));
      ExprKind::Other
    }
    AstExpr::ArrPat(arr) => {
      let kind = lower_arr_pat(arr, builder);
      builder.alloc_pat(to_range(arr.loc), kind);
      ExprKind::Other
    }
    AstExpr::ObjPat(obj) => {
      let kind = lower_obj_pat(obj, builder);
      builder.alloc_pat(to_range(obj.loc), kind);
      ExprKind::Other
    }
    AstExpr::Unary(unary) => {
      lower_expr(&unary.stx.argument, builder);
      ExprKind::Other
    }
    AstExpr::UnaryPostfix(post) => {
      lower_expr(&post.stx.argument, builder);
      ExprKind::Other
    }
    AstExpr::TaggedTemplate(tag) => {
      lower_expr(&tag.stx.function, builder);
      for part in tag.stx.parts.iter() {
        if let parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) = part {
          lower_expr(expr, builder);
        }
      }
      ExprKind::Other
    }
    AstExpr::LitArr(arr) => {
      for element in arr.stx.elements.iter() {
        match element {
          parse_js::ast::expr::lit::LitArrElem::Single(expr)
          | parse_js::ast::expr::lit::LitArrElem::Rest(expr) => {
            lower_expr(expr, builder);
          }
          parse_js::ast::expr::lit::LitArrElem::Empty => {}
        }
      }
      ExprKind::Array
    }
    AstExpr::LitObj(obj) => {
      use parse_js::ast::class_or_object::ClassOrObjVal;
      use parse_js::ast::class_or_object::ObjMemberType;
      for member in obj.stx.members.iter() {
        match &member.stx.typ {
          ObjMemberType::Valued { val, .. } => match val {
            ClassOrObjVal::Prop(Some(expr)) => {
              lower_expr(expr, builder);
            }
            ClassOrObjVal::StaticBlock(block) => {
              for stmt in block.stx.body.iter() {
                lower_stmt(stmt, builder);
              }
            }
            ClassOrObjVal::Getter(_) | ClassOrObjVal::Setter(_) | ClassOrObjVal::Method(_) => {}
            ClassOrObjVal::Prop(None) | ClassOrObjVal::IndexSignature(_) => {}
          },
          ObjMemberType::Shorthand { id } => {
            let _ = builder.intern_name(&id.stx.name);
          }
          ObjMemberType::Rest { val } => {
            lower_expr(val, builder);
          }
        }
      }
      ExprKind::Object
    }
    AstExpr::LitTemplate(tmpl) => {
      for part in tmpl.stx.parts.iter() {
        if let parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) = part {
          lower_expr(expr, builder);
        }
      }
      ExprKind::Other
    }
    AstExpr::This(_) => ExprKind::This,
    AstExpr::Super(_) => ExprKind::Super,
    _ => ExprKind::Other,
  };

  builder.alloc_expr(span, kind)
}

fn lower_pat(pat: &Node<AstPat>, builder: &mut BodyBuilder<'_>) -> PatId {
  let span = to_range(pat.loc);
  let kind = match &*pat.stx {
    AstPat::Id(id) => PatKind::Ident(builder.intern_name(&id.stx.name)),
    AstPat::Arr(arr) => lower_arr_pat(arr, builder),
    AstPat::Obj(obj) => lower_obj_pat(obj, builder),
    AstPat::AssignTarget(expr) => {
      let expr_id = lower_expr(expr, builder);
      PatKind::AssignTarget(expr_id)
    }
  };

  builder.alloc_pat(span, kind)
}

fn lower_arr_pat(arr: &Node<ArrPat>, builder: &mut BodyBuilder<'_>) -> PatKind {
  let mut children = Vec::new();
  for elem in arr.stx.elements.iter().flatten() {
    children.push(lower_pat(&elem.target, builder));
    if let Some(default) = &elem.default_value {
      lower_expr(default, builder);
    }
  }
  if let Some(rest) = &arr.stx.rest {
    children.push(lower_pat(rest, builder));
  }
  PatKind::Destructure(children)
}

fn lower_obj_pat(obj: &Node<ObjPat>, builder: &mut BodyBuilder<'_>) -> PatKind {
  let mut children = Vec::new();
  for prop in obj.stx.properties.iter() {
    children.push(lower_pat(&prop.stx.target, builder));
    if let Some(default) = &prop.stx.default_value {
      lower_expr(default, builder);
    }
  }
  if let Some(rest) = &obj.stx.rest {
    children.push(lower_pat(rest, builder));
  }
  PatKind::Destructure(children)
}

struct BodyBuilder<'a> {
  owner: DefId,
  kind: BodyKind,
  exprs: Vec<Expr>,
  stmts: Vec<Stmt>,
  pats: Vec<Pat>,
  names: &'a mut NameInterner,
  span_map: &'a mut SpanMap,
}

impl<'a> BodyBuilder<'a> {
  fn new(
    owner: DefId,
    kind: BodyKind,
    names: &'a mut NameInterner,
    span_map: &'a mut SpanMap,
  ) -> Self {
    Self {
      owner,
      kind,
      exprs: Vec::new(),
      stmts: Vec::new(),
      pats: Vec::new(),
      names,
      span_map,
    }
  }

  fn alloc_expr(&mut self, span: TextRange, kind: ExprKind) -> ExprId {
    let id = ExprId(self.exprs.len() as u32);
    self.exprs.push(Expr { span, kind });
    self.span_map.add_expr(span, id);
    id
  }

  fn alloc_pat(&mut self, span: TextRange, kind: PatKind) -> PatId {
    let id = PatId(self.pats.len() as u32);
    self.pats.push(Pat { span, kind });
    id
  }

  fn alloc_stmt(&mut self, span: TextRange, kind: StmtKind) -> StmtId {
    let id = StmtId(self.stmts.len() as u32);
    self.stmts.push(Stmt { span, kind });
    id
  }

  fn finish(self) -> Body {
    Body {
      owner: self.owner,
      kind: self.kind,
      exprs: self.exprs,
      stmts: self.stmts,
      pats: self.pats,
      expr_types: None,
    }
  }

  fn intern_name(&mut self, name: &str) -> NameId {
    self.names.intern(name)
  }
}

fn collect_top_level<'a>(
  file: FileId,
  ast: &'a Node<TopLevel>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
) {
  for stmt in ast.stx.body.iter() {
    collect_stmt(file, stmt, descriptors, names, true);
  }
}

fn collect_stmt<'a>(
  file: FileId,
  stmt: &'a Node<AstStmt>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
  is_item: bool,
) {
  match &*stmt.stx {
    AstStmt::FunctionDecl(func) => {
      let (name_id, name_text) = name_from_optional(&func.stx.name, names);
      let span = to_range(stmt.loc);
      descriptors.push(DefDescriptor::new(
        DefKind::Function,
        name_id,
        name_text,
        span,
        is_item,
        DefSource::Function(func),
      ));
      collect_func_params(&func.stx.function, descriptors, names);
    }
    AstStmt::ClassDecl(class_decl) => {
      let (name_id, name_text) = name_from_optional(&class_decl.stx.name, names);
      let span = to_range(stmt.loc);
      descriptors.push(DefDescriptor::new(
        DefKind::Class,
        name_id,
        name_text,
        span,
        is_item,
        DefSource::None,
      ));
    }
    AstStmt::VarDecl(var_decl) => {
      collect_var_decl(var_decl, descriptors, names, is_item);
    }
    AstStmt::NamespaceDecl(ns) => collect_namespace(file, ns, descriptors, names, is_item),
    AstStmt::ModuleDecl(module) => {
      let name_text = match &module.stx.name {
        ModuleName::Identifier(name) => name.clone(),
        ModuleName::String(name) => name.clone(),
      };
      let name_id = names.intern(&name_text);
      descriptors.push(DefDescriptor::new(
        DefKind::Module,
        name_id,
        name_text,
        to_range(stmt.loc),
        is_item,
        DefSource::None,
      ));
      if let Some(body) = &module.stx.body {
        for st in body.iter() {
          collect_stmt(file, st, descriptors, names, false);
        }
      }
    }
    AstStmt::InterfaceDecl(intf) => {
      let name_id = names.intern(&intf.stx.name);
      let text = names.resolve(name_id).unwrap().to_string();
      descriptors.push(DefDescriptor::new(
        DefKind::Interface,
        name_id,
        text,
        to_range(stmt.loc),
        is_item,
        DefSource::None,
      ));
    }
    AstStmt::TypeAliasDecl(ta) => {
      let name_id = names.intern(&ta.stx.name);
      let text = names.resolve(name_id).unwrap().to_string();
      descriptors.push(DefDescriptor::new(
        DefKind::TypeAlias,
        name_id,
        text,
        to_range(stmt.loc),
        is_item,
        DefSource::None,
      ));
    }
    AstStmt::EnumDecl(en) => {
      let name_id = names.intern(&en.stx.name);
      let text = names.resolve(name_id).unwrap().to_string();
      descriptors.push(DefDescriptor::new(
        DefKind::Enum,
        name_id,
        text,
        to_range(stmt.loc),
        is_item,
        DefSource::None,
      ));
    }
    AstStmt::Import(stmt_import) => {
      if let Some(default) = &stmt_import.stx.default {
        let pat_names = collect_pat_names(&default.stx.pat, names);
        for (id, span) in pat_names {
          descriptors.push(DefDescriptor::new(
            DefKind::ImportBinding,
            id,
            names.resolve(id).unwrap().to_string(),
            span,
            is_item,
            DefSource::None,
          ));
        }
      }
      if let Some(names_list) = &stmt_import.stx.names {
        match names_list {
          ImportNames::All(pat) => {
            let pat_names = collect_pat_names(&pat.stx.pat, names);
            for (id, span) in pat_names {
              descriptors.push(DefDescriptor::new(
                DefKind::ImportBinding,
                id,
                names.resolve(id).unwrap().to_string(),
                span,
                is_item,
                DefSource::None,
              ));
            }
          }
          ImportNames::Specific(list) => {
            for item in list.iter() {
              let pat_names = collect_pat_names(&item.stx.alias.stx.pat, names);
              for (id, span) in pat_names {
                descriptors.push(DefDescriptor::new(
                  DefKind::ImportBinding,
                  id,
                  names.resolve(id).unwrap().to_string(),
                  span,
                  is_item,
                  DefSource::None,
                ));
              }
            }
          }
        }
      }
    }
    AstStmt::ExportList(export) => match &export.stx.names {
      ExportNames::All(Some(alias)) => {
        let name_id = names.intern(&alias.stx.name);
        descriptors.push(DefDescriptor::new(
          DefKind::ExportAlias,
          name_id,
          names.resolve(name_id).unwrap().to_string(),
          to_range(alias.loc),
          is_item,
          DefSource::None,
        ));
      }
      ExportNames::Specific(list) => {
        for export_name in list.iter() {
          let alias_node: &Node<IdPat> = &export_name.stx.alias;
          let name_id = names.intern(&alias_node.stx.name);
          descriptors.push(DefDescriptor::new(
            DefKind::ExportAlias,
            name_id,
            names.resolve(name_id).unwrap().to_string(),
            to_range(alias_node.loc),
            is_item,
            DefSource::None,
          ));
        }
      }
      _ => {}
    },
    AstStmt::ExportDefaultExpr(_) => {
      let name_id = names.intern("default");
      let span = to_range(stmt.loc);
      descriptors.push(DefDescriptor::new(
        DefKind::ExportAlias,
        name_id,
        "default".into(),
        span,
        is_item,
        DefSource::None,
      ));
    }
    AstStmt::AmbientVarDecl(av) => {
      let name_id = names.intern(&av.stx.name);
      descriptors.push(DefDescriptor::new(
        DefKind::Var,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        to_range(stmt.loc),
        is_item,
        DefSource::None,
      ));
    }
    AstStmt::AmbientFunctionDecl(af) => {
      let name_id = names.intern(&af.stx.name);
      descriptors.push(DefDescriptor::new(
        DefKind::Function,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        to_range(stmt.loc),
        is_item,
        DefSource::None,
      ));
      collect_func_params_from_parts(&af.stx.parameters, descriptors, names);
    }
    AstStmt::ImportEqualsDecl(ie) => {
      let name_id = names.intern(&ie.stx.name);
      descriptors.push(DefDescriptor::new(
        DefKind::ImportBinding,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        to_range(stmt.loc),
        is_item,
        DefSource::None,
      ));
    }
    AstStmt::ExportAssignmentDecl(_) => {
      let name_id = names.intern("export=");
      descriptors.push(DefDescriptor::new(
        DefKind::ExportAlias,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        to_range(stmt.loc),
        is_item,
        DefSource::None,
      ));
    }
    AstStmt::ForIn(for_in) => {
      match &for_in.stx.lhs {
        ForInOfLhs::Decl((_, pat_decl)) => {
          for (id, span) in collect_pat_names(&pat_decl.stx.pat, names) {
            descriptors.push(DefDescriptor::new(
              DefKind::Var,
              id,
              names.resolve(id).unwrap().to_string(),
              span,
              false,
              DefSource::None,
            ));
          }
        }
        ForInOfLhs::Assign(pat) => {
          let _ = collect_pat_names(pat, names);
        }
      }
      collect_expr(&for_in.stx.rhs, descriptors, names);
      collect_for_body(file, &for_in.stx.body, descriptors, names);
    }
    AstStmt::ForOf(for_of) => {
      match &for_of.stx.lhs {
        ForInOfLhs::Decl((_, pat_decl)) => {
          for (id, span) in collect_pat_names(&pat_decl.stx.pat, names) {
            descriptors.push(DefDescriptor::new(
              DefKind::Var,
              id,
              names.resolve(id).unwrap().to_string(),
              span,
              false,
              DefSource::None,
            ));
          }
        }
        ForInOfLhs::Assign(pat) => {
          let _ = collect_pat_names(pat, names);
        }
      }
      collect_expr(&for_of.stx.rhs, descriptors, names);
      collect_for_body(file, &for_of.stx.body, descriptors, names);
    }
    _ => {
      // Walk expressions and nested statements to ensure nested definitions are collected.
      walk_stmt_children(file, stmt, descriptors, names);
    }
  }
}

fn collect_namespace<'a>(
  file: FileId,
  ns: &'a Node<NamespaceDecl>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
  is_item: bool,
) {
  let name_id = names.intern(&ns.stx.name);
  let span = to_range(ns.loc);
  let text = names.resolve(name_id).unwrap().to_string();
  descriptors.push(DefDescriptor::new(
    DefKind::Namespace,
    name_id,
    text,
    span,
    is_item,
    DefSource::None,
  ));
  match &ns.stx.body {
    NamespaceBody::Block(stmts) => {
      for st in stmts.iter() {
        collect_stmt(file, st, descriptors, names, false);
      }
    }
    NamespaceBody::Namespace(inner) => {
      collect_namespace(file, inner, descriptors, names, false);
    }
  }
}

fn collect_var_decl<'a>(
  var_decl: &'a Node<parse_js::ast::stmt::decl::VarDecl>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
  is_item: bool,
) {
  for declarator in var_decl.stx.declarators.iter() {
    let pat_names = collect_pat_names(&declarator.pattern.stx.pat, names);
    if pat_names.is_empty() {
      let anon = names.intern("<anon>");
      descriptors.push(DefDescriptor::new(
        DefKind::Var,
        anon,
        names.resolve(anon).unwrap().to_string(),
        to_range(declarator.pattern.loc),
        is_item,
        DefSource::Var(declarator),
      ));
    } else {
      for (id, span) in pat_names {
        descriptors.push(DefDescriptor::new(
          DefKind::Var,
          id,
          names.resolve(id).unwrap().to_string(),
          span,
          is_item,
          DefSource::Var(declarator),
        ));
      }
    }
  }
}

fn walk_stmt_children<'a>(
  file: FileId,
  stmt: &'a Node<AstStmt>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
) {
  match &*stmt.stx {
    AstStmt::Expr(expr_stmt) => collect_expr(&expr_stmt.stx.expr, descriptors, names),
    AstStmt::Return(ret) => {
      if let Some(v) = &ret.stx.value {
        collect_expr(v, descriptors, names);
      }
    }
    AstStmt::If(if_stmt) => {
      collect_expr(&if_stmt.stx.test, descriptors, names);
      collect_stmt(file, &if_stmt.stx.consequent, descriptors, names, false);
      if let Some(alt) = &if_stmt.stx.alternate {
        collect_stmt(file, alt, descriptors, names, false);
      }
    }
    AstStmt::Block(block) => {
      for stmt in block.stx.body.iter() {
        collect_stmt(file, stmt, descriptors, names, false);
      }
    }
    AstStmt::While(wh) => {
      collect_expr(&wh.stx.condition, descriptors, names);
      collect_stmt(file, &wh.stx.body, descriptors, names, false);
    }
    AstStmt::DoWhile(dw) => {
      collect_expr(&dw.stx.condition, descriptors, names);
      collect_stmt(file, &dw.stx.body, descriptors, names, false);
    }
    AstStmt::ForTriple(for_stmt) => {
      match &for_stmt.stx.init {
        ForTripleStmtInit::Expr(e) => collect_expr(e, descriptors, names),
        ForTripleStmtInit::Decl(d) => collect_var_decl(d, descriptors, names, false),
        ForTripleStmtInit::None => {}
      }
      if let Some(cond) = &for_stmt.stx.cond {
        collect_expr(cond, descriptors, names);
      }
      if let Some(post) = &for_stmt.stx.post {
        collect_expr(post, descriptors, names);
      }
      collect_for_body(file, &for_stmt.stx.body, descriptors, names);
    }
    AstStmt::ForIn(for_in) => {
      match &for_in.stx.lhs {
        ForInOfLhs::Assign(p) => {
          let _ = collect_pat_names(p, names);
        }
        ForInOfLhs::Decl((_, pat_decl)) => {
          let _ = collect_pat_names(&pat_decl.stx.pat, names);
        }
      }
      collect_expr(&for_in.stx.rhs, descriptors, names);
      collect_for_body(file, &for_in.stx.body, descriptors, names);
    }
    AstStmt::ForOf(for_of) => {
      match &for_of.stx.lhs {
        ForInOfLhs::Assign(p) => {
          let _ = collect_pat_names(p, names);
        }
        ForInOfLhs::Decl((_, pat_decl)) => {
          let _ = collect_pat_names(&pat_decl.stx.pat, names);
        }
      }
      collect_expr(&for_of.stx.rhs, descriptors, names);
      collect_for_body(file, &for_of.stx.body, descriptors, names);
    }
    AstStmt::Switch(sw) => {
      collect_expr(&sw.stx.test, descriptors, names);
      for branch in sw.stx.branches.iter() {
        if let Some(case) = &branch.stx.case {
          collect_expr(case, descriptors, names);
        }
        for stmt in branch.stx.body.iter() {
          collect_stmt(file, stmt, descriptors, names, false);
        }
      }
    }
    AstStmt::Try(tr) => {
      collect_block(file, &tr.stx.wrapped, descriptors, names);
      if let Some(catch) = &tr.stx.catch {
        if let Some(param) = &catch.stx.parameter {
          let _ = collect_pat_names(&param.stx.pat, names);
        }
        for stmt in catch.stx.body.iter() {
          collect_stmt(file, stmt, descriptors, names, false);
        }
      }
      if let Some(finally) = &tr.stx.finally {
        collect_block(file, finally, descriptors, names);
      }
    }
    AstStmt::With(w) => {
      collect_expr(&w.stx.object, descriptors, names);
      collect_stmt(file, &w.stx.body, descriptors, names, false);
    }
    _ => {}
  }
}

fn collect_block<'a>(
  file: FileId,
  block: &'a Node<parse_js::ast::stmt::BlockStmt>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
) {
  for stmt in block.stx.body.iter() {
    collect_stmt(file, stmt, descriptors, names, false);
  }
}

fn collect_for_body<'a>(
  file: FileId,
  body: &'a Node<ForBody>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
) {
  for stmt in body.stx.body.iter() {
    collect_stmt(file, stmt, descriptors, names, false);
  }
}

fn collect_expr<'a>(
  expr: &'a Node<AstExpr>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
) {
  match &*expr.stx {
    AstExpr::Func(f) => {
      let (name_id, name_text) = name_from_optional(&f.stx.name, names);
      descriptors.push(DefDescriptor::new(
        DefKind::Function,
        name_id,
        name_text,
        to_range(expr.loc),
        false,
        DefSource::FuncExpr(f),
      ));
      collect_func_params(&f.stx.func, descriptors, names);
    }
    AstExpr::ArrowFunc(f) => {
      let name_id = names.intern("<arrow>");
      descriptors.push(DefDescriptor::new(
        DefKind::Function,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        to_range(expr.loc),
        false,
        DefSource::ArrowFunction(f),
      ));
      collect_func_params(&f.stx.func, descriptors, names);
    }
    AstExpr::Class(class_expr) => {
      let (name_id, text) = name_from_optional(&class_expr.stx.name, names);
      descriptors.push(DefDescriptor::new(
        DefKind::Class,
        name_id,
        text,
        to_range(expr.loc),
        false,
        DefSource::None,
      ));
    }
    AstExpr::Cond(cond) => {
      collect_expr(&cond.stx.test, descriptors, names);
      collect_expr(&cond.stx.consequent, descriptors, names);
      collect_expr(&cond.stx.alternate, descriptors, names);
    }
    AstExpr::Binary(bin) => {
      collect_expr(&bin.stx.left, descriptors, names);
      collect_expr(&bin.stx.right, descriptors, names);
    }
    AstExpr::Call(call) => {
      collect_expr(&call.stx.callee, descriptors, names);
      for arg in call.stx.arguments.iter() {
        collect_expr(&arg.stx.value, descriptors, names);
      }
    }
    AstExpr::Member(mem) => {
      collect_expr(&mem.stx.left, descriptors, names);
    }
    AstExpr::ComputedMember(mem) => {
      collect_expr(&mem.stx.object, descriptors, names);
      collect_expr(&mem.stx.member, descriptors, names);
    }
    AstExpr::TaggedTemplate(tag) => {
      collect_expr(&tag.stx.function, descriptors, names);
      for part in tag.stx.parts.iter() {
        if let parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) = part {
          collect_expr(expr, descriptors, names);
        }
      }
    }
    AstExpr::LitArr(arr) => {
      for el in arr.stx.elements.iter() {
        match el {
          parse_js::ast::expr::lit::LitArrElem::Single(expr)
          | parse_js::ast::expr::lit::LitArrElem::Rest(expr) => {
            collect_expr(expr, descriptors, names);
          }
          parse_js::ast::expr::lit::LitArrElem::Empty => {}
        }
      }
    }
    AstExpr::LitObj(obj) => {
      use parse_js::ast::class_or_object::ClassOrObjVal;
      use parse_js::ast::class_or_object::ObjMemberType;
      for member in obj.stx.members.iter() {
        match &member.stx.typ {
          ObjMemberType::Valued { val, .. } => match val {
            ClassOrObjVal::Prop(Some(expr)) => collect_expr(expr, descriptors, names),
            _ => {}
          },
          ObjMemberType::Rest { val } => collect_expr(val, descriptors, names),
          ObjMemberType::Shorthand { .. } => {}
        }
      }
    }
    AstExpr::LitTemplate(tmpl) => {
      for part in tmpl.stx.parts.iter() {
        if let parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) = part {
          collect_expr(expr, descriptors, names);
        }
      }
    }
    AstExpr::ArrPat(arr) => {
      for elem in arr.stx.elements.iter().flatten() {
        collect_exprs_from_pat(&elem.target, descriptors, names);
        if let Some(default) = &elem.default_value {
          collect_expr(default, descriptors, names);
        }
      }
      if let Some(rest) = &arr.stx.rest {
        collect_exprs_from_pat(rest, descriptors, names);
      }
    }
    AstExpr::ObjPat(obj) => {
      for prop in obj.stx.properties.iter() {
        collect_exprs_from_pat(&prop.stx.target, descriptors, names);
        if let Some(default) = &prop.stx.default_value {
          collect_expr(default, descriptors, names);
        }
      }
      if let Some(rest) = &obj.stx.rest {
        collect_exprs_from_pat(rest, descriptors, names);
      }
    }
    AstExpr::TypeAssertion(assert) => {
      collect_expr(&assert.stx.expression, descriptors, names);
    }
    AstExpr::NonNullAssertion(nn) => {
      collect_expr(&nn.stx.expression, descriptors, names);
    }
    AstExpr::SatisfiesExpr(sat) => {
      collect_expr(&sat.stx.expression, descriptors, names);
    }
    _ => {}
  }
}

fn collect_exprs_from_pat<'a>(
  pat: &'a Node<AstPat>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
) {
  match &*pat.stx {
    AstPat::Arr(arr) => {
      for elem in arr.stx.elements.iter().flatten() {
        collect_exprs_from_pat(&elem.target, descriptors, names);
        if let Some(default) = &elem.default_value {
          collect_expr(default, descriptors, names);
        }
      }
      if let Some(rest) = &arr.stx.rest {
        collect_exprs_from_pat(rest, descriptors, names);
      }
    }
    AstPat::Obj(obj) => {
      for prop in obj.stx.properties.iter() {
        collect_exprs_from_pat(&prop.stx.target, descriptors, names);
        if let Some(default) = &prop.stx.default_value {
          collect_expr(default, descriptors, names);
        }
      }
      if let Some(rest) = &obj.stx.rest {
        collect_exprs_from_pat(rest, descriptors, names);
      }
    }
    AstPat::AssignTarget(expr) => collect_expr(expr, descriptors, names),
    AstPat::Id(_) => {}
  }
}

fn name_from_optional(
  name: &Option<Node<ClassOrFuncName>>,
  names: &mut NameInterner,
) -> (NameId, String) {
  match name {
    Some(n) => {
      let id = names.intern(&n.stx.name);
      (id, names.resolve(id).unwrap().to_string())
    }
    None => {
      let id = names.intern("<anonymous>");
      (id, names.resolve(id).unwrap().to_string())
    }
  }
}

fn collect_func_params<'a>(
  func: &'a Node<Func>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
) {
  for param in func.stx.parameters.iter() {
    collect_pat_defs(&param.stx.pattern, DefKind::Param, descriptors, names);
    if let Some(default) = &param.stx.default_value {
      collect_expr(default, descriptors, names);
    }
  }
}

fn collect_func_params_from_parts<'a>(
  params: &'a [Node<AmbientFunctionParameter>],
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
) {
  for param in params.iter() {
    let id = names.intern(&param.stx.name);
    let span = to_range(param.loc);
    descriptors.push(DefDescriptor::new(
      DefKind::Param,
      id,
      names.resolve(id).unwrap().to_string(),
      span,
      false,
      DefSource::None,
    ));
  }
}

fn collect_pat_defs<'a>(
  pat_decl: &'a Node<parse_js::ast::stmt::decl::PatDecl>,
  kind: DefKind,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
) {
  for (name_id, span) in collect_pat_names(&pat_decl.stx.pat, names) {
    let text = names.resolve(name_id).unwrap().to_string();
    descriptors.push(DefDescriptor::new(
      kind,
      name_id,
      text,
      span,
      false,
      DefSource::None,
    ));
  }
}

fn collect_pat_names(pat: &Node<AstPat>, names: &mut NameInterner) -> Vec<(NameId, TextRange)> {
  let mut acc = Vec::new();
  collect_pat_names_inner(pat, names, &mut acc);
  acc
}

fn collect_pat_names_inner(
  pat: &Node<AstPat>,
  names: &mut NameInterner,
  acc: &mut Vec<(NameId, TextRange)>,
) {
  match &*pat.stx {
    AstPat::Id(id) => {
      let name_id = names.intern(&id.stx.name);
      acc.push((name_id, to_range(pat.loc)));
    }
    AstPat::Arr(arr) => {
      for elem in arr.stx.elements.iter().flatten() {
        collect_pat_names_inner(&elem.target, names, acc);
      }
      if let Some(rest) = &arr.stx.rest {
        collect_pat_names_inner(rest, names, acc);
      }
    }
    AstPat::Obj(obj) => {
      for prop in obj.stx.properties.iter() {
        collect_pat_names_inner(&prop.stx.target, names, acc);
      }
      if let Some(rest) = &obj.stx.rest {
        collect_pat_names_inner(rest, names, acc);
      }
    }
    AstPat::AssignTarget(expr) => match &*expr.stx {
      AstExpr::Id(id) => {
        let name_id = names.intern(&id.stx.name);
        acc.push((name_id, to_range(expr.loc)));
      }
      _ => {}
    },
  }
}
