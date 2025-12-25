use crate::hir::Body;
use crate::hir::BodyKind;
use crate::hir::DefData;
use crate::hir::Expr;
use crate::hir::ExprKind;
use crate::hir::FileKind;
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
use crate::ids::StableHasher;
use crate::ids::StmtId;
use crate::intern::NameInterner;
use crate::lower_types::TypeLowerer;
use crate::span_map::SpanMap;
use diagnostics::Diagnostic;
use diagnostics::FileId;
use diagnostics::Span;
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
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

struct LoweringContext {
  file: FileId,
  diagnostics: Vec<Diagnostic>,
}

impl LoweringContext {
  fn new(file: FileId) -> Self {
    Self {
      file,
      diagnostics: Vec::new(),
    }
  }

  fn to_range(&mut self, loc: Loc) -> TextRange {
    let (range, note) = loc.to_diagnostics_range_with_note();
    if let Some(note) = note {
      self.diagnostics.push(
        Diagnostic::warning(
          "LOWER0001",
          "span exceeds supported range; offsets truncated",
          Span {
            file: self.file,
            range,
          },
        )
        .with_note(note),
      );
    }
    range
  }

  fn unsupported(&mut self, range: TextRange, message: impl Into<String>) {
    self.diagnostics.push(Diagnostic::warning(
      "LOWER0002",
      message,
      Span {
        file: self.file,
        range,
      },
    ));
  }

  fn into_diagnostics(self) -> Vec<Diagnostic> {
    self.diagnostics
  }
}

#[derive(Debug, Default)]
struct IdAllocator {
  def_paths: BTreeMap<DefPath, DefId>,
  body_ids: BTreeMap<BodyKey, BodyId>,
  used_defs: BTreeSet<DefId>,
  used_bodies: BTreeSet<BodyId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct BodyKey {
  owner: DefId,
  kind: BodyKind,
}

impl IdAllocator {
  fn alloc_def(&mut self, path: DefPath) -> DefId {
    if let Some(id) = self.def_paths.get(&path) {
      return *id;
    }
    let id = self.next_def_id(path.stable_hash());
    self.def_paths.insert(path, id);
    id
  }

  fn alloc_body(&mut self, owner: DefId, kind: BodyKind) -> BodyId {
    let key = BodyKey { owner, kind };
    if let Some(id) = self.body_ids.get(&key) {
      return *id;
    }

    let mut hasher = StableHasher::new();
    hasher.write_u64(owner.0 as u64);
    hasher.write_u64(kind as u64);
    let seed = hasher.finish();
    let id = self.next_body_id(seed);
    self.body_ids.insert(key, id);
    id
  }

  fn next_def_id(&mut self, seed: u64) -> DefId {
    Self::next(seed, &mut self.used_defs, |raw| DefId(raw))
  }

  fn next_body_id(&mut self, seed: u64) -> BodyId {
    Self::next(seed, &mut self.used_bodies, |raw| BodyId(raw))
  }

  fn next<T: Copy + Ord>(seed: u64, used: &mut BTreeSet<T>, wrap: impl Fn(u32) -> T) -> T {
    let mut salt = 0u64;
    loop {
      let mut hasher = StableHasher::new();
      hasher.write_u64(seed);
      hasher.write_u64(salt);
      let candidate = wrap(hasher.finish_u32());
      if used.insert(candidate) {
        return candidate;
      }
      salt = salt.wrapping_add(1);
    }
  }
}

#[derive(Debug)]
struct DefDescriptor<'a> {
  kind: DefKind,
  name: NameId,
  name_text: String,
  span: TextRange,
  is_item: bool,
  is_ambient: bool,
  in_global: bool,
  source: DefSource<'a>,
  type_source: Option<TypeSource<'a>>,
}

#[derive(Debug)]
enum DefSource<'a> {
  None,
  Function(&'a Node<FuncDecl>),
  ArrowFunction(&'a Node<ArrowFuncExpr>),
  FuncExpr(&'a Node<FuncExpr>),
  Var(&'a VarDeclarator),
}

#[derive(Debug, Copy, Clone)]
enum TypeSource<'a> {
  TypeAlias(&'a Node<TypeAliasDecl>),
  Interface(&'a Node<InterfaceDecl>),
}

impl<'a> DefDescriptor<'a> {
  fn new(
    kind: DefKind,
    name: NameId,
    name_text: String,
    span: TextRange,
    is_item: bool,
    is_ambient: bool,
    in_global: bool,
    source: DefSource<'a>,
  ) -> Self {
    Self {
      kind,
      name,
      name_text,
      span,
      is_item,
      is_ambient,
      in_global,
      source,
      type_source: None,
    }
  }
}

/// Lower a parsed file into HIR structures, returning lowering diagnostics.
pub fn lower_file_with_diagnostics(
  file: FileId,
  file_kind: FileKind,
  ast: &Node<TopLevel>,
) -> (LowerResult, Vec<Diagnostic>) {
  let mut ctx = LoweringContext::new(file);
  let mut names = NameInterner::default();
  let mut descriptors = Vec::new();
  collect_top_level(ast, file_kind, &mut descriptors, &mut names, &mut ctx);

  descriptors.sort_by(|a, b| {
    (a.kind, a.name_text.as_str(), a.span.start).cmp(&(b.kind, b.name_text.as_str(), b.span.start))
  });

  let mut span_map = SpanMap::new();
  let mut defs = Vec::with_capacity(descriptors.len());
  let mut bodies = Vec::new();
  let mut body_ids = Vec::new();
  let mut items = Vec::new();
  let mut pending_types = Vec::new();
  let mut disambiguators: BTreeMap<(DefKind, String), u32> = BTreeMap::new();
  let mut id_allocator = IdAllocator::default();
  let mut def_index = BTreeMap::new();
  let mut body_index = BTreeMap::new();

  for desc in descriptors.into_iter() {
    let dis = disambiguators
      .entry((desc.kind, desc.name_text.clone()))
      .or_insert(0);
    let def_path = DefPath::new(file, desc.kind, desc.name_text.clone(), *dis);
    *dis += 1;

    let def_id = id_allocator.alloc_def(def_path.clone());
    if desc.is_item {
      items.push(def_id);
    }

    span_map.add_def(desc.span, def_id);

    let mut def_data = DefData {
      id: def_id,
      name: desc.name,
      path: def_path,
      span: desc.span,
      is_ambient: desc.is_ambient,
      in_global: desc.in_global,
      body: None,
      type_info: None,
    };

    if let Some(body) =
      lower_body_from_source(def_id, &desc.source, &mut names, &mut span_map, &mut ctx)
    {
      let body_id = id_allocator.alloc_body(def_id, body.kind);
      def_data.body = Some(body_id);
      body_ids.push(body_id);
      body_index.insert(body_id, bodies.len());
      bodies.push(Arc::new(body));
    }

    if let Some(type_source) = desc.type_source {
      pending_types.push((def_id, type_source));
    }

    def_index.insert(def_id, defs.len());
    defs.push(def_data);
  }

  let def_paths = id_allocator.def_paths.clone();
  let types = {
    let mut type_lowerer = TypeLowerer::new(&mut names, &mut span_map);
    for (def_id, source) in pending_types {
      let type_info = match source {
        TypeSource::TypeAlias(alias) => Some(type_lowerer.lower_type_alias(alias)),
        TypeSource::Interface(intf) => Some(type_lowerer.lower_interface(intf)),
      };
      if let Some(info) = type_info {
        if let Some(idx) = def_index.get(&def_id) {
          if let Some(def) = defs.get_mut(*idx) {
            def.type_info = Some(info);
          }
        }
      }
    }
    type_lowerer.finish()
  };

  span_map.finalize();

  (
    LowerResult {
      hir: Arc::new(HirFile::new(
        file, file_kind, items, body_ids, def_paths, span_map,
      )),
      defs,
      bodies,
      types,
      names: Arc::new(names),
      def_index,
      body_index,
    },
    ctx.into_diagnostics(),
  )
}

/// Lower a parsed file into HIR structures, discarding diagnostics.
///
/// Prefer [`lower_file_with_diagnostics`] when calling from user-facing
/// tooling so overflow and unsupported constructs can be surfaced.
pub fn lower_file(file: FileId, file_kind: FileKind, ast: &Node<TopLevel>) -> LowerResult {
  lower_file_with_diagnostics(file, file_kind, ast).0
}

fn lower_body_from_source(
  owner: DefId,
  source: &DefSource,
  names: &mut NameInterner,
  span_map: &mut SpanMap,
  ctx: &mut LoweringContext,
) -> Option<Body> {
  match source {
    DefSource::Function(decl) => {
      lower_function_body(owner, &decl.stx.function, names, span_map, ctx)
    }
    DefSource::ArrowFunction(func) => {
      lower_function_body(owner, &func.stx.func, names, span_map, ctx)
    }
    DefSource::FuncExpr(func) => lower_function_body(owner, &func.stx.func, names, span_map, ctx),
    DefSource::Var(decl) => lower_var_body(owner, decl, names, span_map, ctx),
    DefSource::None => None,
  }
}

fn lower_var_body(
  owner: DefId,
  decl: &VarDeclarator,
  names: &mut NameInterner,
  span_map: &mut SpanMap,
  ctx: &mut LoweringContext,
) -> Option<Body> {
  let mut builder = BodyBuilder::new(owner, BodyKind::Initializer, names, span_map);
  lower_pat(&decl.pattern.stx.pat, &mut builder, ctx);
  if let Some(init) = &decl.initializer {
    let expr_id = lower_expr(init, &mut builder, ctx);
    builder.alloc_stmt(ctx.to_range(init.loc), StmtKind::Expr(expr_id));
  }
  Some(builder.finish())
}

fn lower_function_body(
  owner: DefId,
  func: &Node<Func>,
  names: &mut NameInterner,
  span_map: &mut SpanMap,
  ctx: &mut LoweringContext,
) -> Option<Body> {
  let mut builder = BodyBuilder::new(owner, BodyKind::Function, names, span_map);
  for param in func.stx.parameters.iter() {
    lower_pat(&param.stx.pattern.stx.pat, &mut builder, ctx);
    if let Some(default) = &param.stx.default_value {
      lower_expr(default, &mut builder, ctx);
    }
  }

  match &func.stx.body {
    Some(FuncBody::Block(stmts)) => {
      for stmt in stmts.iter() {
        lower_stmt(stmt, &mut builder, ctx);
      }
    }
    Some(FuncBody::Expression(expr)) => {
      let expr_id = lower_expr(expr, &mut builder, ctx);
      builder.alloc_stmt(ctx.to_range(expr.loc), StmtKind::Return(Some(expr_id)));
    }
    None => {}
  }

  Some(builder.finish())
}

fn lower_stmt(
  stmt: &Node<AstStmt>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> StmtId {
  let span = ctx.to_range(stmt.loc);
  let kind = match &*stmt.stx {
    AstStmt::Expr(expr_stmt) => {
      let expr_id = lower_expr(&expr_stmt.stx.expr, builder, ctx);
      StmtKind::Expr(expr_id)
    }
    AstStmt::Return(ret) => {
      let value = ret.stx.value.as_ref().map(|v| lower_expr(v, builder, ctx));
      StmtKind::Return(value)
    }
    AstStmt::Block(block) => {
      let mut stmts = Vec::new();
      for s in block.stx.body.iter() {
        stmts.push(lower_stmt(s, builder, ctx));
      }
      StmtKind::Block(stmts)
    }
    AstStmt::If(if_stmt) => {
      lower_expr(&if_stmt.stx.test, builder, ctx);
      lower_stmt(&if_stmt.stx.consequent, builder, ctx);
      if let Some(alt) = &if_stmt.stx.alternate {
        lower_stmt(alt, builder, ctx);
      }
      StmtKind::Other
    }
    AstStmt::While(wh) => {
      lower_expr(&wh.stx.condition, builder, ctx);
      lower_stmt(&wh.stx.body, builder, ctx);
      StmtKind::Other
    }
    AstStmt::DoWhile(dw) => {
      lower_expr(&dw.stx.condition, builder, ctx);
      lower_stmt(&dw.stx.body, builder, ctx);
      StmtKind::Other
    }
    AstStmt::ForTriple(for_stmt) => {
      match &for_stmt.stx.init {
        ForTripleStmtInit::Expr(e) => {
          lower_expr(e, builder, ctx);
        }
        ForTripleStmtInit::Decl(decl) => {
          lower_var_decl(decl, builder, ctx);
        }
        ForTripleStmtInit::None => {}
      }
      if let Some(cond) = &for_stmt.stx.cond {
        lower_expr(cond, builder, ctx);
      }
      if let Some(post) = &for_stmt.stx.post {
        lower_expr(post, builder, ctx);
      }
      lower_for_body(&for_stmt.stx.body, builder, ctx);
      StmtKind::Other
    }
    AstStmt::ForIn(for_in) => {
      lower_for_lhs(&for_in.stx.lhs, builder, ctx);
      lower_expr(&for_in.stx.rhs, builder, ctx);
      lower_for_body(&for_in.stx.body, builder, ctx);
      StmtKind::Other
    }
    AstStmt::ForOf(for_of) => {
      lower_for_lhs(&for_of.stx.lhs, builder, ctx);
      lower_expr(&for_of.stx.rhs, builder, ctx);
      lower_for_body(&for_of.stx.body, builder, ctx);
      StmtKind::Other
    }
    AstStmt::Switch(sw) => {
      lower_expr(&sw.stx.test, builder, ctx);
      for branch in sw.stx.branches.iter() {
        if let Some(case) = &branch.stx.case {
          lower_expr(case, builder, ctx);
        }
        for stmt in branch.stx.body.iter() {
          lower_stmt(stmt, builder, ctx);
        }
      }
      StmtKind::Other
    }
    AstStmt::Try(tr) => {
      lower_block_stmt(&tr.stx.wrapped, builder, ctx);
      if let Some(catch) = &tr.stx.catch {
        lower_catch(catch, builder, ctx);
      }
      if let Some(finally) = &tr.stx.finally {
        lower_block_stmt(finally, builder, ctx);
      }
      StmtKind::Other
    }
    AstStmt::Throw(th) => {
      lower_expr(&th.stx.value, builder, ctx);
      StmtKind::Other
    }
    AstStmt::Label(label) => {
      lower_stmt(&label.stx.statement, builder, ctx);
      StmtKind::Other
    }
    AstStmt::With(w) => {
      lower_expr(&w.stx.object, builder, ctx);
      lower_stmt(&w.stx.body, builder, ctx);
      StmtKind::Other
    }
    AstStmt::VarDecl(decl) => {
      lower_var_decl(decl, builder, ctx);
      StmtKind::Other
    }
    _ => StmtKind::Other,
  };

  builder.alloc_stmt(span, kind)
}

fn lower_for_body(body: &Node<ForBody>, builder: &mut BodyBuilder<'_>, ctx: &mut LoweringContext) {
  for stmt in body.stx.body.iter() {
    lower_stmt(stmt, builder, ctx);
  }
}

fn lower_for_lhs(lhs: &ForInOfLhs, builder: &mut BodyBuilder<'_>, ctx: &mut LoweringContext) {
  match lhs {
    ForInOfLhs::Assign(pat) => {
      lower_pat(pat, builder, ctx);
    }
    ForInOfLhs::Decl((_, pat_decl)) => {
      lower_pat(&pat_decl.stx.pat, builder, ctx);
    }
  }
}

fn lower_var_decl(
  decl: &Node<parse_js::ast::stmt::decl::VarDecl>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) {
  for declarator in decl.stx.declarators.iter() {
    lower_pat(&declarator.pattern.stx.pat, builder, ctx);
    if let Some(init) = &declarator.initializer {
      lower_expr(init, builder, ctx);
    }
  }
}

fn lower_block_stmt(
  block: &Node<parse_js::ast::stmt::BlockStmt>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) {
  for stmt in block.stx.body.iter() {
    lower_stmt(stmt, builder, ctx);
  }
}

fn lower_catch(catch: &Node<CatchBlock>, builder: &mut BodyBuilder<'_>, ctx: &mut LoweringContext) {
  if let Some(param) = &catch.stx.parameter {
    lower_pat(&param.stx.pat, builder, ctx);
  }
  for stmt in catch.stx.body.iter() {
    lower_stmt(stmt, builder, ctx);
  }
}

fn lower_expr(
  expr: &Node<AstExpr>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> ExprId {
  let span = ctx.to_range(expr.loc);
  let kind = match &*expr.stx {
    AstExpr::Id(id) => ExprKind::Ident(builder.intern_name(&id.stx.name)),
    AstExpr::Binary(bin) => {
      let left = lower_expr(&bin.stx.left, builder, ctx);
      let right = lower_expr(&bin.stx.right, builder, ctx);
      ExprKind::Binary { left, right }
    }
    AstExpr::Call(call) => {
      let callee = lower_expr(&call.stx.callee, builder, ctx);
      let args = call
        .stx
        .arguments
        .iter()
        .map(|arg| lower_expr(&arg.stx.value, builder, ctx))
        .collect();
      ExprKind::Call {
        callee,
        args,
        optional: call.stx.optional_chaining,
      }
    }
    AstExpr::Member(mem) => {
      let object = lower_expr(&mem.stx.left, builder, ctx);
      let property = builder.intern_name(&mem.stx.right);
      ExprKind::Member {
        object,
        property,
        optional: mem.stx.optional_chaining,
      }
    }
    AstExpr::ComputedMember(mem) => {
      lower_expr(&mem.stx.object, builder, ctx);
      lower_expr(&mem.stx.member, builder, ctx);
      ExprKind::Other
    }
    AstExpr::Cond(cond) => {
      let test = lower_expr(&cond.stx.test, builder, ctx);
      let cons = lower_expr(&cond.stx.consequent, builder, ctx);
      let alt = lower_expr(&cond.stx.alternate, builder, ctx);
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
      let kind = lower_arr_pat(arr, builder, ctx);
      builder.alloc_pat(ctx.to_range(arr.loc), kind);
      ExprKind::Other
    }
    AstExpr::ObjPat(obj) => {
      let kind = lower_obj_pat(obj, builder, ctx);
      builder.alloc_pat(ctx.to_range(obj.loc), kind);
      ExprKind::Other
    }
    AstExpr::Unary(unary) => {
      lower_expr(&unary.stx.argument, builder, ctx);
      ExprKind::Other
    }
    AstExpr::UnaryPostfix(post) => {
      lower_expr(&post.stx.argument, builder, ctx);
      ExprKind::Other
    }
    AstExpr::TaggedTemplate(tag) => {
      lower_expr(&tag.stx.function, builder, ctx);
      for part in tag.stx.parts.iter() {
        if let parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) = part {
          lower_expr(expr, builder, ctx);
        }
      }
      ExprKind::Other
    }
    AstExpr::LitArr(arr) => {
      for element in arr.stx.elements.iter() {
        match element {
          parse_js::ast::expr::lit::LitArrElem::Single(expr)
          | parse_js::ast::expr::lit::LitArrElem::Rest(expr) => {
            lower_expr(expr, builder, ctx);
          }
          parse_js::ast::expr::lit::LitArrElem::Empty => {}
        }
      }
      ExprKind::Array
    }
    AstExpr::LitObj(obj) => {
      use parse_js::ast::class_or_object::ClassOrObjKey;
      use parse_js::ast::class_or_object::ClassOrObjVal;
      use parse_js::ast::class_or_object::ObjMemberType;
      for member in obj.stx.members.iter() {
        match &member.stx.typ {
          ObjMemberType::Valued { key, val } => {
            if let ClassOrObjKey::Computed(key_expr) = key {
              let key_span = ctx.to_range(key_expr.loc);
              ctx.unsupported(key_span, "computed property keys are not lowered yet");
              lower_expr(key_expr, builder, ctx);
            }
            match val {
              ClassOrObjVal::Prop(Some(expr)) => {
                lower_expr(expr, builder, ctx);
              }
              ClassOrObjVal::StaticBlock(block) => {
                for stmt in block.stx.body.iter() {
                  lower_stmt(stmt, builder, ctx);
                }
              }
              ClassOrObjVal::Getter(_) | ClassOrObjVal::Setter(_) | ClassOrObjVal::Method(_) => {}
              ClassOrObjVal::Prop(None) | ClassOrObjVal::IndexSignature(_) => {}
            }
          }
          ObjMemberType::Shorthand { id } => {
            let _ = builder.intern_name(&id.stx.name);
          }
          ObjMemberType::Rest { val } => {
            lower_expr(val, builder, ctx);
          }
        }
      }
      ExprKind::Object
    }
    AstExpr::LitTemplate(tmpl) => {
      for part in tmpl.stx.parts.iter() {
        if let parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) = part {
          lower_expr(expr, builder, ctx);
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

fn lower_pat(
  pat: &Node<AstPat>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> PatId {
  let span = ctx.to_range(pat.loc);
  let kind = match &*pat.stx {
    AstPat::Id(id) => PatKind::Ident(builder.intern_name(&id.stx.name)),
    AstPat::Arr(arr) => lower_arr_pat(arr, builder, ctx),
    AstPat::Obj(obj) => lower_obj_pat(obj, builder, ctx),
    AstPat::AssignTarget(expr) => {
      let expr_id = lower_expr(expr, builder, ctx);
      PatKind::AssignTarget(expr_id)
    }
  };

  builder.alloc_pat(span, kind)
}

fn lower_arr_pat(
  arr: &Node<ArrPat>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> PatKind {
  let mut children = Vec::new();
  for elem in arr.stx.elements.iter().flatten() {
    children.push(lower_pat(&elem.target, builder, ctx));
    if let Some(default) = &elem.default_value {
      lower_expr(default, builder, ctx);
    }
  }
  if let Some(rest) = &arr.stx.rest {
    children.push(lower_pat(rest, builder, ctx));
  }
  PatKind::Destructure(children)
}

fn lower_obj_pat(
  obj: &Node<ObjPat>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> PatKind {
  let mut children = Vec::new();
  for prop in obj.stx.properties.iter() {
    children.push(lower_pat(&prop.stx.target, builder, ctx));
    if let Some(default) = &prop.stx.default_value {
      lower_expr(default, builder, ctx);
    }
  }
  if let Some(rest) = &obj.stx.rest {
    children.push(lower_pat(rest, builder, ctx));
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
  ast: &'a Node<TopLevel>,
  file_kind: FileKind,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
  ctx: &mut LoweringContext,
) {
  let ambient = matches!(file_kind, FileKind::Dts);
  for stmt in ast.stx.body.iter() {
    collect_stmt(stmt, descriptors, names, true, ambient, false, ctx);
  }
}

fn collect_stmt<'a>(
  stmt: &'a Node<AstStmt>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
  is_item: bool,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  match &*stmt.stx {
    AstStmt::FunctionDecl(func) => {
      let (name_id, name_text) = name_from_optional(&func.stx.name, names);
      let span = ctx.to_range(stmt.loc);
      let decl_ambient = ambient;
      descriptors.push(DefDescriptor::new(
        DefKind::Function,
        name_id,
        name_text,
        span,
        is_item,
        decl_ambient,
        in_global,
        DefSource::Function(func),
      ));
      collect_func_params(
        &func.stx.function,
        descriptors,
        names,
        decl_ambient,
        in_global,
        ctx,
      );
    }
    AstStmt::ClassDecl(class_decl) => {
      let (name_id, name_text) = name_from_optional(&class_decl.stx.name, names);
      let span = ctx.to_range(stmt.loc);
      let decl_ambient = ambient || class_decl.stx.declare;
      descriptors.push(DefDescriptor::new(
        DefKind::Class,
        name_id,
        name_text,
        span,
        is_item,
        decl_ambient,
        in_global,
        DefSource::None,
      ));
    }
    AstStmt::VarDecl(var_decl) => {
      collect_var_decl(
        var_decl,
        descriptors,
        names,
        is_item,
        ambient,
        in_global,
        ctx,
      );
    }
    AstStmt::NamespaceDecl(ns) => {
      let decl_ambient = ambient || ns.stx.declare;
      collect_namespace(
        ns,
        descriptors,
        names,
        is_item,
        decl_ambient,
        in_global,
        ctx,
      )
    }
    AstStmt::ModuleDecl(module) => {
      let name_text = match &module.stx.name {
        ModuleName::Identifier(name) => name.clone(),
        ModuleName::String(name) => name.clone(),
      };
      let name_id = names.intern(&name_text);
      let decl_ambient = ambient || module.stx.declare;
      descriptors.push(DefDescriptor::new(
        DefKind::Module,
        name_id,
        name_text,
        ctx.to_range(stmt.loc),
        is_item,
        decl_ambient,
        in_global,
        DefSource::None,
      ));
      if let Some(body) = &module.stx.body {
        for st in body.iter() {
          collect_stmt(st, descriptors, names, false, decl_ambient, in_global, ctx);
        }
      }
    }
    AstStmt::GlobalDecl(global) => {
      for st in global.stx.body.iter() {
        collect_stmt(st, descriptors, names, true, true, true, ctx);
      }
    }
    AstStmt::InterfaceDecl(intf) => {
      let name_id = names.intern(&intf.stx.name);
      let text = names.resolve(name_id).unwrap().to_string();
      let decl_ambient = ambient || intf.stx.declare;
      let mut desc = DefDescriptor::new(
        DefKind::Interface,
        name_id,
        text,
        ctx.to_range(stmt.loc),
        is_item,
        decl_ambient,
        in_global,
        DefSource::None,
      );
      desc.type_source = Some(TypeSource::Interface(intf));
      descriptors.push(desc);
    }
    AstStmt::TypeAliasDecl(ta) => {
      let name_id = names.intern(&ta.stx.name);
      let text = names.resolve(name_id).unwrap().to_string();
      let decl_ambient = ambient || ta.stx.declare;
      let mut desc = DefDescriptor::new(
        DefKind::TypeAlias,
        name_id,
        text,
        ctx.to_range(stmt.loc),
        is_item,
        decl_ambient,
        in_global,
        DefSource::None,
      );
      desc.type_source = Some(TypeSource::TypeAlias(ta));
      descriptors.push(desc);
    }
    AstStmt::EnumDecl(en) => {
      let name_id = names.intern(&en.stx.name);
      let text = names.resolve(name_id).unwrap().to_string();
      let decl_ambient = ambient || en.stx.declare;
      descriptors.push(DefDescriptor::new(
        DefKind::Enum,
        name_id,
        text,
        ctx.to_range(stmt.loc),
        is_item,
        decl_ambient,
        in_global,
        DefSource::None,
      ));
    }
    AstStmt::Import(stmt_import) => {
      if let Some(default) = &stmt_import.stx.default {
        let pat_names = collect_pat_names(&default.stx.pat, names, ctx);
        for (id, span) in pat_names {
          descriptors.push(DefDescriptor::new(
            DefKind::ImportBinding,
            id,
            names.resolve(id).unwrap().to_string(),
            span,
            is_item,
            ambient,
            in_global,
            DefSource::None,
          ));
        }
      }
      if let Some(names_list) = &stmt_import.stx.names {
        match names_list {
          ImportNames::All(pat) => {
            let pat_names = collect_pat_names(&pat.stx.pat, names, ctx);
            for (id, span) in pat_names {
              descriptors.push(DefDescriptor::new(
                DefKind::ImportBinding,
                id,
                names.resolve(id).unwrap().to_string(),
                span,
                is_item,
                ambient,
                in_global,
                DefSource::None,
              ));
            }
          }
          ImportNames::Specific(list) => {
            for item in list.iter() {
              let pat_names = collect_pat_names(&item.stx.alias.stx.pat, names, ctx);
              for (id, span) in pat_names {
                descriptors.push(DefDescriptor::new(
                  DefKind::ImportBinding,
                  id,
                  names.resolve(id).unwrap().to_string(),
                  span,
                  is_item,
                  ambient,
                  in_global,
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
          ctx.to_range(alias.loc),
          is_item,
          ambient,
          in_global,
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
            ctx.to_range(alias_node.loc),
            is_item,
            ambient,
            in_global,
            DefSource::None,
          ));
        }
      }
      _ => {}
    },
    AstStmt::ExportDefaultExpr(_) => {
      let name_id = names.intern("default");
      let span = ctx.to_range(stmt.loc);
      descriptors.push(DefDescriptor::new(
        DefKind::ExportAlias,
        name_id,
        "default".into(),
        span,
        is_item,
        ambient,
        in_global,
        DefSource::None,
      ));
    }
    AstStmt::AmbientVarDecl(av) => {
      let name_id = names.intern(&av.stx.name);
      descriptors.push(DefDescriptor::new(
        DefKind::Var,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        ctx.to_range(stmt.loc),
        is_item,
        true,
        in_global,
        DefSource::None,
      ));
    }
    AstStmt::AmbientFunctionDecl(af) => {
      let name_id = names.intern(&af.stx.name);
      descriptors.push(DefDescriptor::new(
        DefKind::Function,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        ctx.to_range(stmt.loc),
        is_item,
        true,
        in_global,
        DefSource::None,
      ));
      collect_func_params_from_parts(&af.stx.parameters, descriptors, names, true, in_global, ctx);
    }
    AstStmt::ImportEqualsDecl(ie) => {
      let name_id = names.intern(&ie.stx.name);
      descriptors.push(DefDescriptor::new(
        DefKind::ImportBinding,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        ctx.to_range(stmt.loc),
        is_item,
        ambient,
        in_global,
        DefSource::None,
      ));
    }
    AstStmt::ExportAssignmentDecl(_) => {
      let name_id = names.intern("export=");
      descriptors.push(DefDescriptor::new(
        DefKind::ExportAlias,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        ctx.to_range(stmt.loc),
        is_item,
        true,
        in_global,
        DefSource::None,
      ));
    }
    AstStmt::ForIn(for_in) => {
      match &for_in.stx.lhs {
        ForInOfLhs::Decl((_, pat_decl)) => {
          for (id, span) in collect_pat_names(&pat_decl.stx.pat, names, ctx) {
            descriptors.push(DefDescriptor::new(
              DefKind::Var,
              id,
              names.resolve(id).unwrap().to_string(),
              span,
              false,
              ambient,
              in_global,
              DefSource::None,
            ));
          }
        }
        ForInOfLhs::Assign(pat) => {
          let _ = collect_pat_names(pat, names, ctx);
        }
      }
      collect_expr(&for_in.stx.rhs, descriptors, names, ambient, in_global, ctx);
      collect_for_body(
        &for_in.stx.body,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    AstStmt::ForOf(for_of) => {
      match &for_of.stx.lhs {
        ForInOfLhs::Decl((_, pat_decl)) => {
          for (id, span) in collect_pat_names(&pat_decl.stx.pat, names, ctx) {
            descriptors.push(DefDescriptor::new(
              DefKind::Var,
              id,
              names.resolve(id).unwrap().to_string(),
              span,
              false,
              ambient,
              in_global,
              DefSource::None,
            ));
          }
        }
        ForInOfLhs::Assign(pat) => {
          let _ = collect_pat_names(pat, names, ctx);
        }
      }
      collect_expr(&for_of.stx.rhs, descriptors, names, ambient, in_global, ctx);
      collect_for_body(
        &for_of.stx.body,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    _ => {
      // Walk expressions and nested statements to ensure nested definitions are collected.
      walk_stmt_children(stmt, descriptors, names, ambient, in_global, ctx);
    }
  }
}

fn collect_namespace<'a>(
  ns: &'a Node<NamespaceDecl>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
  is_item: bool,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  let name_id = names.intern(&ns.stx.name);
  let span = ctx.to_range(ns.loc);
  let text = names.resolve(name_id).unwrap().to_string();
  descriptors.push(DefDescriptor::new(
    DefKind::Namespace,
    name_id,
    text,
    span,
    is_item,
    ambient,
    in_global,
    DefSource::None,
  ));
  match &ns.stx.body {
    NamespaceBody::Block(stmts) => {
      for st in stmts.iter() {
        collect_stmt(st, descriptors, names, false, ambient, in_global, ctx);
      }
    }
    NamespaceBody::Namespace(inner) => {
      collect_namespace(inner, descriptors, names, false, ambient, in_global, ctx);
    }
  }
}

fn collect_var_decl<'a>(
  var_decl: &'a Node<parse_js::ast::stmt::decl::VarDecl>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
  is_item: bool,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  for declarator in var_decl.stx.declarators.iter() {
    let pat_names = collect_pat_names(&declarator.pattern.stx.pat, names, ctx);
    if pat_names.is_empty() {
      let anon = names.intern("<anon>");
      descriptors.push(DefDescriptor::new(
        DefKind::Var,
        anon,
        names.resolve(anon).unwrap().to_string(),
        ctx.to_range(declarator.pattern.loc),
        is_item,
        ambient,
        in_global,
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
          ambient,
          in_global,
          DefSource::Var(declarator),
        ));
      }
    }
  }
}

fn walk_stmt_children<'a>(
  stmt: &'a Node<AstStmt>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  match &*stmt.stx {
    AstStmt::Expr(expr_stmt) => collect_expr(
      &expr_stmt.stx.expr,
      descriptors,
      names,
      ambient,
      in_global,
      ctx,
    ),
    AstStmt::Return(ret) => {
      if let Some(v) = &ret.stx.value {
        collect_expr(v, descriptors, names, ambient, in_global, ctx);
      }
    }
    AstStmt::If(if_stmt) => {
      collect_expr(
        &if_stmt.stx.test,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_stmt(
        &if_stmt.stx.consequent,
        descriptors,
        names,
        false,
        ambient,
        in_global,
        ctx,
      );
      if let Some(alt) = &if_stmt.stx.alternate {
        collect_stmt(alt, descriptors, names, false, ambient, in_global, ctx);
      }
    }
    AstStmt::Block(block) => {
      for stmt in block.stx.body.iter() {
        collect_stmt(stmt, descriptors, names, false, ambient, in_global, ctx);
      }
    }
    AstStmt::While(wh) => {
      collect_expr(
        &wh.stx.condition,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_stmt(
        &wh.stx.body,
        descriptors,
        names,
        false,
        ambient,
        in_global,
        ctx,
      );
    }
    AstStmt::DoWhile(dw) => {
      collect_expr(
        &dw.stx.condition,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_stmt(
        &dw.stx.body,
        descriptors,
        names,
        false,
        ambient,
        in_global,
        ctx,
      );
    }
    AstStmt::ForTriple(for_stmt) => {
      match &for_stmt.stx.init {
        ForTripleStmtInit::Expr(e) => collect_expr(e, descriptors, names, ambient, in_global, ctx),
        ForTripleStmtInit::Decl(d) => {
          collect_var_decl(d, descriptors, names, false, ambient, in_global, ctx)
        }
        ForTripleStmtInit::None => {}
      }
      if let Some(cond) = &for_stmt.stx.cond {
        collect_expr(cond, descriptors, names, ambient, in_global, ctx);
      }
      if let Some(post) = &for_stmt.stx.post {
        collect_expr(post, descriptors, names, ambient, in_global, ctx);
      }
      collect_for_body(
        &for_stmt.stx.body,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    AstStmt::ForIn(for_in) => {
      match &for_in.stx.lhs {
        ForInOfLhs::Assign(p) => {
          let _ = collect_pat_names(p, names, ctx);
        }
        ForInOfLhs::Decl((_, pat_decl)) => {
          let _ = collect_pat_names(&pat_decl.stx.pat, names, ctx);
        }
      }
      collect_expr(&for_in.stx.rhs, descriptors, names, ambient, in_global, ctx);
      collect_for_body(
        &for_in.stx.body,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    AstStmt::ForOf(for_of) => {
      match &for_of.stx.lhs {
        ForInOfLhs::Assign(p) => {
          let _ = collect_pat_names(p, names, ctx);
        }
        ForInOfLhs::Decl((_, pat_decl)) => {
          let _ = collect_pat_names(&pat_decl.stx.pat, names, ctx);
        }
      }
      collect_expr(&for_of.stx.rhs, descriptors, names, ambient, in_global, ctx);
      collect_for_body(
        &for_of.stx.body,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    AstStmt::Switch(sw) => {
      collect_expr(&sw.stx.test, descriptors, names, ambient, in_global, ctx);
      for branch in sw.stx.branches.iter() {
        if let Some(case) = &branch.stx.case {
          collect_expr(case, descriptors, names, ambient, in_global, ctx);
        }
        for stmt in branch.stx.body.iter() {
          collect_stmt(stmt, descriptors, names, false, ambient, in_global, ctx);
        }
      }
    }
    AstStmt::Try(tr) => {
      collect_block(&tr.stx.wrapped, descriptors, names, ambient, in_global, ctx);
      if let Some(catch) = &tr.stx.catch {
        if let Some(param) = &catch.stx.parameter {
          let _ = collect_pat_names(&param.stx.pat, names, ctx);
        }
        for stmt in catch.stx.body.iter() {
          collect_stmt(stmt, descriptors, names, false, ambient, in_global, ctx);
        }
      }
      if let Some(finally) = &tr.stx.finally {
        collect_block(finally, descriptors, names, ambient, in_global, ctx);
      }
    }
    AstStmt::With(w) => {
      collect_expr(&w.stx.object, descriptors, names, ambient, in_global, ctx);
      collect_stmt(
        &w.stx.body,
        descriptors,
        names,
        false,
        ambient,
        in_global,
        ctx,
      );
    }
    _ => {}
  }
}

fn collect_block<'a>(
  block: &'a Node<parse_js::ast::stmt::BlockStmt>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  for stmt in block.stx.body.iter() {
    collect_stmt(stmt, descriptors, names, false, ambient, in_global, ctx);
  }
}

fn collect_for_body<'a>(
  body: &'a Node<ForBody>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  for stmt in body.stx.body.iter() {
    collect_stmt(stmt, descriptors, names, false, ambient, in_global, ctx);
  }
}

fn collect_expr<'a>(
  expr: &'a Node<AstExpr>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  match &*expr.stx {
    AstExpr::Func(f) => {
      let (name_id, name_text) = name_from_optional(&f.stx.name, names);
      descriptors.push(DefDescriptor::new(
        DefKind::Function,
        name_id,
        name_text,
        ctx.to_range(expr.loc),
        false,
        ambient,
        in_global,
        DefSource::FuncExpr(f),
      ));
      collect_func_params(&f.stx.func, descriptors, names, ambient, in_global, ctx);
    }
    AstExpr::ArrowFunc(f) => {
      let name_id = names.intern("<arrow>");
      descriptors.push(DefDescriptor::new(
        DefKind::Function,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        ctx.to_range(expr.loc),
        false,
        ambient,
        in_global,
        DefSource::ArrowFunction(f),
      ));
      collect_func_params(&f.stx.func, descriptors, names, ambient, in_global, ctx);
    }
    AstExpr::Class(class_expr) => {
      let (name_id, text) = name_from_optional(&class_expr.stx.name, names);
      descriptors.push(DefDescriptor::new(
        DefKind::Class,
        name_id,
        text,
        ctx.to_range(expr.loc),
        false,
        ambient,
        in_global,
        DefSource::None,
      ));
    }
    AstExpr::Cond(cond) => {
      collect_expr(&cond.stx.test, descriptors, names, ambient, in_global, ctx);
      collect_expr(
        &cond.stx.consequent,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_expr(
        &cond.stx.alternate,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    AstExpr::Binary(bin) => {
      collect_expr(&bin.stx.left, descriptors, names, ambient, in_global, ctx);
      collect_expr(&bin.stx.right, descriptors, names, ambient, in_global, ctx);
    }
    AstExpr::Call(call) => {
      collect_expr(
        &call.stx.callee,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
      for arg in call.stx.arguments.iter() {
        collect_expr(&arg.stx.value, descriptors, names, ambient, in_global, ctx);
      }
    }
    AstExpr::Member(mem) => {
      collect_expr(&mem.stx.left, descriptors, names, ambient, in_global, ctx);
    }
    AstExpr::ComputedMember(mem) => {
      collect_expr(&mem.stx.object, descriptors, names, ambient, in_global, ctx);
      collect_expr(&mem.stx.member, descriptors, names, ambient, in_global, ctx);
    }
    AstExpr::TaggedTemplate(tag) => {
      collect_expr(
        &tag.stx.function,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
      for part in tag.stx.parts.iter() {
        if let parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) = part {
          collect_expr(expr, descriptors, names, ambient, in_global, ctx);
        }
      }
    }
    AstExpr::LitArr(arr) => {
      for el in arr.stx.elements.iter() {
        match el {
          parse_js::ast::expr::lit::LitArrElem::Single(expr)
          | parse_js::ast::expr::lit::LitArrElem::Rest(expr) => {
            collect_expr(expr, descriptors, names, ambient, in_global, ctx);
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
            ClassOrObjVal::Prop(Some(expr)) => {
              collect_expr(expr, descriptors, names, ambient, in_global, ctx)
            }
            _ => {}
          },
          ObjMemberType::Rest { val } => {
            collect_expr(val, descriptors, names, ambient, in_global, ctx)
          }
          ObjMemberType::Shorthand { .. } => {}
        }
      }
    }
    AstExpr::LitTemplate(tmpl) => {
      for part in tmpl.stx.parts.iter() {
        if let parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) = part {
          collect_expr(expr, descriptors, names, ambient, in_global, ctx);
        }
      }
    }
    AstExpr::ArrPat(arr) => {
      for elem in arr.stx.elements.iter().flatten() {
        collect_exprs_from_pat(&elem.target, descriptors, names, ambient, in_global, ctx);
        if let Some(default) = &elem.default_value {
          collect_expr(default, descriptors, names, ambient, in_global, ctx);
        }
      }
      if let Some(rest) = &arr.stx.rest {
        collect_exprs_from_pat(rest, descriptors, names, ambient, in_global, ctx);
      }
    }
    AstExpr::ObjPat(obj) => {
      for prop in obj.stx.properties.iter() {
        collect_exprs_from_pat(
          &prop.stx.target,
          descriptors,
          names,
          ambient,
          in_global,
          ctx,
        );
        if let Some(default) = &prop.stx.default_value {
          collect_expr(default, descriptors, names, ambient, in_global, ctx);
        }
      }
      if let Some(rest) = &obj.stx.rest {
        collect_exprs_from_pat(rest, descriptors, names, ambient, in_global, ctx);
      }
    }
    AstExpr::TypeAssertion(assert) => {
      collect_expr(
        &assert.stx.expression,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    AstExpr::NonNullAssertion(nn) => {
      collect_expr(
        &nn.stx.expression,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    AstExpr::SatisfiesExpr(sat) => {
      collect_expr(
        &sat.stx.expression,
        descriptors,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    _ => {}
  }
}

fn collect_exprs_from_pat<'a>(
  pat: &'a Node<AstPat>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  match &*pat.stx {
    AstPat::Arr(arr) => {
      for elem in arr.stx.elements.iter().flatten() {
        collect_exprs_from_pat(&elem.target, descriptors, names, ambient, in_global, ctx);
        if let Some(default) = &elem.default_value {
          collect_expr(default, descriptors, names, ambient, in_global, ctx);
        }
      }
      if let Some(rest) = &arr.stx.rest {
        collect_exprs_from_pat(rest, descriptors, names, ambient, in_global, ctx);
      }
    }
    AstPat::Obj(obj) => {
      for prop in obj.stx.properties.iter() {
        collect_exprs_from_pat(
          &prop.stx.target,
          descriptors,
          names,
          ambient,
          in_global,
          ctx,
        );
        if let Some(default) = &prop.stx.default_value {
          collect_expr(default, descriptors, names, ambient, in_global, ctx);
        }
      }
      if let Some(rest) = &obj.stx.rest {
        collect_exprs_from_pat(rest, descriptors, names, ambient, in_global, ctx);
      }
    }
    AstPat::AssignTarget(expr) => collect_expr(expr, descriptors, names, ambient, in_global, ctx),
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
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  for param in func.stx.parameters.iter() {
    collect_pat_defs(
      &param.stx.pattern,
      DefKind::Param,
      descriptors,
      names,
      ambient,
      in_global,
      ctx,
    );
    if let Some(default) = &param.stx.default_value {
      collect_expr(default, descriptors, names, ambient, in_global, ctx);
    }
  }
}

fn collect_func_params_from_parts<'a>(
  params: &'a [Node<AmbientFunctionParameter>],
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  for param in params.iter() {
    let id = names.intern(&param.stx.name);
    let span = ctx.to_range(param.loc);
    descriptors.push(DefDescriptor::new(
      DefKind::Param,
      id,
      names.resolve(id).unwrap().to_string(),
      span,
      false,
      ambient,
      in_global,
      DefSource::None,
    ));
  }
}

fn collect_pat_defs<'a>(
  pat_decl: &'a Node<parse_js::ast::stmt::decl::PatDecl>,
  kind: DefKind,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  names: &mut NameInterner,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  for (name_id, span) in collect_pat_names(&pat_decl.stx.pat, names, ctx) {
    let text = names.resolve(name_id).unwrap().to_string();
    descriptors.push(DefDescriptor::new(
      kind,
      name_id,
      text,
      span,
      false,
      ambient,
      in_global,
      DefSource::None,
    ));
  }
}

fn collect_pat_names(
  pat: &Node<AstPat>,
  names: &mut NameInterner,
  ctx: &mut LoweringContext,
) -> Vec<(NameId, TextRange)> {
  let mut acc = Vec::new();
  collect_pat_names_inner(pat, names, &mut acc, ctx);
  acc
}

fn collect_pat_names_inner(
  pat: &Node<AstPat>,
  names: &mut NameInterner,
  acc: &mut Vec<(NameId, TextRange)>,
  ctx: &mut LoweringContext,
) {
  match &*pat.stx {
    AstPat::Id(id) => {
      let name_id = names.intern(&id.stx.name);
      acc.push((name_id, ctx.to_range(pat.loc)));
    }
    AstPat::Arr(arr) => {
      for elem in arr.stx.elements.iter().flatten() {
        collect_pat_names_inner(&elem.target, names, acc, ctx);
      }
      if let Some(rest) = &arr.stx.rest {
        collect_pat_names_inner(rest, names, acc, ctx);
      }
    }
    AstPat::Obj(obj) => {
      for prop in obj.stx.properties.iter() {
        collect_pat_names_inner(&prop.stx.target, names, acc, ctx);
      }
      if let Some(rest) = &obj.stx.rest {
        collect_pat_names_inner(rest, names, acc, ctx);
      }
    }
    AstPat::AssignTarget(expr) => match &*expr.stx {
      AstExpr::Id(id) => {
        let name_id = names.intern(&id.stx.name);
        acc.push((name_id, ctx.to_range(expr.loc)));
      }
      _ => {}
    },
  }
}
