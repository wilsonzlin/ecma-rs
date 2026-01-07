use crate::hir::{
  ArrayElement, ArrayLiteral, ArrayPat, ArrayPatElement, AssignOp, BinaryOp, Body, BodyKind,
  CallArg, CallExpr, CatchClause, ClassBody, ClassMember as HirClassMember, ClassMemberKey,
  ClassMemberKind as HirClassMemberKind, ClassMethodKind, Decorator, DefData, DefTypeInfo, Export,
  ExportAlias, ExportAll, ExportAsNamespace, ExportAssignment, ExportDefault, ExportDefaultValue,
  ExportKind, ExportNamed, ExportSpecifier, Expr, ExprKind, FileKind, ForHead, ForInit,
  FunctionBody, FunctionData, HirFile, Import, ImportBinding, ImportEquals, ImportEqualsTarget,
  ImportEs, ImportKind, ImportNamed, JsxAttr, JsxAttrValue, JsxChild, JsxElement, JsxElementName,
  JsxExprContainer, JsxMemberExpr, JsxName, Literal, LowerResult, MemberExpr, ModuleAttributes,
  ModuleSpecifier, ObjectKey, ObjectLiteral, ObjectPat, ObjectPatProp, ObjectProperty, Param, Pat,
  PatKind, Stmt, StmtKind, SwitchCase, TemplateLiteral, TemplateLiteralSpan, UnaryOp, UpdateOp,
  VarDecl, VarDeclKind, VarDeclarator,
};
use crate::ids::{
  BodyId, BodyPath, DefId, DefKind, DefPath, ExportId, ExportSpecifierId, ExprId, ImportId,
  ImportSpecifierId, NameId, PatId, StableHasher, StmtId,
};
use crate::intern::NameInterner;
use crate::lower_types::TypeLowerer;
use crate::span_map::SpanMap;
use derive_visitor::{Drive, DriveMut};
use diagnostics::Cancelled;
use diagnostics::Diagnostic;
use diagnostics::FileId;
use diagnostics::Span;
use diagnostics::TextRange;
use parse_js::ast::class_or_object::ClassMember;
use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::class_or_object::ClassOrObjVal;
use parse_js::ast::class_or_object::ClassStaticBlock;
use parse_js::ast::expr::jsx;
use parse_js::ast::expr::pat::ArrPat;
use parse_js::ast::expr::pat::ClassOrFuncName;
use parse_js::ast::expr::pat::ObjPat;
use parse_js::ast::expr::pat::Pat as AstPat;
use parse_js::ast::expr::ArrowFuncExpr;
use parse_js::ast::expr::ClassExpr;
use parse_js::ast::expr::Decorator as AstDecorator;
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::expr::FuncExpr;
use parse_js::ast::func::Func;
use parse_js::ast::func::FuncBody;
use parse_js::ast::import_export::*;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::ClassDecl;
use parse_js::ast::stmt::decl::FuncDecl;
use parse_js::ast::stmt::decl::VarDeclarator as AstVarDeclarator;
use parse_js::ast::stmt::ExportDefaultExprStmt;
use parse_js::ast::stmt::ForBody;
use parse_js::ast::stmt::ForInOfLhs;
use parse_js::ast::stmt::ForTripleStmtInit;
use parse_js::ast::stmt::Stmt as AstStmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::*;
use parse_js::loc::Loc;
use std::collections::{btree_map::Entry, BTreeMap, HashMap};
use std::panic::panic_any;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct RawNode(*const ());

impl<T: Drive + DriveMut> From<&Node<T>> for RawNode {
  fn from(value: &Node<T>) -> Self {
    Self(value as *const _ as *const ())
  }
}

pub(crate) struct LoweringContext {
  file: FileId,
  cancelled: Option<Arc<AtomicBool>>,
  diagnostics: Vec<Diagnostic>,
  parent_stack: Vec<Option<RawNode>>,
}

impl LoweringContext {
  fn new(file: FileId, cancelled: Option<Arc<AtomicBool>>) -> Self {
    Self {
      file,
      cancelled,
      diagnostics: Vec::new(),
      parent_stack: vec![None],
    }
  }

  #[inline]
  fn check_cancelled(&mut self) {
    let Some(cancelled) = self.cancelled.as_ref() else {
      return;
    };
    if cancelled.load(Ordering::Relaxed) {
      panic_any(Cancelled);
    }
  }

  pub(crate) fn to_range(&mut self, loc: Loc) -> TextRange {
    self.check_cancelled();
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

  pub(crate) fn warn(&mut self, code: &'static str, message: impl Into<String>, range: TextRange) {
    self.diagnostics.push(Diagnostic::warning(
      code,
      message,
      Span {
        file: self.file,
        range,
      },
    ));
  }

  #[allow(dead_code)]
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

  fn warn_non_module_export(&mut self, range: TextRange, message: impl Into<String>) {
    self.diagnostics.push(Diagnostic::warning(
      "LOWER0003",
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

  fn current_parent(&self) -> Option<RawNode> {
    self.parent_stack.last().copied().unwrap_or(None)
  }

  fn with_parent<F, R>(&mut self, parent: Option<RawNode>, f: F) -> R
  where
    F: FnOnce(&mut LoweringContext) -> R,
  {
    self.parent_stack.push(parent);
    let result = f(self);
    self.parent_stack.pop();
    result
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
  is_exported: bool,
  is_default_export: bool,
  depth: usize,
  parent: Option<RawNode>,
  node: Option<RawNode>,
  is_static: bool,
  source: DefSource<'a>,
  type_source: Option<TypeSource<'a>>,
}

#[derive(Debug)]
enum DefSource<'a> {
  None,
  ClassDecl(&'a Node<ClassDecl>),
  ClassExpr(&'a Node<ClassExpr>),
  ClassField(&'a Node<ClassMember>),
  ClassStaticBlock(&'a Node<ClassStaticBlock>),
  Function(&'a Node<FuncDecl>),
  ArrowFunction(&'a Node<ArrowFuncExpr>),
  FuncExpr(&'a Node<FuncExpr>),
  Enum(&'a Node<EnumDecl>),
  Var(&'a AstVarDeclarator, VarDeclKind),
  Method(&'a Node<parse_js::ast::class_or_object::ClassOrObjMethod>),
  Getter(&'a Node<parse_js::ast::class_or_object::ClassOrObjGetter>),
  Setter(&'a Node<parse_js::ast::class_or_object::ClassOrObjSetter>),
  ExportDefaultExpr(&'a Node<ExportDefaultExprStmt>),
  ExportAssignment(&'a Node<ExportAssignmentDecl>),
}

#[derive(Debug, Copy, Clone)]
enum TypeSource<'a> {
  TypeAlias(&'a Node<TypeAliasDecl>),
  Interface(&'a Node<InterfaceDecl>),
  Class(&'a Node<ClassDecl>),
  ClassExpr(&'a Node<parse_js::ast::expr::ClassExpr>),
  AmbientClass(&'a Node<AmbientClassDecl>),
  Enum(&'a Node<EnumDecl>),
  Namespace,
  Module,
}

#[derive(Debug)]
struct ModuleItem<'a> {
  span: TextRange,
  kind: ModuleItemKind<'a>,
}

#[derive(Debug)]
enum ModuleItemKind<'a> {
  Import(&'a Node<parse_js::ast::stmt::ImportStmt>),
  ImportType(&'a Node<ImportTypeDecl>),
  ImportEquals(&'a Node<ImportEqualsDecl>),
  ExportList(&'a Node<parse_js::ast::stmt::ExportListStmt>),
  ExportDefaultExpr(&'a Node<ExportDefaultExprStmt>),
  ExportType(&'a Node<ExportTypeDecl>),
  ExportAssignment(&'a Node<ExportAssignmentDecl>),
  ExportAsNamespace(&'a Node<ExportAsNamespaceDecl>),
  ExportedDecl(ExportedDecl<'a>),
}

#[derive(Debug)]
struct ExportedDecl<'a> {
  default: bool,
  type_only: bool,
  span: TextRange,
  kind: ExportedDeclKind<'a>,
}

#[derive(Debug)]
enum ExportedDeclKind<'a> {
  Func(&'a Node<FuncDecl>),
  Class(&'a Node<ClassDecl>),
  Var(&'a Node<parse_js::ast::stmt::decl::VarDecl>),
  Interface(&'a Node<InterfaceDecl>),
  TypeAlias(&'a Node<TypeAliasDecl>),
  Enum(&'a Node<EnumDecl>),
  Namespace(&'a Node<NamespaceDecl>),
  Module(&'a Node<ModuleDecl>),
  AmbientVar(&'a Node<AmbientVarDecl>),
  AmbientFunction(&'a Node<AmbientFunctionDecl>),
  AmbientClass(&'a Node<AmbientClassDecl>),
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
      is_exported: false,
      is_default_export: false,
      depth: 0,
      parent: None,
      node: None,
      is_static: false,
      source,
      type_source: None,
    }
  }
}

#[derive(Default)]
struct DefLookup {
  node_to_def: HashMap<RawNode, DefId>,
  def_bodies: HashMap<DefId, BodyId>,
}

#[derive(Default)]
struct DecoratorStore {
  by_def: HashMap<DefId, Vec<Decorator>>,
  params_by_def: HashMap<DefId, Vec<Vec<Decorator>>>,
}

fn compute_descriptor_depths(descriptors: &mut [DefDescriptor<'_>]) {
  let mut raw_to_desc: HashMap<RawNode, usize> = HashMap::new();
  for (idx, desc) in descriptors.iter().enumerate() {
    if let Some(raw) = desc.node {
      raw_to_desc.insert(raw, idx);
    }
    if let Some(raw) = desc.source.ptr() {
      raw_to_desc.insert(raw, idx);
    }
  }

  let mut cache: Vec<Option<usize>> = vec![None; descriptors.len()];
  for idx in 0..descriptors.len() {
    let depth = descriptor_depth(idx, descriptors, &raw_to_desc, &mut cache);
    descriptors[idx].depth = depth;
  }
}

fn descriptor_depth<'a>(
  idx: usize,
  descriptors: &[DefDescriptor<'a>],
  raw_to_desc: &HashMap<RawNode, usize>,
  cache: &mut [Option<usize>],
) -> usize {
  if let Some(depth) = cache[idx] {
    return depth;
  }

  // Treat cycles gracefully by marking the descriptor as visited before recursing.
  cache[idx] = Some(0);
  let depth = descriptors[idx]
    .parent
    .and_then(|raw| raw_to_desc.get(&raw).copied())
    .map(|parent_idx| descriptor_depth(parent_idx, descriptors, raw_to_desc, cache) + 1)
    .unwrap_or(0);
  cache[idx] = Some(depth);
  depth
}

#[derive(Debug, Clone, Copy)]
struct PlannedBody {
  id: BodyId,
  kind: BodyKind,
}

#[derive(Debug)]
struct PlannedDef<'a> {
  desc: DefDescriptor<'a>,
  def_id: DefId,
  def_path: DefPath,
  parent: Option<DefId>,
  body: Option<PlannedBody>,
}

impl DefLookup {
  fn record_source(&mut self, source: &DefSource<'_>, def: DefId) {
    if let Some(ptr) = source.ptr() {
      self.node_to_def.insert(ptr, def);
    }
  }

  fn def_for_node<T: Drive + DriveMut>(&self, node: &Node<T>) -> Option<DefId> {
    self.node_to_def.get(&RawNode::from(node)).copied()
  }

  fn def_for_raw(&self, raw: RawNode) -> Option<DefId> {
    self.node_to_def.get(&raw).copied()
  }

  fn body_for(&self, def: DefId) -> Option<BodyId> {
    self.def_bodies.get(&def).copied()
  }
}

fn allocate_def_id(def_path: DefPath, allocated: &mut BTreeMap<u32, DefPath>) -> DefId {
  let mut salt = 0u64;
  loop {
    let candidate = if salt == 0 {
      def_path.stable_hash_u32()
    } else {
      def_path.stable_hash_with_salt(salt)
    };
    match allocated.entry(candidate) {
      Entry::Vacant(slot) => {
        slot.insert(def_path);
        return DefId(candidate);
      }
      Entry::Occupied(existing) if *existing.get() == def_path => {
        return DefId(candidate);
      }
      Entry::Occupied(_) => {
        salt += 1;
      }
    }
  }
}

fn allocate_body_id(body_path: BodyPath, allocated: &mut BTreeMap<u32, BodyPath>) -> BodyId {
  let mut salt = 0u64;
  loop {
    let candidate = if salt == 0 {
      body_path.stable_hash_u32()
    } else {
      body_path.stable_hash_with_salt(salt)
    };
    match allocated.entry(candidate) {
      Entry::Vacant(slot) => {
        slot.insert(body_path);
        return BodyId(candidate);
      }
      Entry::Occupied(existing) if *existing.get() == body_path => {
        return BodyId(candidate);
      }
      Entry::Occupied(_) => {
        salt += 1;
      }
    }
  }
}

impl<'a> DefSource<'a> {
  fn body_kind(&self) -> Option<BodyKind> {
    match self {
      DefSource::ClassField(member) => {
        if matches!(member.stx.val, ClassOrObjVal::Prop(Some(_))) {
          Some(BodyKind::Initializer)
        } else {
          None
        }
      }
      DefSource::ClassStaticBlock(_) => Some(BodyKind::Class),
      DefSource::Function(decl) => decl
        .stx
        .function
        .stx
        .body
        .as_ref()
        .map(|_| BodyKind::Function),
      DefSource::ArrowFunction(_) | DefSource::FuncExpr(_) => Some(BodyKind::Function),
      DefSource::Method(method) => method
        .stx
        .func
        .stx
        .body
        .as_ref()
        .map(|_| BodyKind::Function),
      DefSource::Getter(getter) => getter
        .stx
        .func
        .stx
        .body
        .as_ref()
        .map(|_| BodyKind::Function),
      DefSource::Setter(setter) => setter
        .stx
        .func
        .stx
        .body
        .as_ref()
        .map(|_| BodyKind::Function),
      DefSource::Enum(_) => None,
      DefSource::Var(decl, _) => decl.initializer.as_ref().map(|_| BodyKind::Initializer),
      DefSource::ClassDecl(_) | DefSource::ClassExpr(_) => Some(BodyKind::Class),
      DefSource::ExportDefaultExpr(_) | DefSource::ExportAssignment(_) => Some(BodyKind::TopLevel),
      DefSource::None => None,
    }
  }

  fn ptr(&self) -> Option<RawNode> {
    match self {
      DefSource::ClassDecl(node) => Some(RawNode::from(*node)),
      DefSource::ClassExpr(node) => Some(RawNode::from(*node)),
      DefSource::ClassField(node) => Some(RawNode::from(*node)),
      DefSource::ClassStaticBlock(block) => Some(RawNode::from(*block)),
      DefSource::Function(node) => Some(RawNode::from(*node)),
      DefSource::ArrowFunction(node) => Some(RawNode::from(*node)),
      DefSource::FuncExpr(node) => Some(RawNode::from(*node)),
      DefSource::Enum(node) => Some(RawNode::from(*node)),
      DefSource::Var(_, _) => None,
      DefSource::Method(node) => Some(RawNode::from(*node)),
      DefSource::Getter(node) => Some(RawNode::from(*node)),
      DefSource::Setter(node) => Some(RawNode::from(*node)),
      DefSource::ExportDefaultExpr(node) => Some(RawNode::from(*node)),
      DefSource::ExportAssignment(node) => Some(RawNode::from(*node)),
      DefSource::None => None,
    }
  }
}

/// Lower a parsed file into HIR structures, returning lowering diagnostics.
pub fn lower_file_with_diagnostics(
  file: FileId,
  file_kind: FileKind,
  ast: &Node<TopLevel>,
) -> (LowerResult, Vec<Diagnostic>) {
  lower_file_with_diagnostics_with_cancellation(file, file_kind, ast, None)
}

/// Lower a parsed file into HIR structures, returning lowering diagnostics.
///
/// When a cancellation flag is provided, lowering aborts by panicking with
/// [`diagnostics::Cancelled`] once cancellation is observed. This mirrors how
/// the type checker propagates cancellation through salsa queries.
pub fn lower_file_with_diagnostics_with_cancellation(
  file: FileId,
  file_kind: FileKind,
  ast: &Node<TopLevel>,
  cancelled: Option<Arc<AtomicBool>>,
) -> (LowerResult, Vec<Diagnostic>) {
  let mut ctx = LoweringContext::new(file, cancelled);
  let mut names = NameInterner::default();
  let mut descriptors = Vec::new();
  let mut module_items = Vec::new();
  collect_top_level(
    ast,
    file_kind,
    &mut descriptors,
    &mut module_items,
    &mut names,
    &mut ctx,
  );

  compute_descriptor_depths(&mut descriptors);
  descriptors.sort_by(|a, b| {
    (a.depth, a.kind, a.name_text.as_str(), a.span.start).cmp(&(
      b.depth,
      b.kind,
      b.name_text.as_str(),
      b.span.start,
    ))
  });

  let mut span_map = SpanMap::new();
  let mut defs = Vec::with_capacity(descriptors.len());
  let mut types = BTreeMap::new();
  let mut pending_namespaces: Vec<DefId> = Vec::new();
  let mut disambiguators: BTreeMap<(Option<DefId>, DefKind, NameId), u32> = BTreeMap::new();
  let mut def_lookup = DefLookup::default();
  let mut allocated_def_ids: BTreeMap<u32, DefPath> = BTreeMap::new();
  let mut allocated_body_ids: BTreeMap<u32, BodyPath> = BTreeMap::new();

  let mut planned = Vec::new();
  let mut body_disambiguators: BTreeMap<DefId, u32> = BTreeMap::new();
  let mut parent_nodes: HashMap<RawNode, DefId> = HashMap::new();
  for desc in descriptors {
    ctx.check_cancelled();
    let parent = desc.parent.and_then(|raw| {
      def_lookup
        .def_for_raw(raw)
        .or_else(|| parent_nodes.get(&raw).copied())
    });
    let dis = disambiguators
      .entry((parent, desc.kind, desc.name))
      .or_insert(0);
    let def_path = DefPath::new(file, parent, desc.kind, desc.name, *dis);
    *dis += 1;
    let def_id = allocate_def_id(def_path, &mut allocated_def_ids);
    let body = desc.source.body_kind().map(|kind| {
      let disambiguator = body_disambiguators.entry(def_id).or_insert(0);
      let path = BodyPath::new(def_id, kind, *disambiguator);
      let id = allocate_body_id(path, &mut allocated_body_ids);
      *disambiguator += 1;
      PlannedBody { id, kind }
    });
    def_lookup.record_source(&desc.source, def_id);
    if let Some(body) = &body {
      def_lookup.def_bodies.insert(def_id, body.id);
    }
    if let Some(node) = desc.node {
      parent_nodes.insert(node, def_id);
    }
    planned.push(PlannedDef {
      desc,
      def_id,
      def_path,
      parent,
      body,
    });
  }

  let mut body_ids: Vec<BodyId> = Vec::new();
  let mut bodies: Vec<Arc<Body>> = Vec::new();
  let mut body_index: BTreeMap<BodyId, usize> = BTreeMap::new();
  let mut items = Vec::new();
  let mut decorator_store = DecoratorStore::default();

  for PlannedDef {
    desc,
    def_id,
    def_path,
    parent,
    body,
  } in planned
  {
    ctx.check_cancelled();
    if desc.is_item {
      items.push(def_id);
    }

    span_map.add_def(desc.span, desc.kind, def_id);

    let body_id = body.map(|b| b.id);
    let mut def_data = DefData {
      id: def_id,
      name: desc.name,
      path: def_path,
      span: desc.span,
      parent,
      decorators: Vec::new(),
      is_static: desc.is_static,
      is_ambient: desc.is_ambient,
      in_global: desc.in_global,
      is_exported: desc.is_exported,
      is_default_export: desc.is_default_export,
      body: body_id,
      type_info: None,
    };

    if let Some(type_source) = desc.type_source {
      match type_source {
        TypeSource::Namespace => {
          pending_namespaces.push(def_id);
          types.entry(def_id).or_default();
        }
        TypeSource::Module => {
          pending_namespaces.push(def_id);
          types.entry(def_id).or_default();
        }
        other => {
          let arenas = types.entry(def_id).or_default();
          let mut type_lowerer =
            TypeLowerer::new(def_id, arenas, &mut names, &mut span_map, &mut ctx);
          def_data.type_info = Some(match other {
            TypeSource::TypeAlias(alias) => type_lowerer.lower_type_alias(alias),
            TypeSource::Interface(intf) => type_lowerer.lower_interface(intf),
            TypeSource::Class(class) => type_lowerer.lower_class_decl(class),
            TypeSource::ClassExpr(class) => type_lowerer.lower_class_expr(class),
            TypeSource::AmbientClass(class) => type_lowerer.lower_ambient_class(class),
            TypeSource::Enum(en) => type_lowerer.lower_enum(en),
            TypeSource::Namespace | TypeSource::Module => unreachable!("handled above"),
          });
        }
      }
    }

    if let Some(body) = body {
      // Some definitions (notably variable declarators) are synthesized from
      // nested syntax and can be referenced by multiple `DefData` entries. Make
      // sure each `BodyId` is lowered and stored exactly once.
      if !body_index.contains_key(&body.id) {
        let lowered_body = lower_body_from_source(
          def_id,
          body.id,
          &desc.source,
          &def_lookup,
          &mut decorator_store,
          &mut names,
          &mut types,
          &mut span_map,
          &mut ctx,
        )
        .unwrap_or_else(|| {
          let placeholder = empty_body(def_id, body.kind, desc.span);
          span_map.add_body(placeholder.span, body.id);
          placeholder
        });
        let body_arc = Arc::new(lowered_body);
        let idx = bodies.len();
        body_ids.push(body.id);
        body_index.insert(body.id, idx);
        bodies.push(body_arc);
      }
    }

    def_data.decorators = decorator_store.by_def.remove(&def_id).unwrap_or_default();
    defs.push(def_data);
  }

  let root_body_id = allocate_body_id(
    BodyPath::new(DefId(file.0), BodyKind::TopLevel, 0),
    &mut allocated_body_ids,
  );
  body_index.insert(root_body_id, bodies.len());
  body_ids.push(root_body_id);
  bodies.push(Arc::new(lower_root_body(
    ast,
    root_body_id,
    &def_lookup,
    &mut names,
    &mut types,
    &mut span_map,
    &mut ctx,
  )));

  let id_to_index: BTreeMap<DefId, usize> = defs
    .iter()
    .enumerate()
    .map(|(idx, def)| (def.id, idx))
    .collect();

  for def_id in pending_namespaces {
    ctx.check_cancelled();
    if let Some(idx) = id_to_index.get(&def_id) {
      let members = collect_namespace_members(def_id, &defs);
      if let Some(def) = defs.get_mut(*idx) {
        def.type_info = Some(DefTypeInfo::Namespace { members });
      }
    }
  }

  let def_paths: BTreeMap<DefPath, DefId> = defs.iter().map(|def| (def.path, def.id)).collect();
  let def_index = id_to_index.clone();

  let (imports, exports) = lower_module_items(
    module_items,
    &mut names,
    &def_lookup,
    &defs,
    &id_to_index,
    &mut bodies,
    &mut body_index,
    &mut body_ids,
    &mut allocated_body_ids,
    &mut types,
    &mut span_map,
    &mut ctx,
  );

  span_map.finalize();

  (
    LowerResult {
      hir: Arc::new(HirFile::new(
        file,
        file_kind,
        root_body_id,
        items,
        body_ids,
        def_paths,
        imports,
        exports,
        span_map,
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

fn collect_namespace_members(def_id: DefId, defs: &[DefData]) -> Vec<DefId> {
  let mut members: Vec<DefId> = Vec::new();
  for def in defs.iter().filter(|def| def.parent == Some(def_id)) {
    if def.path.kind == DefKind::VarDeclarator {
      members.extend(
        defs
          .iter()
          .filter(|child| child.parent == Some(def.id) && child.path.kind == DefKind::Var)
          .map(|child| child.id),
      );
    } else {
      members.push(def.id);
    }
  }
  members.sort();
  members
}

fn empty_body(owner: DefId, kind: BodyKind, span: TextRange) -> Body {
  Body {
    owner,
    span,
    kind,
    exprs: Vec::new(),
    stmts: Vec::new(),
    pats: Vec::new(),
    root_stmts: Vec::new(),
    function: None,
    class: None,
    expr_types: None,
  }
}

fn lower_root_body(
  ast: &Node<TopLevel>,
  body_id: BodyId,
  def_lookup: &DefLookup,
  names: &mut NameInterner,
  types: &mut crate::hir::TypeArenasByDef,
  span_map: &mut SpanMap,
  ctx: &mut LoweringContext,
) -> Body {
  let span = ctx.to_range(ast.loc);
  let mut builder = BodyBuilder::new(
    DefId(u32::MAX),
    span,
    body_id,
    BodyKind::TopLevel,
    def_lookup,
    names,
    types,
    span_map,
  );
  for stmt in ast.stx.body.iter() {
    // Import/export declarations are tracked separately as module items and
    // emitted via `HirFile::{imports,exports}`; do not lower them into the
    // executable root body.
    match &*stmt.stx {
      AstStmt::Import(_)
      | AstStmt::ExportList(_)
      | AstStmt::ExportDefaultExpr(_)
      | AstStmt::ImportTypeDecl(_)
      | AstStmt::ExportTypeDecl(_)
      | AstStmt::ExportAsNamespaceDecl(_)
      | AstStmt::ImportEqualsDecl(_)
      | AstStmt::ExportAssignmentDecl(_) => continue,
      _ => {}
    }
    let stmt_id = lower_stmt(stmt, &mut builder, ctx);
    builder.root_stmt(stmt_id);
  }
  builder.finish_with_id(body_id)
}

fn lower_body_from_source(
  owner: DefId,
  body_id: BodyId,
  source: &DefSource,
  def_lookup: &DefLookup,
  decorator_store: &mut DecoratorStore,
  names: &mut NameInterner,
  types: &mut crate::hir::TypeArenasByDef,
  span_map: &mut SpanMap,
  ctx: &mut LoweringContext,
) -> Option<Body> {
  match source {
    DefSource::Function(decl) => lower_function_body(
      owner,
      body_id,
      &decl.stx.function,
      false,
      def_lookup,
      decorator_store,
      names,
      types,
      span_map,
      ctx,
    ),
    DefSource::ArrowFunction(func) => lower_function_body(
      owner,
      body_id,
      &func.stx.func,
      true,
      def_lookup,
      decorator_store,
      names,
      types,
      span_map,
      ctx,
    ),
    DefSource::FuncExpr(func) => lower_function_body(
      owner,
      body_id,
      &func.stx.func,
      false,
      def_lookup,
      decorator_store,
      names,
      types,
      span_map,
      ctx,
    ),
    DefSource::ClassDecl(class) => Some(lower_class_body(
      owner,
      body_id,
      ctx.to_range(class.loc),
      &class.stx.decorators,
      class.stx.extends.as_ref(),
      &class.stx.members,
      def_lookup,
      decorator_store,
      names,
      types,
      span_map,
      ctx,
    )),
    DefSource::ClassExpr(class) => Some(lower_class_body(
      owner,
      body_id,
      ctx.to_range(class.loc),
      &class.stx.decorators,
      class.stx.extends.as_ref(),
      &class.stx.members,
      def_lookup,
      decorator_store,
      names,
      types,
      span_map,
      ctx,
    )),
    DefSource::ClassField(member) => match &member.stx.val {
      ClassOrObjVal::Prop(Some(init)) => lower_field_initializer_body(
        owner, body_id, init, def_lookup, names, types, span_map, ctx,
      ),
      _ => None,
    },
    DefSource::Method(method) => lower_function_body(
      owner,
      body_id,
      &method.stx.func,
      false,
      def_lookup,
      decorator_store,
      names,
      types,
      span_map,
      ctx,
    ),
    DefSource::ClassStaticBlock(block) => {
      let span = ctx.to_range(block.loc);
      let mut builder = BodyBuilder::new(
        owner,
        span,
        body_id,
        BodyKind::Class,
        def_lookup,
        names,
        types,
        span_map,
      );
      for stmt in block.stx.body.iter() {
        let id = lower_stmt(stmt, &mut builder, ctx);
        builder.root_stmt(id);
      }
      Some(builder.finish())
    }
    DefSource::Getter(getter) => lower_function_body(
      owner,
      body_id,
      &getter.stx.func,
      false,
      def_lookup,
      decorator_store,
      names,
      types,
      span_map,
      ctx,
    ),
    DefSource::Setter(setter) => lower_function_body(
      owner,
      body_id,
      &setter.stx.func,
      false,
      def_lookup,
      decorator_store,
      names,
      types,
      span_map,
      ctx,
    ),
    DefSource::Var(decl, kind) => lower_var_body(
      owner, body_id, decl, *kind, def_lookup, names, types, span_map, ctx,
    ),
    DefSource::ExportDefaultExpr(expr) => {
      let span = ctx.to_range(expr.loc);
      let mut builder = BodyBuilder::new(
        owner,
        span,
        body_id,
        BodyKind::TopLevel,
        def_lookup,
        names,
        types,
        span_map,
      );
      let expr_id = lower_expr(&expr.stx.expression, &mut builder, ctx);
      let stmt_id = builder.alloc_stmt(ctx.to_range(expr.loc), StmtKind::Expr(expr_id));
      builder.root_stmt(stmt_id);
      Some(builder.finish())
    }
    DefSource::ExportAssignment(assign) => {
      let span = ctx.to_range(assign.loc);
      let mut builder = BodyBuilder::new(
        owner,
        span,
        body_id,
        BodyKind::TopLevel,
        def_lookup,
        names,
        types,
        span_map,
      );
      let expr_id = lower_expr(&assign.stx.expression, &mut builder, ctx);
      let stmt_id = builder.alloc_stmt(ctx.to_range(assign.loc), StmtKind::Expr(expr_id));
      builder.root_stmt(stmt_id);
      Some(builder.finish())
    }
    DefSource::Enum(_) => None,
    DefSource::None => None,
  }
}

fn lower_var_body(
  owner: DefId,
  body_id: BodyId,
  decl: &AstVarDeclarator,
  kind: VarDeclKind,
  def_lookup: &DefLookup,
  names: &mut NameInterner,
  types: &mut crate::hir::TypeArenasByDef,
  span_map: &mut SpanMap,
  ctx: &mut LoweringContext,
) -> Option<Body> {
  let span = ctx.to_range(decl.pattern.loc);
  let mut builder = BodyBuilder::new(
    owner,
    span,
    body_id,
    BodyKind::Initializer,
    def_lookup,
    names,
    types,
    span_map,
  );
  let pat_id = lower_pat(&decl.pattern.stx.pat, &mut builder, ctx);
  let init = decl
    .initializer
    .as_ref()
    .map(|expr| lower_expr(expr, &mut builder, ctx));
  let definite_assignment = decl.definite_assignment;
  let type_annotation = decl
    .type_annotation
    .as_ref()
    .map(|ann| builder.lower_type_expr(ann, ctx));
  let stmt_id = builder.alloc_stmt(
    ctx.to_range(decl.pattern.loc),
    StmtKind::Var(VarDecl {
      kind,
      declarators: vec![VarDeclarator {
        pat: pat_id,
        init,
        definite_assignment,
        type_annotation,
      }],
    }),
  );
  builder.root_stmt(stmt_id);
  Some(builder.finish())
}

fn lower_field_initializer_body(
  owner: DefId,
  body_id: BodyId,
  init: &Node<AstExpr>,
  def_lookup: &DefLookup,
  names: &mut NameInterner,
  types: &mut crate::hir::TypeArenasByDef,
  span_map: &mut SpanMap,
  ctx: &mut LoweringContext,
) -> Option<Body> {
  let span = ctx.to_range(init.loc);
  let mut builder = BodyBuilder::new(
    owner,
    span,
    body_id,
    BodyKind::Initializer,
    def_lookup,
    names,
    types,
    span_map,
  );
  let expr_id = lower_expr(init, &mut builder, ctx);
  let stmt_id = builder.alloc_stmt(ctx.to_range(init.loc), StmtKind::Expr(expr_id));
  builder.root_stmt(stmt_id);
  Some(builder.finish())
}

fn lower_function_body(
  owner: DefId,
  body_id: BodyId,
  func: &Node<Func>,
  is_arrow: bool,
  def_lookup: &DefLookup,
  decorator_store: &mut DecoratorStore,
  names: &mut NameInterner,
  types: &mut crate::hir::TypeArenasByDef,
  span_map: &mut SpanMap,
  ctx: &mut LoweringContext,
) -> Option<Body> {
  let span = ctx.to_range(func.loc);
  let mut builder = BodyBuilder::new(
    owner,
    span,
    body_id,
    BodyKind::Function,
    def_lookup,
    names,
    types,
    span_map,
  );

  let (type_params, param_type_annotations, return_type) = {
    let arenas = builder.types.entry(owner).or_default();
    let mut lowerer = TypeLowerer::new(
      owner,
      arenas,
      &mut *builder.names,
      &mut *builder.span_map,
      ctx,
    );
    let type_params = lowerer.lower_type_params(func.stx.type_parameters.as_deref());
    let param_type_annotations = func
      .stx
      .parameters
      .iter()
      .map(|param| {
        param
          .stx
          .type_annotation
          .as_ref()
          .map(|ann| lowerer.lower_type_expr(ann))
      })
      .collect::<Vec<_>>();
    let return_type = func
      .stx
      .return_type
      .as_ref()
      .map(|ret| lowerer.lower_type_expr(ret));
    (type_params, param_type_annotations, return_type)
  };

  let mut param_decorators = decorator_store
    .params_by_def
    .remove(&owner)
    .unwrap_or_default();
  let mut params = Vec::new();
  for (idx, param) in func.stx.parameters.iter().enumerate() {
    let pat = lower_pat(&param.stx.pattern.stx.pat, &mut builder, ctx);
    let default = param
      .stx
      .default_value
      .as_ref()
      .map(|default| lower_expr(default, &mut builder, ctx));
    let decorators = param_decorators
      .get_mut(idx)
      .map(std::mem::take)
      .unwrap_or_default();
    let type_annotation = param_type_annotations.get(idx).copied().unwrap_or(None);
    params.push(Param {
      pat,
      decorators,
      default,
      optional: param.stx.optional,
      rest: param.stx.rest,
      type_annotation,
    });
  }

  let body = match &func.stx.body {
    Some(FuncBody::Block(stmts)) => {
      let mut stmt_ids = Vec::new();
      for stmt in stmts.iter() {
        let id = lower_stmt(stmt, &mut builder, ctx);
        builder.root_stmt(id);
        stmt_ids.push(id);
      }
      FunctionBody::Block(stmt_ids)
    }
    Some(FuncBody::Expression(expr)) => {
      let expr_id = lower_expr(expr, &mut builder, ctx);
      let ret_stmt = builder.alloc_stmt(ctx.to_range(expr.loc), StmtKind::Return(Some(expr_id)));
      builder.root_stmt(ret_stmt);
      FunctionBody::Expr(expr_id)
    }
    None => FunctionBody::Block(Vec::new()),
  };

  builder.function = Some(FunctionData {
    type_params,
    params,
    return_type,
    async_: func.stx.async_,
    generator: func.stx.generator,
    is_arrow,
    body,
  });

  Some(builder.finish_with_id(body_id))
}

fn lower_class_body<'a>(
  owner: DefId,
  body_id: BodyId,
  class_span: TextRange,
  decorators: &'a [Node<AstDecorator>],
  extends: Option<&Node<AstExpr>>,
  members: &'a [Node<ClassMember>],
  def_lookup: &DefLookup,
  decorator_store: &mut DecoratorStore,
  names: &mut NameInterner,
  types: &mut crate::hir::TypeArenasByDef,
  span_map: &mut SpanMap,
  ctx: &mut LoweringContext,
) -> Body {
  #[derive(Clone, Copy)]
  enum DecoratorTarget {
    Def(DefId),
    Param { def: DefId, index: usize },
  }

  enum ClassEvalKind<'a> {
    Decorator {
      node: &'a Node<AstDecorator>,
      target: DecoratorTarget,
    },
    StaticBlock {
      node: &'a Node<ClassStaticBlock>,
    },
  }

  struct ClassEvalItem<'a> {
    range: TextRange,
    order: usize,
    kind: ClassEvalKind<'a>,
  }

  let mut start = class_span.start;
  let mut end = class_span.end;
  for decorator in decorators {
    let range = ctx.to_range(decorator.loc);
    start = start.min(range.start);
    end = end.max(range.end);
  }
  let span = TextRange::new(start, end);

  let mut builder = BodyBuilder::new(
    owner,
    span,
    body_id,
    BodyKind::Class,
    def_lookup,
    names,
    types,
    span_map,
  );

  let extends = extends.map(|expr| lower_expr(expr, &mut builder, ctx));
  let mut class_members: Vec<HirClassMember> = Vec::new();
  let mut static_blocks: HashMap<RawNode, usize> = HashMap::new();

  let mut items: Vec<ClassEvalItem<'a>> = Vec::new();

  fn collect_param_decorators<'b>(
    items: &mut Vec<ClassEvalItem<'b>>,
    func: &'b Node<Func>,
    owner_def: DefId,
    ctx: &mut LoweringContext,
  ) {
    for (param_idx, param) in func.stx.parameters.iter().enumerate() {
      for decorator in param.stx.decorators.iter() {
        let range = ctx.to_range(decorator.loc);
        let order = items.len();
        items.push(ClassEvalItem {
          range,
          order,
          kind: ClassEvalKind::Decorator {
            node: decorator,
            target: DecoratorTarget::Param {
              def: owner_def,
              index: param_idx,
            },
          },
        });
      }
    }
  }

  for decorator in decorators {
    let range = ctx.to_range(decorator.loc);
    items.push(ClassEvalItem {
      range,
      order: items.len(),
      kind: ClassEvalKind::Decorator {
        node: decorator,
        target: DecoratorTarget::Def(owner),
      },
    });
  }

  for member in members {
    let member_span = ctx.to_range(member.loc);
    match &member.stx.val {
      ClassOrObjVal::StaticBlock(block) => {
        static_blocks.insert(RawNode::from(block), class_members.len());
        class_members.push(HirClassMember {
          span: member_span,
          static_: true,
          kind: HirClassMemberKind::StaticBlock {
            stmt: StmtId(u32::MAX),
          },
        });
      }
      ClassOrObjVal::Prop(_) => {
        let def = builder
          .def_lookup
          .def_for_node(member)
          .unwrap_or(DefId(u32::MAX));
        let initializer = builder.def_lookup.body_for(def);
        let key = lower_class_member_key(&member.stx.key, &mut builder, ctx);
        class_members.push(HirClassMember {
          span: member_span,
          static_: member.stx.static_,
          kind: HirClassMemberKind::Field {
            def,
            initializer,
            key,
          },
        });
      }
      ClassOrObjVal::Method(method) => {
        let def = builder
          .def_lookup
          .def_for_node(method)
          .unwrap_or(DefId(u32::MAX));
        let body = builder.def_lookup.body_for(def);
        let key = lower_class_member_key(&member.stx.key, &mut builder, ctx);
        let is_constructor = matches!(&member.stx.key, ClassOrObjKey::Direct(direct) if direct.stx.key == "constructor")
          && !member.stx.static_;
        if is_constructor {
          class_members.push(HirClassMember {
            span: member_span,
            static_: false,
            kind: HirClassMemberKind::Constructor { def, body },
          });
        } else {
          class_members.push(HirClassMember {
            span: member_span,
            static_: member.stx.static_,
            kind: HirClassMemberKind::Method {
              def,
              body,
              key,
              kind: ClassMethodKind::Method,
            },
          });
        }
      }
      ClassOrObjVal::Getter(getter) => {
        let def = builder
          .def_lookup
          .def_for_node(getter)
          .unwrap_or(DefId(u32::MAX));
        let body = builder.def_lookup.body_for(def);
        let key = lower_class_member_key(&member.stx.key, &mut builder, ctx);
        class_members.push(HirClassMember {
          span: member_span,
          static_: member.stx.static_,
          kind: HirClassMemberKind::Method {
            def,
            body,
            key,
            kind: ClassMethodKind::Getter,
          },
        });
      }
      ClassOrObjVal::Setter(setter) => {
        let def = builder
          .def_lookup
          .def_for_node(setter)
          .unwrap_or(DefId(u32::MAX));
        let body = builder.def_lookup.body_for(def);
        let key = lower_class_member_key(&member.stx.key, &mut builder, ctx);
        class_members.push(HirClassMember {
          span: member_span,
          static_: member.stx.static_,
          kind: HirClassMemberKind::Method {
            def,
            body,
            key,
            kind: ClassMethodKind::Setter,
          },
        });
      }
      ClassOrObjVal::IndexSignature(_) => {}
    }

    let member_def = match &member.stx.val {
      ClassOrObjVal::Method(method) => def_lookup.def_for_node(method),
      ClassOrObjVal::Getter(getter) => def_lookup.def_for_node(getter),
      ClassOrObjVal::Setter(setter) => def_lookup.def_for_node(setter),
      ClassOrObjVal::Prop(_) => def_lookup.def_for_node(member),
      ClassOrObjVal::StaticBlock(block) => def_lookup.def_for_node(block),
      ClassOrObjVal::IndexSignature(_) => None,
    };

    if let Some(member_def) = member_def {
      for decorator in member.stx.decorators.iter() {
        let range = ctx.to_range(decorator.loc);
        items.push(ClassEvalItem {
          range,
          order: items.len(),
          kind: ClassEvalKind::Decorator {
            node: decorator,
            target: DecoratorTarget::Def(member_def),
          },
        });
      }

      match &member.stx.val {
        ClassOrObjVal::Method(method) => {
          collect_param_decorators(&mut items, &method.stx.func, member_def, ctx)
        }
        ClassOrObjVal::Setter(setter) => {
          collect_param_decorators(&mut items, &setter.stx.func, member_def, ctx)
        }
        ClassOrObjVal::Getter(getter) => {
          collect_param_decorators(&mut items, &getter.stx.func, member_def, ctx)
        }
        _ => {}
      }
    }

    if let ClassOrObjVal::StaticBlock(block) = &member.stx.val {
      let range = ctx.to_range(block.loc);
      items.push(ClassEvalItem {
        range,
        order: items.len(),
        kind: ClassEvalKind::StaticBlock { node: block },
      });
    }
  }

  items.sort_by(|a, b| {
    (a.range.start, a.range.end, a.order).cmp(&(b.range.start, b.range.end, b.order))
  });

  for item in items {
    match item.kind {
      ClassEvalKind::Decorator { node, target } => {
        let expr = lower_expr(&node.stx.expression, &mut builder, ctx);
        let stmt_id = builder.alloc_stmt(item.range, StmtKind::Expr(expr));
        builder.root_stmt(stmt_id);
        let decorator = Decorator {
          span: item.range,
          expr,
          body: body_id,
        };
        match target {
          DecoratorTarget::Def(def_id) => {
            decorator_store
              .by_def
              .entry(def_id)
              .or_default()
              .push(decorator);
          }
          DecoratorTarget::Param { def, index } => {
            let params = decorator_store.params_by_def.entry(def).or_default();
            if params.len() <= index {
              params.resize_with(index + 1, Vec::new);
            }
            params[index].push(decorator);
          }
        }
      }
      ClassEvalKind::StaticBlock { node } => {
        let mut block_stmts = Vec::new();
        for stmt in node.stx.body.iter() {
          let stmt_id = lower_stmt(stmt, &mut builder, ctx);
          block_stmts.push(stmt_id);
        }
        let stmt_id = builder.alloc_stmt(item.range, StmtKind::Block(block_stmts));
        builder.root_stmt(stmt_id);

        if let Some(idx) = static_blocks.get(&RawNode::from(node)).copied() {
          if let HirClassMemberKind::StaticBlock { stmt } = &mut class_members[idx].kind {
            *stmt = stmt_id;
          }
        }
      }
    }
  }

  builder.class = Some(ClassBody {
    extends,
    members: class_members,
  });

  builder.finish_with_id(body_id)
}

fn lower_class_member_key(
  key: &parse_js::ast::class_or_object::ClassOrObjKey,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> ClassMemberKey {
  use parse_js::token::TT;
  match key {
    parse_js::ast::class_or_object::ClassOrObjKey::Direct(direct) => match direct.stx.tt {
      TT::LiteralString | TT::LiteralTemplatePartString | TT::LiteralTemplatePartStringEnd => {
        ClassMemberKey::String(direct.stx.key.clone())
      }
      TT::LiteralNumber | TT::LiteralNumberBin | TT::LiteralNumberHex | TT::LiteralNumberOct => {
        ClassMemberKey::Number(direct.stx.key.clone())
      }
      TT::PrivateMember => ClassMemberKey::Private(builder.intern_name(&direct.stx.key)),
      _ => ClassMemberKey::Ident(builder.intern_name(&direct.stx.key)),
    },
    parse_js::ast::class_or_object::ClassOrObjKey::Computed(expr) => {
      let expr_id = lower_expr(expr, builder, ctx);
      ClassMemberKey::Computed(expr_id)
    }
  }
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
      let test = lower_expr(&if_stmt.stx.test, builder, ctx);
      let cons = lower_stmt(&if_stmt.stx.consequent, builder, ctx);
      let alt = if let Some(alt) = &if_stmt.stx.alternate {
        Some(lower_stmt(alt, builder, ctx))
      } else {
        None
      };
      StmtKind::If {
        test,
        consequent: cons,
        alternate: alt,
      }
    }
    AstStmt::While(wh) => {
      let test = lower_expr(&wh.stx.condition, builder, ctx);
      let body = lower_stmt(&wh.stx.body, builder, ctx);
      StmtKind::While { test, body }
    }
    AstStmt::DoWhile(dw) => {
      let test = lower_expr(&dw.stx.condition, builder, ctx);
      let body = lower_stmt(&dw.stx.body, builder, ctx);
      StmtKind::DoWhile { test, body }
    }
    AstStmt::ForTriple(for_stmt) => {
      let init = match &for_stmt.stx.init {
        ForTripleStmtInit::Expr(e) => Some(ForInit::Expr(lower_expr(e, builder, ctx))),
        ForTripleStmtInit::Decl(decl) => {
          Some(ForInit::Var(lower_var_decl_stmt(decl, builder, ctx)))
        }
        ForTripleStmtInit::None => None,
      };
      let cond = for_stmt
        .stx
        .cond
        .as_ref()
        .map(|c| lower_expr(c, builder, ctx));
      let post = for_stmt
        .stx
        .post
        .as_ref()
        .map(|p| lower_expr(p, builder, ctx));
      let body = lower_for_body(&for_stmt.stx.body, builder, ctx);
      StmtKind::For {
        init,
        test: cond,
        update: post,
        body,
      }
    }
    AstStmt::ForIn(for_in) => {
      let left = lower_for_head(&for_in.stx.lhs, builder, ctx);
      let right = lower_expr(&for_in.stx.rhs, builder, ctx);
      let body = lower_for_body(&for_in.stx.body, builder, ctx);
      StmtKind::ForIn {
        left,
        right,
        body,
        is_for_of: false,
        await_: false,
      }
    }
    AstStmt::ForOf(for_of) => {
      let left = lower_for_head(&for_of.stx.lhs, builder, ctx);
      let right = lower_expr(&for_of.stx.rhs, builder, ctx);
      let body = lower_for_body(&for_of.stx.body, builder, ctx);
      StmtKind::ForIn {
        left,
        right,
        body,
        is_for_of: true,
        await_: for_of.stx.await_,
      }
    }
    AstStmt::Switch(sw) => {
      let discriminant = lower_expr(&sw.stx.test, builder, ctx);
      let mut cases = Vec::new();
      for branch in sw.stx.branches.iter() {
        let test = branch
          .stx
          .case
          .as_ref()
          .map(|c| lower_expr(c, builder, ctx));
        let mut stmts = Vec::new();
        for stmt in branch.stx.body.iter() {
          stmts.push(lower_stmt(stmt, builder, ctx));
        }
        cases.push(SwitchCase {
          test,
          consequent: stmts,
        });
      }
      StmtKind::Switch {
        discriminant,
        cases,
      }
    }
    AstStmt::Try(tr) => {
      let block = lower_block_stmt(&tr.stx.wrapped, builder, ctx);
      let catch = if let Some(catch) = &tr.stx.catch {
        let param = catch
          .stx
          .parameter
          .as_ref()
          .map(|p| lower_pat(&p.stx.pat, builder, ctx));
        let mut catch_stmts = Vec::new();
        for stmt in catch.stx.body.iter() {
          catch_stmts.push(lower_stmt(stmt, builder, ctx));
        }
        let body = builder.alloc_stmt(ctx.to_range(catch.loc), StmtKind::Block(catch_stmts));
        Some(CatchClause { param, body })
      } else {
        None
      };
      let finally_block = if let Some(finally) = &tr.stx.finally {
        Some(lower_block_stmt(finally, builder, ctx))
      } else {
        None
      };
      StmtKind::Try {
        block,
        catch,
        finally_block,
      }
    }
    AstStmt::Throw(th) => {
      let value = lower_expr(&th.stx.value, builder, ctx);
      StmtKind::Throw(value)
    }
    AstStmt::Label(label) => {
      let body = lower_stmt(&label.stx.statement, builder, ctx);
      let label_id = builder.intern_name(&label.stx.name);
      StmtKind::Labeled {
        label: label_id,
        body,
      }
    }
    AstStmt::With(w) => {
      let obj = lower_expr(&w.stx.object, builder, ctx);
      let body = lower_stmt(&w.stx.body, builder, ctx);
      StmtKind::With { object: obj, body }
    }
    AstStmt::VarDecl(decl) => StmtKind::Var(lower_var_decl_stmt(decl, builder, ctx)),
    AstStmt::NamespaceDecl(ns) => {
      let stmts = lower_namespace_body(&ns.stx.body, builder, ctx);
      StmtKind::Block(stmts)
    }
    AstStmt::FunctionDecl(func) => {
      if let Some(def_id) = builder.def_lookup.def_for_node(func) {
        StmtKind::Decl(def_id)
      } else {
        StmtKind::Empty
      }
    }
    AstStmt::ClassDecl(class_decl) => {
      if let Some(def_id) = builder.def_lookup.def_for_node(class_decl) {
        StmtKind::Decl(def_id)
      } else {
        StmtKind::Empty
      }
    }
    AstStmt::Break(br) => {
      let label = br.stx.label.as_ref().map(|l| builder.intern_name(l));
      StmtKind::Break(label)
    }
    AstStmt::Continue(ct) => {
      let label = ct.stx.label.as_ref().map(|l| builder.intern_name(l));
      StmtKind::Continue(label)
    }
    AstStmt::Empty(_) => StmtKind::Empty,
    AstStmt::Debugger(_) => StmtKind::Debugger,
    _ => StmtKind::Empty,
  };

  builder.alloc_stmt(span, kind)
}

fn lower_var_decl_stmt(
  decl: &Node<parse_js::ast::stmt::decl::VarDecl>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> VarDecl {
  let kind = match decl.stx.mode {
    parse_js::ast::stmt::decl::VarDeclMode::Const => VarDeclKind::Const,
    parse_js::ast::stmt::decl::VarDeclMode::Let => VarDeclKind::Let,
    parse_js::ast::stmt::decl::VarDeclMode::Var => VarDeclKind::Var,
    parse_js::ast::stmt::decl::VarDeclMode::Using => VarDeclKind::Using,
    parse_js::ast::stmt::decl::VarDeclMode::AwaitUsing => VarDeclKind::AwaitUsing,
  };
  let mut declarators: Vec<VarDeclarator> = Vec::new();
  for declarator in decl.stx.declarators.iter() {
    let pat_id = lower_pat(&declarator.pattern.stx.pat, builder, ctx);
    let init = declarator
      .initializer
      .as_ref()
      .map(|expr| lower_expr(expr, builder, ctx));
    let type_annotation = declarator
      .type_annotation
      .as_ref()
      .map(|ann| builder.lower_type_expr(ann, ctx));
    declarators.push(VarDeclarator {
      pat: pat_id,
      init,
      definite_assignment: declarator.definite_assignment,
      type_annotation,
    });
  }
  VarDecl { kind, declarators }
}

fn lower_namespace_body(
  body: &NamespaceBody,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> Vec<StmtId> {
  match body {
    NamespaceBody::Block(stmts) => stmts
      .iter()
      .map(|stmt| lower_stmt(stmt, builder, ctx))
      .collect(),
    NamespaceBody::Namespace(inner) => lower_namespace_body(&inner.stx.body, builder, ctx),
  }
}

fn lower_for_head(
  lhs: &ForInOfLhs,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> ForHead {
  match lhs {
    ForInOfLhs::Assign(pat) => ForHead::Pat(lower_pat(pat, builder, ctx)),
    ForInOfLhs::Decl((mode, pat_decl)) => {
      let kind = match mode {
        parse_js::ast::stmt::decl::VarDeclMode::Const => VarDeclKind::Const,
        parse_js::ast::stmt::decl::VarDeclMode::Let => VarDeclKind::Let,
        parse_js::ast::stmt::decl::VarDeclMode::Var => VarDeclKind::Var,
        parse_js::ast::stmt::decl::VarDeclMode::Using => VarDeclKind::Using,
        parse_js::ast::stmt::decl::VarDeclMode::AwaitUsing => VarDeclKind::AwaitUsing,
      };
      let pat_id = lower_pat(&pat_decl.stx.pat, builder, ctx);
      ForHead::Var(VarDecl {
        kind,
        declarators: vec![VarDeclarator {
          pat: pat_id,
          init: None,
          definite_assignment: false,
          type_annotation: None,
        }],
      })
    }
  }
}

fn lower_for_body(
  body: &Node<ForBody>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> StmtId {
  let mut stmts = Vec::new();
  for stmt in body.stx.body.iter() {
    stmts.push(lower_stmt(stmt, builder, ctx));
  }
  builder.alloc_stmt(ctx.to_range(body.loc), StmtKind::Block(stmts))
}

fn lower_block_stmt(
  block: &Node<parse_js::ast::stmt::BlockStmt>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> StmtId {
  let mut stmts = Vec::new();
  for stmt in block.stx.body.iter() {
    stmts.push(lower_stmt(stmt, builder, ctx));
  }
  builder.alloc_stmt(ctx.to_range(block.loc), StmtKind::Block(stmts))
}

fn lower_expr(
  expr: &Node<AstExpr>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> ExprId {
  use parse_js::operator::OperatorName;

  let span = ctx.to_range(expr.loc);
  #[allow(unreachable_patterns)]
  let kind = match &*expr.stx {
    AstExpr::Id(id) => ExprKind::Ident(builder.intern_name(&id.stx.name)),
    AstExpr::This(_) => ExprKind::This,
    AstExpr::Super(_) => ExprKind::Super,
    AstExpr::LitNum(num) => ExprKind::Literal(Literal::Number(num.stx.value.to_string())),
    AstExpr::LitStr(str) => ExprKind::Literal(Literal::String(str.stx.value.clone())),
    AstExpr::LitBool(b) => ExprKind::Literal(Literal::Boolean(b.stx.value)),
    AstExpr::LitNull(_) => ExprKind::Literal(Literal::Null),
    AstExpr::LitBigInt(b) => ExprKind::Literal(Literal::BigInt(b.stx.value.clone())),
    AstExpr::LitRegex(r) => ExprKind::Literal(Literal::Regex(r.stx.value.clone())),
    AstExpr::Binary(bin) => {
      let op = bin.stx.operator;
      if let Some(assign_op) = map_assign_op(op) {
        let target = lower_assignment_pat(&bin.stx.left, builder, ctx);
        let value = lower_expr(&bin.stx.right, builder, ctx);
        ExprKind::Assignment {
          op: assign_op,
          target,
          value,
        }
      } else {
        let left = lower_expr(&bin.stx.left, builder, ctx);
        let right = lower_expr(&bin.stx.right, builder, ctx);
        let mapped = map_binary_op(op).unwrap_or(BinaryOp::Add);
        ExprKind::Binary {
          op: mapped,
          left,
          right,
        }
      }
    }
    AstExpr::Call(call) => lower_call_expr(call, builder, ctx, false),
    AstExpr::Member(mem) => {
      let object = lower_expr(&mem.stx.left, builder, ctx);
      let property = ObjectKey::Ident(builder.intern_name(&mem.stx.right));
      ExprKind::Member(MemberExpr {
        object,
        property,
        optional: mem.stx.optional_chaining,
      })
    }
    AstExpr::ComputedMember(mem) => {
      let object = lower_expr(&mem.stx.object, builder, ctx);
      let property_expr = lower_expr(&mem.stx.member, builder, ctx);
      ExprKind::Member(MemberExpr {
        object,
        property: ObjectKey::Computed(property_expr),
        optional: mem.stx.optional_chaining,
      })
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
    AstExpr::Func(func) => {
      if let Some(def) = builder.def_lookup.def_for_node(func) {
        let body = builder.def_lookup.body_for(def).unwrap_or(BodyId(u32::MAX));
        let name = func
          .stx
          .name
          .as_ref()
          .map(|n| builder.intern_name(&n.stx.name));
        ExprKind::FunctionExpr {
          def,
          body,
          name,
          is_arrow: false,
        }
      } else {
        #[cfg(test)]
        eprintln!("missing def for func expr at {:?}", ctx.to_range(func.loc));
        ExprKind::Missing
      }
    }
    AstExpr::ArrowFunc(func) => {
      if let Some(def) = builder.def_lookup.def_for_node(func) {
        let body = builder.def_lookup.body_for(def).unwrap_or(BodyId(u32::MAX));
        ExprKind::FunctionExpr {
          def,
          body,
          name: Some(builder.intern_name("<arrow>")),
          is_arrow: true,
        }
      } else {
        #[cfg(test)]
        eprintln!("missing def for arrow func at {:?}", ctx.to_range(func.loc));
        ExprKind::Missing
      }
    }
    AstExpr::Class(class_expr) => {
      if let Some(def) = builder.def_lookup.def_for_node(class_expr) {
        let body = builder.def_lookup.body_for(def).unwrap_or(BodyId(u32::MAX));
        let name = class_expr
          .stx
          .name
          .as_ref()
          .map(|n| builder.intern_name(&n.stx.name));
        ExprKind::ClassExpr { def, body, name }
      } else {
        #[cfg(test)]
        eprintln!(
          "missing def for class expr at {:?}",
          ctx.to_range(class_expr.loc)
        );
        ExprKind::Missing
      }
    }
    AstExpr::Unary(unary) => match unary.stx.operator {
      OperatorName::Await => ExprKind::Await {
        expr: lower_expr(&unary.stx.argument, builder, ctx),
      },
      OperatorName::Yield => ExprKind::Yield {
        expr: Some(lower_expr(&unary.stx.argument, builder, ctx)),
        delegate: false,
      },
      OperatorName::YieldDelegated => ExprKind::Yield {
        expr: Some(lower_expr(&unary.stx.argument, builder, ctx)),
        delegate: true,
      },
      OperatorName::PrefixIncrement => ExprKind::Update {
        op: UpdateOp::Increment,
        expr: lower_expr(&unary.stx.argument, builder, ctx),
        prefix: true,
      },
      OperatorName::PrefixDecrement => ExprKind::Update {
        op: UpdateOp::Decrement,
        expr: lower_expr(&unary.stx.argument, builder, ctx),
        prefix: true,
      },
      OperatorName::New => {
        if let AstExpr::Call(call) = unary.stx.argument.stx.as_ref() {
          lower_call_expr(call, builder, ctx, true)
        } else {
          let callee = lower_expr(&unary.stx.argument, builder, ctx);
          ExprKind::Call(CallExpr {
            callee,
            args: Vec::new(),
            optional: false,
            is_new: true,
          })
        }
      }
      op => {
        let mapped = map_unary_op(op).unwrap_or(UnaryOp::Plus);
        let arg = lower_expr(&unary.stx.argument, builder, ctx);
        ExprKind::Unary {
          op: mapped,
          expr: arg,
        }
      }
    },
    AstExpr::UnaryPostfix(post) => {
      let op = match post.stx.operator {
        OperatorName::PostfixIncrement => UpdateOp::Increment,
        _ => UpdateOp::Decrement,
      };
      let expr = lower_expr(&post.stx.argument, builder, ctx);
      ExprKind::Update {
        op,
        expr,
        prefix: false,
      }
    }
    AstExpr::TaggedTemplate(tag) => {
      let function = lower_expr(&tag.stx.function, builder, ctx);
      let tmpl = lower_template_literal(&tag.stx.parts, builder, ctx);
      ExprKind::TaggedTemplate {
        tag: function,
        template: tmpl,
      }
    }
    AstExpr::LitArr(arr) => {
      let mut elements = Vec::new();
      for element in arr.stx.elements.iter() {
        match element {
          parse_js::ast::expr::lit::LitArrElem::Single(expr) => {
            elements.push(ArrayElement::Expr(lower_expr(expr, builder, ctx)));
          }
          parse_js::ast::expr::lit::LitArrElem::Rest(expr) => {
            elements.push(ArrayElement::Spread(lower_expr(expr, builder, ctx)));
          }
          parse_js::ast::expr::lit::LitArrElem::Empty => elements.push(ArrayElement::Empty),
        }
      }
      ExprKind::Array(ArrayLiteral { elements })
    }
    AstExpr::LitObj(obj) => ExprKind::Object(lower_object_literal(obj, builder, ctx)),
    AstExpr::LitTemplate(tmpl) => {
      ExprKind::Template(lower_template_literal(&tmpl.stx.parts, builder, ctx))
    }
    AstExpr::TypeAssertion(assert) => {
      let expr = lower_expr(&assert.stx.expression, builder, ctx);
      let type_annotation = if assert.stx.const_assertion {
        None
      } else {
        assert
          .stx
          .type_annotation
          .as_ref()
          .map(|annotation| builder.lower_type_expr(annotation, ctx))
      };
      ExprKind::TypeAssertion {
        expr,
        const_assertion: assert.stx.const_assertion,
        type_annotation,
      }
    }
    AstExpr::NonNullAssertion(nn) => ExprKind::NonNull {
      expr: lower_expr(&nn.stx.expression, builder, ctx),
    },
    AstExpr::SatisfiesExpr(sat) => ExprKind::Satisfies {
      expr: lower_expr(&sat.stx.expression, builder, ctx),
      type_annotation: builder.lower_type_expr(&sat.stx.type_annotation, ctx),
    },
    AstExpr::Import(import_expr) => {
      let arg = lower_expr(&import_expr.stx.module, builder, ctx);
      let attrs = import_expr
        .stx
        .attributes
        .as_ref()
        .map(|a| lower_expr(a, builder, ctx));
      ExprKind::ImportCall {
        argument: arg,
        attributes: attrs,
      }
    }
    AstExpr::ImportMeta(_) => ExprKind::ImportMeta,
    AstExpr::NewTarget(_) => ExprKind::NewTarget,
    AstExpr::JsxElem(elem) => ExprKind::Jsx(lower_jsx_elem(elem, builder, ctx)),
    AstExpr::ArrPat(arr) => {
      let kind = lower_arr_pat(arr, builder, ctx);
      let _ = builder.alloc_pat(ctx.to_range(arr.loc), kind);
      ExprKind::Missing
    }
    AstExpr::ObjPat(obj) => {
      let kind = lower_obj_pat(obj, builder, ctx);
      let _ = builder.alloc_pat(ctx.to_range(obj.loc), kind);
      ExprKind::Missing
    }
    AstExpr::IdPat(id_pat) => {
      let name = builder.intern_name(&id_pat.stx.name);
      let _ = builder.alloc_pat(span, PatKind::Ident(name));
      ExprKind::Missing
    }
    _ => ExprKind::Missing,
  };

  builder.alloc_expr(span, kind)
}

fn lower_call_expr(
  call: &Node<parse_js::ast::expr::CallExpr>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
  is_new: bool,
) -> ExprKind {
  let callee = lower_expr(&call.stx.callee, builder, ctx);
  let args = call
    .stx
    .arguments
    .iter()
    .map(|arg| CallArg {
      expr: lower_expr(&arg.stx.value, builder, ctx),
      spread: arg.stx.spread,
    })
    .collect();
  ExprKind::Call(CallExpr {
    callee,
    args,
    optional: call.stx.optional_chaining,
    is_new,
  })
}

fn map_binary_op(op: parse_js::operator::OperatorName) -> Option<BinaryOp> {
  use parse_js::operator::OperatorName::*;
  Some(match op {
    Addition => BinaryOp::Add,
    Subtraction => BinaryOp::Subtract,
    Multiplication => BinaryOp::Multiply,
    Division => BinaryOp::Divide,
    Remainder => BinaryOp::Remainder,
    Exponentiation => BinaryOp::Exponent,
    BitwiseLeftShift => BinaryOp::ShiftLeft,
    BitwiseRightShift => BinaryOp::ShiftRight,
    BitwiseUnsignedRightShift => BinaryOp::ShiftRightUnsigned,
    BitwiseOr => BinaryOp::BitOr,
    BitwiseAnd => BinaryOp::BitAnd,
    BitwiseXor => BinaryOp::BitXor,
    LogicalOr => BinaryOp::LogicalOr,
    LogicalAnd => BinaryOp::LogicalAnd,
    NullishCoalescing => BinaryOp::NullishCoalescing,
    Equality => BinaryOp::Equality,
    Inequality => BinaryOp::Inequality,
    StrictEquality => BinaryOp::StrictEquality,
    StrictInequality => BinaryOp::StrictInequality,
    LessThan => BinaryOp::LessThan,
    LessThanOrEqual => BinaryOp::LessEqual,
    GreaterThan => BinaryOp::GreaterThan,
    GreaterThanOrEqual => BinaryOp::GreaterEqual,
    In => BinaryOp::In,
    Instanceof => BinaryOp::Instanceof,
    Comma => BinaryOp::Comma,
    _ => return None,
  })
}

fn map_assign_op(op: parse_js::operator::OperatorName) -> Option<AssignOp> {
  use parse_js::operator::OperatorName::*;
  Some(match op {
    Assignment => AssignOp::Assign,
    AssignmentAddition => AssignOp::AddAssign,
    AssignmentSubtraction => AssignOp::SubAssign,
    AssignmentMultiplication => AssignOp::MulAssign,
    AssignmentDivision => AssignOp::DivAssign,
    AssignmentRemainder => AssignOp::RemAssign,
    AssignmentBitwiseLeftShift => AssignOp::ShiftLeftAssign,
    AssignmentBitwiseRightShift => AssignOp::ShiftRightAssign,
    AssignmentBitwiseUnsignedRightShift => AssignOp::ShiftRightUnsignedAssign,
    AssignmentBitwiseOr => AssignOp::BitOrAssign,
    AssignmentBitwiseAnd => AssignOp::BitAndAssign,
    AssignmentBitwiseXor => AssignOp::BitXorAssign,
    AssignmentLogicalAnd => AssignOp::LogicalAndAssign,
    AssignmentLogicalOr => AssignOp::LogicalOrAssign,
    AssignmentNullishCoalescing => AssignOp::NullishAssign,
    AssignmentExponentiation => AssignOp::ExponentAssign,
    _ => return None,
  })
}

fn map_unary_op(op: parse_js::operator::OperatorName) -> Option<UnaryOp> {
  use parse_js::operator::OperatorName::*;
  Some(match op {
    LogicalNot => UnaryOp::Not,
    BitwiseNot => UnaryOp::BitNot,
    UnaryPlus => UnaryOp::Plus,
    UnaryNegation => UnaryOp::Minus,
    Typeof => UnaryOp::Typeof,
    Void => UnaryOp::Void,
    Delete => UnaryOp::Delete,
    _ => return None,
  })
}

fn lower_assignment_pat(
  expr: &Node<AstExpr>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> PatId {
  match &*expr.stx {
    AstExpr::Id(id) => {
      let span = ctx.to_range(expr.loc);
      let name_id = builder.intern_name(&id.stx.name);
      builder.alloc_pat(span, PatKind::Ident(name_id))
    }
    AstExpr::IdPat(id) => {
      let span = ctx.to_range(expr.loc);
      let name_id = builder.intern_name(&id.stx.name);
      builder.alloc_pat(span, PatKind::Ident(name_id))
    }
    AstExpr::ArrPat(arr) => {
      let pat_kind = lower_arr_pat(arr, builder, ctx);
      builder.alloc_pat(ctx.to_range(arr.loc), pat_kind)
    }
    AstExpr::ObjPat(obj) => {
      let pat_kind = lower_obj_pat(obj, builder, ctx);
      builder.alloc_pat(ctx.to_range(obj.loc), pat_kind)
    }
    _ => {
      let expr_id = lower_expr(expr, builder, ctx);
      builder.alloc_pat(ctx.to_range(expr.loc), PatKind::AssignTarget(expr_id))
    }
  }
}

fn lower_arr_pat(
  arr: &Node<ArrPat>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> PatKind {
  let mut elements = Vec::new();
  for elem in arr.stx.elements.iter() {
    if let Some(elem) = elem {
      let pat = lower_pat(&elem.target, builder, ctx);
      let default_value = elem
        .default_value
        .as_ref()
        .map(|expr| lower_expr(expr, builder, ctx));
      elements.push(Some(ArrayPatElement { pat, default_value }));
    } else {
      elements.push(None);
    }
  }
  let rest = arr.stx.rest.as_ref().map(|r| lower_pat(r, builder, ctx));
  PatKind::Array(ArrayPat { elements, rest })
}

fn is_valid_identifier_name(name: &str) -> bool {
  let mut chars = name.chars();
  let Some(first) = chars.next() else {
    return false;
  };

  if !(first == '$' || first == '_' || first.is_ascii_alphabetic()) {
    return false;
  }

  chars.all(|c| c == '$' || c == '_' || c.is_ascii_alphanumeric())
}

fn lower_object_key(
  key: &parse_js::ast::class_or_object::ClassOrObjKey,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> ObjectKey {
  use parse_js::ast::class_or_object::ClassOrObjKey;
  use parse_js::token::TT;

  match key {
    ClassOrObjKey::Direct(direct) => match direct.stx.tt {
      TT::LiteralString => {
        if is_valid_identifier_name(&direct.stx.key) {
          ObjectKey::Ident(builder.intern_name(&direct.stx.key))
        } else {
          ObjectKey::String(direct.stx.key.clone())
        }
      }
      TT::LiteralNumber | TT::LiteralBigInt => ObjectKey::Number(direct.stx.key.clone()),
      _ => ObjectKey::Ident(builder.intern_name(&direct.stx.key)),
    },
    ClassOrObjKey::Computed(expr) => {
      let expr_id = lower_expr(expr, builder, ctx);
      ObjectKey::Computed(expr_id)
    }
  }
}

fn lower_obj_pat(
  obj: &Node<ObjPat>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> PatKind {
  let mut props = Vec::new();
  for prop in obj.stx.properties.iter() {
    let key = lower_object_key(&prop.stx.key, builder, ctx);
    let value = lower_pat(&prop.stx.target, builder, ctx);
    let default_value = prop
      .stx
      .default_value
      .as_ref()
      .map(|expr| lower_expr(expr, builder, ctx));
    props.push(ObjectPatProp {
      key,
      value,
      shorthand: prop.stx.shorthand,
      default_value,
    });
  }
  let rest = obj.stx.rest.as_ref().map(|r| lower_pat(r, builder, ctx));
  PatKind::Object(ObjectPat { props, rest })
}

fn lower_object_literal(
  obj: &Node<parse_js::ast::expr::lit::LitObjExpr>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> ObjectLiteral {
  use parse_js::ast::class_or_object::{ClassOrObjVal, ObjMemberType};
  let mut properties = Vec::new();
  for member in obj.stx.members.iter() {
    match &member.stx.typ {
      ObjMemberType::Valued { key, val } => {
        let key = lower_object_key(key, builder, ctx);
        match val {
          ClassOrObjVal::Prop(Some(expr)) => {
            let value = lower_expr(expr, builder, ctx);
            properties.push(ObjectProperty::KeyValue {
              key,
              value,
              method: false,
              shorthand: false,
            });
          }
          ClassOrObjVal::Getter(get) => {
            if let Some(def) = builder.def_lookup.def_for_node(get) {
              let body = builder.def_lookup.body_for(def).unwrap_or(BodyId(u32::MAX));
              properties.push(ObjectProperty::Getter { key, body });
            }
          }
          ClassOrObjVal::Setter(set) => {
            if let Some(def) = builder.def_lookup.def_for_node(set) {
              let body = builder.def_lookup.body_for(def).unwrap_or(BodyId(u32::MAX));
              properties.push(ObjectProperty::Setter { key, body });
            }
          }
          ClassOrObjVal::Method(method) => {
            if let Some(def) = builder.def_lookup.def_for_node(method) {
              let body = builder.def_lookup.body_for(def).unwrap_or(BodyId(u32::MAX));
              let expr_id = builder.alloc_expr(
                ctx.to_range(method.loc),
                ExprKind::FunctionExpr {
                  def,
                  body,
                  name: None,
                  is_arrow: false,
                },
              );
              properties.push(ObjectProperty::KeyValue {
                key,
                value: expr_id,
                method: true,
                shorthand: false,
              });
            }
          }
          ClassOrObjVal::Prop(None) | ClassOrObjVal::IndexSignature(_) => {}
          ClassOrObjVal::StaticBlock(block) => {
            for stmt in block.stx.body.iter() {
              lower_stmt(stmt, builder, ctx);
            }
          }
        }
      }
      ObjMemberType::Shorthand { id } => {
        let name = builder.intern_name(&id.stx.name);
        let ident_expr = builder.alloc_expr(ctx.to_range(id.loc), ExprKind::Ident(name));
        properties.push(ObjectProperty::KeyValue {
          key: ObjectKey::Ident(name),
          value: ident_expr,
          method: false,
          shorthand: true,
        });
      }
      ObjMemberType::Rest { val } => {
        let expr_id = lower_expr(val, builder, ctx);
        properties.push(ObjectProperty::Spread(expr_id));
      }
    }
  }
  ObjectLiteral { properties }
}

fn lower_template_literal(
  parts: &[parse_js::ast::expr::lit::LitTemplatePart],
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> TemplateLiteral {
  let mut head = String::new();
  let mut spans: Vec<TemplateLiteralSpan> = Vec::new();
  let mut saw_head = false;
  for part in parts.iter() {
    match part {
      parse_js::ast::expr::lit::LitTemplatePart::String(text) => {
        if !saw_head {
          head = text.clone();
          saw_head = true;
        } else if let Some(last) = spans.last_mut() {
          last.literal = text.clone();
        }
      }
      parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) => {
        let expr_id = lower_expr(expr, builder, ctx);
        spans.push(TemplateLiteralSpan {
          expr: expr_id,
          literal: String::new(),
        });
      }
    }
  }
  TemplateLiteral { head, spans }
}

fn lower_jsx_elem(
  elem: &Node<jsx::JsxElem>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> JsxElement {
  let name = match &elem.stx.name {
    Some(jsx::JsxElemName::Id(id)) => {
      Some(JsxElementName::Ident(builder.intern_name(&id.stx.name)))
    }
    Some(jsx::JsxElemName::Name(name)) => Some(JsxElementName::Name(lower_jsx_name(name))),
    Some(jsx::JsxElemName::Member(member)) => Some(JsxElementName::Member(lower_jsx_member_expr(
      member, builder,
    ))),
    None => None,
  };

  let attributes = elem
    .stx
    .attributes
    .iter()
    .map(|attr| lower_jsx_attr(attr, builder, ctx))
    .collect();
  let children = elem
    .stx
    .children
    .iter()
    .map(|child| lower_jsx_child(child, builder, ctx))
    .collect();

  JsxElement {
    name,
    attributes,
    children,
  }
}

fn lower_jsx_name(name: &Node<jsx::JsxName>) -> JsxName {
  JsxName {
    namespace: name.stx.namespace.clone(),
    name: name.stx.name.clone(),
  }
}

fn lower_jsx_member_expr(
  member: &Node<jsx::JsxMemberExpr>,
  builder: &mut BodyBuilder<'_>,
) -> JsxMemberExpr {
  let base = builder.intern_name(&member.stx.base.stx.name);
  let path = member
    .stx
    .path
    .iter()
    .map(|segment| builder.intern_name(segment))
    .collect();
  JsxMemberExpr { base, path }
}

fn lower_jsx_attr(
  attr: &jsx::JsxAttr,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> JsxAttr {
  match attr {
    jsx::JsxAttr::Named { name, value } => JsxAttr::Named {
      name: lower_jsx_name(name),
      value: value
        .as_ref()
        .map(|value| lower_jsx_attr_value(value, builder, ctx)),
    },
    jsx::JsxAttr::Spread { value } => JsxAttr::Spread {
      expr: lower_expr(&value.stx.value, builder, ctx),
    },
  }
}

fn lower_jsx_attr_value(
  value: &jsx::JsxAttrVal,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> JsxAttrValue {
  match value {
    jsx::JsxAttrVal::Text(text) => JsxAttrValue::Text(text.stx.value.clone()),
    jsx::JsxAttrVal::Expression(expr) => {
      JsxAttrValue::Expression(lower_jsx_expr_container(expr, builder, ctx))
    }
    jsx::JsxAttrVal::Element(elem) => {
      JsxAttrValue::Element(lower_jsx_elem_as_expr(elem, builder, ctx))
    }
  }
}

fn lower_jsx_child(
  child: &jsx::JsxElemChild,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> JsxChild {
  match child {
    jsx::JsxElemChild::Element(elem) => {
      JsxChild::Element(lower_jsx_elem_as_expr(elem, builder, ctx))
    }
    jsx::JsxElemChild::Expr(expr) => JsxChild::Expr(lower_jsx_expr_container(expr, builder, ctx)),
    jsx::JsxElemChild::Text(text) => JsxChild::Text(text.stx.value.clone()),
  }
}

fn lower_jsx_expr_container(
  container: &Node<jsx::JsxExprContainer>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> JsxExprContainer {
  let expr = if is_empty_jsx_expr_placeholder(&container.stx.value) {
    None
  } else {
    Some(lower_expr(&container.stx.value, builder, ctx))
  };

  JsxExprContainer {
    spread: container.stx.spread,
    expr,
  }
}

fn is_empty_jsx_expr_placeholder(expr: &Node<AstExpr>) -> bool {
  expr.loc.is_empty() && matches!(expr.stx.as_ref(), AstExpr::Id(id) if id.stx.name.is_empty())
}

fn lower_jsx_elem_as_expr(
  elem: &Node<jsx::JsxElem>,
  builder: &mut BodyBuilder<'_>,
  ctx: &mut LoweringContext,
) -> ExprId {
  let lowered = lower_jsx_elem(elem, builder, ctx);
  let kind = ExprKind::Jsx(lowered);
  builder.alloc_expr(ctx.to_range(elem.loc), kind)
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

struct BodyBuilder<'a> {
  owner: DefId,
  span: TextRange,
  kind: BodyKind,
  body_id: BodyId,
  exprs: Vec<Expr>,
  stmts: Vec<Stmt>,
  pats: Vec<Pat>,
  root_stmts: Vec<StmtId>,
  function: Option<FunctionData>,
  class: Option<ClassBody>,
  def_lookup: &'a DefLookup,
  names: &'a mut NameInterner,
  types: &'a mut crate::hir::TypeArenasByDef,
  span_map: &'a mut SpanMap,
}

impl<'a> BodyBuilder<'a> {
  fn new(
    owner: DefId,
    span: TextRange,
    body_id: BodyId,
    kind: BodyKind,
    def_lookup: &'a DefLookup,
    names: &'a mut NameInterner,
    types: &'a mut crate::hir::TypeArenasByDef,
    span_map: &'a mut SpanMap,
  ) -> Self {
    Self {
      owner,
      span,
      kind,
      body_id,
      exprs: Vec::new(),
      stmts: Vec::new(),
      pats: Vec::new(),
      root_stmts: Vec::new(),
      function: None,
      class: None,
      def_lookup,
      names,
      types,
      span_map,
    }
  }

  fn alloc_expr(&mut self, span: TextRange, kind: ExprKind) -> ExprId {
    let id = ExprId(self.exprs.len() as u32);
    self.exprs.push(Expr { span, kind });
    self.span_map.add_expr(span, self.body_id, id);
    id
  }

  fn alloc_pat(&mut self, span: TextRange, kind: PatKind) -> PatId {
    let id = PatId(self.pats.len() as u32);
    self.pats.push(Pat { span, kind });
    self.span_map.add_pat(span, self.body_id, id);
    id
  }

  fn alloc_stmt(&mut self, span: TextRange, kind: StmtKind) -> StmtId {
    let id = StmtId(self.stmts.len() as u32);
    self.stmts.push(Stmt { span, kind });
    self.span_map.add_stmt(span, self.body_id, id);
    id
  }

  fn root_stmt(&mut self, id: StmtId) {
    self.root_stmts.push(id);
  }

  fn finish_with_id(self, _body_id: BodyId) -> Body {
    self.finish()
  }

  fn finish(self) -> Body {
    let mut body_span: Option<TextRange> = None;
    let mut include = |span: TextRange| {
      body_span = Some(match body_span {
        Some(existing) => {
          TextRange::new(existing.start.min(span.start), existing.end.max(span.end))
        }
        None => span,
      });
    };
    for expr in &self.exprs {
      include(expr.span);
    }
    for stmt in &self.stmts {
      include(stmt.span);
    }
    for pat in &self.pats {
      include(pat.span);
    }
    let body_span = body_span
      .filter(|span| !span.is_empty())
      .unwrap_or(self.span);
    self.span_map.add_body(body_span, self.body_id);

    Body {
      owner: self.owner,
      span: self.span,
      kind: self.kind,
      exprs: self.exprs,
      stmts: self.stmts,
      pats: self.pats,
      root_stmts: self.root_stmts,
      function: self.function,
      class: self.class,
      expr_types: None,
    }
  }

  fn intern_name(&mut self, name: &str) -> NameId {
    self.names.intern(name)
  }

  fn lower_type_expr(
    &mut self,
    expr: &Node<parse_js::ast::type_expr::TypeExpr>,
    ctx: &mut LoweringContext,
  ) -> crate::ids::TypeExprId {
    // Type IDs are scoped to a single `DefId`. For type syntax that appears
    // inside executable bodies (e.g. function parameters and variable
    // declarators), attach lowered type nodes to the body's owner `DefId`.
    let owner = self.owner;
    let arenas = self.types.entry(owner).or_default();
    let mut lowerer = TypeLowerer::new(owner, arenas, &mut *self.names, &mut *self.span_map, ctx);
    lowerer.lower_type_expr(expr)
  }
}

fn collect_top_level<'a>(
  ast: &'a Node<TopLevel>,
  file_kind: FileKind,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  module_items: &mut Vec<ModuleItem<'a>>,
  names: &mut NameInterner,
  ctx: &mut LoweringContext,
) {
  let ambient = matches!(file_kind, FileKind::Dts);
  for stmt in ast.stx.body.iter() {
    collect_stmt(
      stmt,
      descriptors,
      module_items,
      names,
      true,
      true,
      ambient,
      false,
      ctx,
    );
  }
}

/// Render a module declaration name into a stable string suitable for
/// interning. String-literal module specifiers are wrapped in quotes so they do
/// not collide with namespace-style `module Foo {}` declarations.
fn module_name_text(name: &ModuleName) -> String {
  match name {
    ModuleName::Identifier(name) => name.clone(),
    ModuleName::String(spec) => format!("\"{}\"", spec),
  }
}

fn collect_stmt<'a>(
  stmt: &'a Node<AstStmt>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  module_items: &mut Vec<ModuleItem<'a>>,
  names: &mut NameInterner,
  module_item: bool,
  is_item: bool,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  let span = ctx.to_range(stmt.loc);
  let parent = ctx.current_parent();
  let record_module_item = module_item && is_item;
  match &*stmt.stx {
    AstStmt::FunctionDecl(func) => {
      let (name_id, name_text) = name_from_optional(&func.stx.name, names);
      let decl_ambient = ambient;
      let func_raw = RawNode::from(func);
      let mut desc = DefDescriptor::new(
        DefKind::Function,
        name_id,
        name_text,
        span,
        is_item,
        decl_ambient,
        in_global,
        DefSource::Function(func),
      );
      desc.parent = parent;
      desc.is_exported = func.stx.export;
      desc.is_default_export = func.stx.export_default;
      if desc.is_exported || desc.is_default_export {
        if record_module_item {
          module_items.push(ModuleItem {
            span,
            kind: ModuleItemKind::ExportedDecl(ExportedDecl {
              default: desc.is_default_export,
              type_only: false,
              span,
              kind: ExportedDeclKind::Func(func),
            }),
          });
        } else if !module_item && desc.is_default_export {
          ctx.warn_non_module_export(
            span,
            "export default is only allowed at the module top level",
          );
        }
      }
      descriptors.push(desc);
      ctx.with_parent(Some(func_raw), |ctx| {
        collect_func_params(
          &func.stx.function,
          descriptors,
          module_items,
          names,
          decl_ambient,
          in_global,
          ctx,
        );
        collect_func_body(
          &func.stx.function,
          descriptors,
          module_items,
          names,
          decl_ambient,
          in_global,
          ctx,
        );
      });
    }
    AstStmt::ClassDecl(class_decl) => {
      let (name_id, name_text) = name_from_optional(&class_decl.stx.name, names);
      let decl_ambient = ambient || class_decl.stx.declare;
      let class_raw = RawNode::from(class_decl);
      let mut desc = DefDescriptor::new(
        DefKind::Class,
        name_id,
        name_text,
        span,
        is_item,
        decl_ambient,
        in_global,
        DefSource::ClassDecl(class_decl),
      );
      desc.type_source = Some(TypeSource::Class(class_decl));
      desc.parent = parent;
      desc.is_exported = class_decl.stx.export;
      desc.is_default_export = class_decl.stx.export_default;
      if desc.is_exported || desc.is_default_export {
        if record_module_item {
          module_items.push(ModuleItem {
            span,
            kind: ModuleItemKind::ExportedDecl(ExportedDecl {
              default: desc.is_default_export,
              type_only: false,
              span,
              kind: ExportedDeclKind::Class(class_decl),
            }),
          });
        } else if !module_item && desc.is_default_export {
          ctx.warn_non_module_export(
            span,
            "export default is only allowed at the module top level",
          );
        }
      }
      descriptors.push(desc);
      ctx.with_parent(Some(class_raw), |ctx| {
        for decorator in class_decl.stx.decorators.iter() {
          collect_expr(
            &decorator.stx.expression,
            descriptors,
            module_items,
            names,
            decl_ambient,
            in_global,
            ctx,
          );
        }
        if let Some(extends) = class_decl.stx.extends.as_ref() {
          collect_expr(
            extends,
            descriptors,
            module_items,
            names,
            decl_ambient,
            in_global,
            ctx,
          );
        }
        collect_class_members(
          &class_decl.stx.members,
          class_raw,
          descriptors,
          module_items,
          names,
          decl_ambient,
          in_global,
          ctx,
        );
      });
    }
    AstStmt::VarDecl(var_decl) => {
      collect_var_decl(
        var_decl,
        descriptors,
        module_items,
        names,
        module_item,
        is_item,
        ambient,
        in_global,
        ctx,
      );
      if var_decl.stx.export {
        if record_module_item {
          module_items.push(ModuleItem {
            span,
            kind: ModuleItemKind::ExportedDecl(ExportedDecl {
              default: false,
              type_only: false,
              span,
              kind: ExportedDeclKind::Var(var_decl),
            }),
          });
        }
      }
    }
    AstStmt::NamespaceDecl(ns) => {
      let decl_ambient = ambient || ns.stx.declare;
      collect_namespace(
        ns,
        descriptors,
        module_items,
        names,
        module_item,
        is_item,
        decl_ambient,
        in_global,
        ctx,
      );
      if ns.stx.export {
        if record_module_item {
          module_items.push(ModuleItem {
            span,
            kind: ModuleItemKind::ExportedDecl(ExportedDecl {
              default: false,
              type_only: false,
              span,
              kind: ExportedDeclKind::Namespace(ns),
            }),
          });
        }
      }
    }
    AstStmt::ModuleDecl(module) => {
      let name_text = module_name_text(&module.stx.name);
      let name_id = names.intern(&name_text);
      let decl_ambient = ambient || module.stx.declare;
      let exported = module.stx.export || (!module_item && parent.is_some());
      let module_raw = RawNode::from(module);
      let mut desc = DefDescriptor::new(
        DefKind::Module,
        name_id,
        name_text,
        span,
        is_item,
        decl_ambient,
        in_global,
        DefSource::None,
      );
      desc.parent = parent;
      desc.node = Some(module_raw);
      desc.is_exported = exported;
      desc.type_source = Some(TypeSource::Module);
      descriptors.push(desc);
      if module.stx.export {
        if record_module_item {
          module_items.push(ModuleItem {
            span,
            kind: ModuleItemKind::ExportedDecl(ExportedDecl {
              default: false,
              type_only: false,
              span,
              kind: ExportedDeclKind::Module(module),
            }),
          });
        }
      }
      if let Some(body) = &module.stx.body {
        let body_start = descriptors.len();
        ctx.with_parent(Some(module_raw), |ctx| {
          let body_module_item = matches!(module.stx.name, ModuleName::String(_));
          for st in body.iter() {
            collect_stmt(
              st,
              descriptors,
              module_items,
              names,
              body_module_item,
              false,
              decl_ambient,
              in_global,
              ctx,
            );
          }
        });
        let has_export_assignment = body
          .iter()
          .any(|st| matches!(st.stx.as_ref(), AstStmt::ExportAssignmentDecl(_)));
        // Match TypeScript's `export =` semantics: when a module has an export
        // assignment, it behaves like a CommonJS module and does not implicitly
        // export all declarations as named exports.
        let members_exported_by_default = (decl_ambient
          || matches!(module.stx.name, ModuleName::String(_)))
          && !has_export_assignment;
        for desc in descriptors.iter_mut().skip(body_start) {
          // Ambient modules export their declarations without `export` modifiers.
          if desc.parent == Some(module_raw) && members_exported_by_default {
            desc.is_exported = true;
          }
        }
      }
    }
    AstStmt::GlobalDecl(global) => {
      for st in global.stx.body.iter() {
        collect_stmt(
          st,
          descriptors,
          module_items,
          names,
          false,
          true,
          true,
          true,
          ctx,
        );
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
        span,
        is_item,
        decl_ambient,
        in_global,
        DefSource::None,
      );
      desc.parent = parent;
      desc.type_source = Some(TypeSource::Interface(intf));
      desc.is_exported = intf.stx.export;
      descriptors.push(desc);
      if intf.stx.export && record_module_item {
        module_items.push(ModuleItem {
          span,
          kind: ModuleItemKind::ExportedDecl(ExportedDecl {
            default: false,
            type_only: true,
            span,
            kind: ExportedDeclKind::Interface(intf),
          }),
        });
      }
    }
    AstStmt::TypeAliasDecl(ta) => {
      let name_id = names.intern(&ta.stx.name);
      let text = names.resolve(name_id).unwrap().to_string();
      let decl_ambient = ambient || ta.stx.declare;
      let mut desc = DefDescriptor::new(
        DefKind::TypeAlias,
        name_id,
        text,
        span,
        is_item,
        decl_ambient,
        in_global,
        DefSource::None,
      );
      desc.parent = parent;
      desc.type_source = Some(TypeSource::TypeAlias(ta));
      desc.is_exported = ta.stx.export;
      descriptors.push(desc);
      if ta.stx.export && record_module_item {
        module_items.push(ModuleItem {
          span,
          kind: ModuleItemKind::ExportedDecl(ExportedDecl {
            default: false,
            type_only: true,
            span,
            kind: ExportedDeclKind::TypeAlias(ta),
          }),
        });
      }
    }
    AstStmt::EnumDecl(en) => {
      let name_id = names.intern(&en.stx.name);
      let text = names.resolve(name_id).unwrap().to_string();
      let decl_ambient = ambient || en.stx.declare;
      let mut desc = DefDescriptor::new(
        DefKind::Enum,
        name_id,
        text,
        span,
        is_item,
        decl_ambient,
        in_global,
        DefSource::Enum(en),
      );
      desc.type_source = Some(TypeSource::Enum(en));
      desc.parent = parent;
      desc.is_exported = en.stx.export;
      let parent_raw = RawNode::from(en);
      for member in en.stx.members.iter() {
        let member_name = names.intern(&member.stx.name);
        let member_text = names.resolve(member_name).unwrap().to_string();
        let mut member_desc = DefDescriptor::new(
          DefKind::EnumMember,
          member_name,
          member_text,
          ctx.to_range(member.loc),
          false,
          decl_ambient,
          in_global,
          DefSource::None,
        );
        member_desc.parent = Some(parent_raw);
        member_desc.is_exported = desc.is_exported;
        member_desc.is_default_export = desc.is_default_export;
        descriptors.push(member_desc);
        if let Some(init) = &member.stx.initializer {
          collect_expr(
            init,
            descriptors,
            module_items,
            names,
            decl_ambient,
            in_global,
            ctx,
          );
        }
      }
      descriptors.push(desc);
      if en.stx.export && record_module_item {
        module_items.push(ModuleItem {
          span,
          kind: ModuleItemKind::ExportedDecl(ExportedDecl {
            default: false,
            type_only: false,
            span,
            kind: ExportedDeclKind::Enum(en),
          }),
        });
      }
    }
    AstStmt::Import(stmt_import) => {
      if record_module_item {
        module_items.push(ModuleItem {
          span,
          kind: ModuleItemKind::Import(stmt_import),
        });
      }
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
    AstStmt::ExportList(export) => {
      if record_module_item {
        module_items.push(ModuleItem {
          span,
          kind: ModuleItemKind::ExportList(export),
        });
      } else if !module_item {
        ctx.warn_non_module_export(
          span,
          "export statements are only allowed at the module top level",
        );
      }
    }
    AstStmt::ExportDefaultExpr(expr) => {
      let name_id = names.intern("default");
      let mut desc = DefDescriptor::new(
        DefKind::ExportAlias,
        name_id,
        "default".into(),
        span,
        is_item,
        ambient,
        in_global,
        DefSource::ExportDefaultExpr(expr),
      );
      desc.is_default_export = true;
      desc.parent = parent;
      descriptors.push(desc);
      collect_expr(
        &expr.stx.expression,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      if record_module_item {
        module_items.push(ModuleItem {
          span,
          kind: ModuleItemKind::ExportDefaultExpr(expr),
        });
      } else if !module_item {
        ctx.warn_non_module_export(
          span,
          "export default is only allowed at the module top level",
        );
      }
    }
    AstStmt::AmbientVarDecl(av) => {
      let name_id = names.intern(&av.stx.name);
      let mut desc = DefDescriptor::new(
        DefKind::Var,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        span,
        is_item,
        true,
        in_global,
        DefSource::None,
      );
      desc.parent = parent;
      desc.is_exported = av.stx.export;
      descriptors.push(desc);
      if av.stx.export && record_module_item {
        module_items.push(ModuleItem {
          span,
          kind: ModuleItemKind::ExportedDecl(ExportedDecl {
            default: false,
            type_only: false,
            span,
            kind: ExportedDeclKind::AmbientVar(av),
          }),
        });
      }
    }
    AstStmt::AmbientFunctionDecl(af) => {
      let name_id = names.intern(&af.stx.name);
      let func_raw = RawNode::from(af);
      let mut desc = DefDescriptor::new(
        DefKind::Function,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        span,
        is_item,
        true,
        in_global,
        DefSource::None,
      );
      desc.parent = parent;
      // Mark the AST node so parameters can resolve their parent `DefId`.
      desc.node = Some(func_raw);
      desc.is_exported = af.stx.export;
      descriptors.push(desc);
      ctx.with_parent(Some(func_raw), |ctx| {
        collect_func_params_from_parts(
          &af.stx.parameters,
          descriptors,
          names,
          true,
          in_global,
          ctx,
        );
      });
      if af.stx.export && record_module_item {
        module_items.push(ModuleItem {
          span,
          kind: ModuleItemKind::ExportedDecl(ExportedDecl {
            default: false,
            type_only: false,
            span,
            kind: ExportedDeclKind::AmbientFunction(af),
          }),
        });
      }
    }
    AstStmt::AmbientClassDecl(ac) => {
      let name_id = names.intern(&ac.stx.name);
      let mut desc = DefDescriptor::new(
        DefKind::Class,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        span,
        is_item,
        true,
        in_global,
        DefSource::None,
      );
      desc.parent = parent;
      desc.is_exported = ac.stx.export;
      desc.type_source = Some(TypeSource::AmbientClass(ac));
      descriptors.push(desc);
      if ac.stx.export && record_module_item {
        module_items.push(ModuleItem {
          span,
          kind: ModuleItemKind::ExportedDecl(ExportedDecl {
            default: false,
            type_only: false,
            span,
            kind: ExportedDeclKind::AmbientClass(ac),
          }),
        });
      }
    }
    AstStmt::ImportTypeDecl(import_type) => {
      if record_module_item {
        module_items.push(ModuleItem {
          span,
          kind: ModuleItemKind::ImportType(import_type),
        });
      }
    }
    AstStmt::ExportTypeDecl(export_type) => {
      if record_module_item {
        module_items.push(ModuleItem {
          span,
          kind: ModuleItemKind::ExportType(export_type),
        });
      } else if !module_item {
        ctx.warn_non_module_export(span, "export type is only allowed at the module top level");
      }
    }
    AstStmt::ImportEqualsDecl(ie) => {
      if record_module_item {
        module_items.push(ModuleItem {
          span,
          kind: ModuleItemKind::ImportEquals(ie),
        });
      }
      let name_id = names.intern(&ie.stx.name);
      let mut desc = DefDescriptor::new(
        DefKind::ImportBinding,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        span,
        is_item,
        ambient,
        in_global,
        DefSource::None,
      );
      desc.parent = parent;
      desc.is_exported = ie.stx.export;
      descriptors.push(desc);
    }
    AstStmt::ExportAssignmentDecl(assign) => {
      let name_id = names.intern("export=");
      let mut desc = DefDescriptor::new(
        DefKind::ExportAlias,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        span,
        is_item,
        true,
        in_global,
        DefSource::ExportAssignment(assign),
      );
      desc.parent = parent;
      desc.is_exported = true;
      descriptors.push(desc);
      if record_module_item {
        module_items.push(ModuleItem {
          span,
          kind: ModuleItemKind::ExportAssignment(assign),
        });
      } else if !module_item {
        ctx.warn_non_module_export(
          span,
          "export assignment is only allowed at the module top level",
        );
      }
    }
    AstStmt::ExportAsNamespaceDecl(export_ns) => {
      if record_module_item {
        module_items.push(ModuleItem {
          span,
          kind: ModuleItemKind::ExportAsNamespace(export_ns),
        });
      } else if !module_item {
        ctx.warn_non_module_export(
          span,
          "export as namespace is only allowed at the module top level",
        );
      }
    }
    AstStmt::ForIn(for_in) => {
      collect_for_lhs(
        &for_in.stx.lhs,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_expr(
        &for_in.stx.rhs,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_for_body(
        &for_in.stx.body,
        descriptors,
        module_items,
        names,
        false,
        ambient,
        in_global,
        ctx,
      );
    }
    AstStmt::ForOf(for_of) => {
      collect_for_lhs(
        &for_of.stx.lhs,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_expr(
        &for_of.stx.rhs,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_for_body(
        &for_of.stx.body,
        descriptors,
        module_items,
        names,
        false,
        ambient,
        in_global,
        ctx,
      );
    }
    _ => {
      walk_stmt_children(
        stmt,
        descriptors,
        module_items,
        names,
        false,
        ambient,
        in_global,
        ctx,
      );
    }
  }
}

fn collect_class_members<'a>(
  members: &'a [Node<ClassMember>],
  parent: RawNode,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  module_items: &mut Vec<ModuleItem<'a>>,
  names: &mut NameInterner,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  for member in members.iter() {
    for decorator in member.stx.decorators.iter() {
      collect_expr(
        &decorator.stx.expression,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    let span = ctx.to_range(member.loc);
    let member_raw = RawNode::from(member);
    let is_static = member.stx.static_;
    if let ClassOrObjKey::Computed(expr) = &member.stx.key {
      collect_expr(
        expr,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    match &member.stx.val {
      ClassOrObjVal::Method(method) => {
        let (name_id, name_text) = obj_key_name(&member.stx.key, names);
        let is_constructor = matches!(&member.stx.key, ClassOrObjKey::Direct(direct) if direct.stx.key == "constructor")
          && !member.stx.static_;
        let kind = if is_constructor {
          DefKind::Constructor
        } else {
          DefKind::Method
        };
        let method_raw = RawNode::from(method);
        let mut desc = DefDescriptor::new(
          kind,
          name_id,
          name_text,
          span,
          false,
          ambient,
          in_global,
          DefSource::Method(method),
        );
        desc.parent = Some(parent);
        desc.is_static = is_static;
        descriptors.push(desc);
        ctx.with_parent(Some(method_raw), |ctx| {
          collect_func_params(
            &method.stx.func,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
          collect_func_body(
            &method.stx.func,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
        });
      }
      ClassOrObjVal::Getter(getter) => {
        let (name_id, name_text) = obj_key_name(&member.stx.key, names);
        let getter_raw = RawNode::from(getter);
        let mut desc = DefDescriptor::new(
          DefKind::Getter,
          name_id,
          name_text,
          span,
          false,
          ambient,
          in_global,
          DefSource::Getter(getter),
        );
        desc.parent = Some(parent);
        desc.is_static = is_static;
        descriptors.push(desc);
        ctx.with_parent(Some(getter_raw), |ctx| {
          collect_func_params(
            &getter.stx.func,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
          collect_func_body(
            &getter.stx.func,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
        });
      }
      ClassOrObjVal::Setter(setter) => {
        let (name_id, name_text) = obj_key_name(&member.stx.key, names);
        let setter_raw = RawNode::from(setter);
        let mut desc = DefDescriptor::new(
          DefKind::Setter,
          name_id,
          name_text,
          span,
          false,
          ambient,
          in_global,
          DefSource::Setter(setter),
        );
        desc.parent = Some(parent);
        desc.is_static = is_static;
        descriptors.push(desc);
        ctx.with_parent(Some(setter_raw), |ctx| {
          collect_func_params(
            &setter.stx.func,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
          collect_func_body(
            &setter.stx.func,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
        });
      }
      ClassOrObjVal::Prop(init) => {
        let (name_id, name_text) = obj_key_name(&member.stx.key, names);
        let mut desc = DefDescriptor::new(
          DefKind::Field,
          name_id,
          name_text,
          span,
          false,
          ambient,
          in_global,
          DefSource::ClassField(member),
        );
        desc.parent = Some(parent);
        desc.is_static = is_static;
        descriptors.push(desc);
        if let Some(expr) = init {
          ctx.with_parent(Some(member_raw), |ctx| {
            collect_expr(
              expr,
              descriptors,
              module_items,
              names,
              ambient,
              in_global,
              ctx,
            );
          });
        }
      }
      ClassOrObjVal::StaticBlock(block) => {
        let name_id = names.intern("<static_block>");
        let name_text = names.resolve(name_id).unwrap().to_string();
        let block_raw = RawNode::from(block);
        let mut desc = DefDescriptor::new(
          DefKind::StaticBlock,
          name_id,
          name_text,
          span,
          false,
          ambient,
          in_global,
          DefSource::ClassStaticBlock(block),
        );
        desc.parent = Some(parent);
        desc.is_static = true;
        descriptors.push(desc);
        ctx.with_parent(Some(block_raw), |ctx| {
          for stmt in block.stx.body.iter() {
            collect_stmt(
              stmt,
              descriptors,
              module_items,
              names,
              false,
              false,
              ambient,
              in_global,
              ctx,
            );
          }
        });
      }
      ClassOrObjVal::IndexSignature(_) => {}
    }
  }
}

fn collect_namespace<'a>(
  ns: &'a Node<NamespaceDecl>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  module_items: &mut Vec<ModuleItem<'a>>,
  names: &mut NameInterner,
  module_item: bool,
  is_item: bool,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  let name_id = names.intern(&ns.stx.name);
  let span = ctx.to_range(ns.loc);
  let text = names.resolve(name_id).unwrap().to_string();
  let ns_raw = RawNode::from(ns);
  let parent = ctx.current_parent();
  let mut desc = DefDescriptor::new(
    DefKind::Namespace,
    name_id,
    text,
    span,
    is_item,
    ambient,
    in_global,
    DefSource::None,
  );
  desc.parent = parent;
  desc.node = Some(ns_raw);
  // Nested namespaces (e.g. `namespace A.B {}`) are implicitly exported from
  // their containing namespace or module.
  //
  // Note: for external module declarations (`declare module "x" {}` / module
  // augmentations), TypeScript does *not* implicitly export a top-level
  // `namespace Foo` without an `export` modifier. However, nested namespaces
  // (`namespace A.B {}`) are still implicitly exported from their containing
  // namespace.
  desc.is_exported = ns.stx.export || (!module_item && parent.is_some());
  desc.type_source = Some(TypeSource::Namespace);
  descriptors.push(desc);
  ctx.with_parent(Some(ns_raw), |ctx| match &ns.stx.body {
    NamespaceBody::Block(stmts) => {
      for st in stmts.iter() {
        collect_stmt(
          st,
          descriptors,
          module_items,
          names,
          false,
          false,
          ambient,
          in_global,
          ctx,
        );
      }
    }
    NamespaceBody::Namespace(inner) => {
      collect_namespace(
        inner,
        descriptors,
        module_items,
        names,
        false,
        false,
        ambient,
        in_global,
        ctx,
      );
    }
  });
}

fn collect_var_decl<'a>(
  var_decl: &'a Node<parse_js::ast::stmt::decl::VarDecl>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  module_items: &mut Vec<ModuleItem<'a>>,
  names: &mut NameInterner,
  _module_item: bool,
  is_item: bool,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  let parent = ctx.current_parent();
  let kind = match var_decl.stx.mode {
    parse_js::ast::stmt::decl::VarDeclMode::Const => VarDeclKind::Const,
    parse_js::ast::stmt::decl::VarDeclMode::Let => VarDeclKind::Let,
    parse_js::ast::stmt::decl::VarDeclMode::Var => VarDeclKind::Var,
    parse_js::ast::stmt::decl::VarDeclMode::Using => VarDeclKind::Using,
    parse_js::ast::stmt::decl::VarDeclMode::AwaitUsing => VarDeclKind::AwaitUsing,
  };
  for declarator in var_decl.stx.declarators.iter() {
    let declarator_raw = RawNode(declarator as *const _ as *const ());
    let pat_names = collect_pat_names(&declarator.pattern.stx.pat, names, ctx);

    let (decl_name, decl_name_text) = pat_names
      .first()
      .map(|(id, _)| (*id, names.resolve(*id).unwrap().to_string()))
      .unwrap_or_else(|| {
        let name = names.intern("<var_decl>");
        (name, names.resolve(name).unwrap().to_string())
      });

    let mut declarator_desc = DefDescriptor::new(
      DefKind::VarDeclarator,
      decl_name,
      decl_name_text,
      ctx.to_range(declarator.pattern.loc),
      is_item,
      ambient,
      in_global,
      DefSource::Var(declarator, kind),
    );
    declarator_desc.parent = parent;
    declarator_desc.node = Some(declarator_raw);
    declarator_desc.is_exported = var_decl.stx.export;
    descriptors.push(declarator_desc);

    for (id, span) in pat_names {
      let mut desc = DefDescriptor::new(
        DefKind::Var,
        id,
        names.resolve(id).unwrap().to_string(),
        span,
        is_item,
        ambient,
        in_global,
        DefSource::None,
      );
      desc.parent = Some(declarator_raw);
      desc.is_exported = var_decl.stx.export;
      descriptors.push(desc);
    }

    collect_exprs_from_pat(
      &declarator.pattern.stx.pat,
      descriptors,
      module_items,
      names,
      ambient,
      in_global,
      ctx,
    );

    if let Some(init) = &declarator.initializer {
      collect_expr(
        init,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
  }
}

fn collect_for_lhs<'a>(
  lhs: &'a ForInOfLhs,
  _descriptors: &mut Vec<DefDescriptor<'a>>,
  _module_items: &mut Vec<ModuleItem<'a>>,
  names: &mut NameInterner,
  _ambient: bool,
  _in_global: bool,
  ctx: &mut LoweringContext,
) {
  match lhs {
    ForInOfLhs::Assign(pat) => {
      let _ = collect_pat_names(pat, names, ctx);
    }
    ForInOfLhs::Decl((_, pat_decl)) => {
      let _ = collect_pat_names(&pat_decl.stx.pat, names, ctx);
    }
  }
}

fn walk_stmt_children<'a>(
  stmt: &'a Node<AstStmt>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  module_items: &mut Vec<ModuleItem<'a>>,
  names: &mut NameInterner,
  _module_item: bool,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  match &*stmt.stx {
    AstStmt::Expr(expr_stmt) => collect_expr(
      &expr_stmt.stx.expr,
      descriptors,
      module_items,
      names,
      ambient,
      in_global,
      ctx,
    ),
    AstStmt::Return(ret) => {
      if let Some(v) = &ret.stx.value {
        collect_expr(v, descriptors, module_items, names, ambient, in_global, ctx);
      }
    }
    AstStmt::If(if_stmt) => {
      collect_expr(
        &if_stmt.stx.test,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_stmt(
        &if_stmt.stx.consequent,
        descriptors,
        module_items,
        names,
        false,
        false,
        ambient,
        in_global,
        ctx,
      );
      if let Some(alt) = &if_stmt.stx.alternate {
        collect_stmt(
          alt,
          descriptors,
          module_items,
          names,
          false,
          false,
          ambient,
          in_global,
          ctx,
        );
      }
    }
    AstStmt::Block(block) => {
      for stmt in block.stx.body.iter() {
        collect_stmt(
          stmt,
          descriptors,
          module_items,
          names,
          false,
          false,
          ambient,
          in_global,
          ctx,
        );
      }
    }
    AstStmt::While(wh) => {
      collect_expr(
        &wh.stx.condition,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_stmt(
        &wh.stx.body,
        descriptors,
        module_items,
        names,
        false,
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
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_stmt(
        &dw.stx.body,
        descriptors,
        module_items,
        names,
        false,
        false,
        ambient,
        in_global,
        ctx,
      );
    }
    AstStmt::ForTriple(for_stmt) => {
      match &for_stmt.stx.init {
        ForTripleStmtInit::Expr(e) => {
          collect_expr(e, descriptors, module_items, names, ambient, in_global, ctx)
        }
        ForTripleStmtInit::Decl(d) => collect_var_decl(
          d,
          descriptors,
          module_items,
          names,
          false,
          false,
          ambient,
          in_global,
          ctx,
        ),
        ForTripleStmtInit::None => {}
      }
      if let Some(cond) = &for_stmt.stx.cond {
        collect_expr(
          cond,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
      }
      if let Some(post) = &for_stmt.stx.post {
        collect_expr(
          post,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
      }
      collect_for_body(
        &for_stmt.stx.body,
        descriptors,
        module_items,
        names,
        false,
        ambient,
        in_global,
        ctx,
      );
    }
    AstStmt::ForIn(for_in) => {
      collect_for_lhs(
        &for_in.stx.lhs,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_expr(
        &for_in.stx.rhs,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_for_body(
        &for_in.stx.body,
        descriptors,
        module_items,
        names,
        false,
        ambient,
        in_global,
        ctx,
      );
    }
    AstStmt::ForOf(for_of) => {
      collect_for_lhs(
        &for_of.stx.lhs,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_expr(
        &for_of.stx.rhs,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_for_body(
        &for_of.stx.body,
        descriptors,
        module_items,
        names,
        false,
        ambient,
        in_global,
        ctx,
      );
    }
    AstStmt::Switch(sw) => {
      collect_expr(
        &sw.stx.test,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      for branch in sw.stx.branches.iter() {
        if let Some(case) = &branch.stx.case {
          collect_expr(
            case,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
        }
        for stmt in branch.stx.body.iter() {
          collect_stmt(
            stmt,
            descriptors,
            module_items,
            names,
            false,
            false,
            ambient,
            in_global,
            ctx,
          );
        }
      }
    }
    AstStmt::Try(tr) => {
      collect_block(
        &tr.stx.wrapped,
        descriptors,
        module_items,
        names,
        false,
        ambient,
        in_global,
        ctx,
      );
      if let Some(catch) = &tr.stx.catch {
        if let Some(param) = &catch.stx.parameter {
          let _ = collect_pat_names(&param.stx.pat, names, ctx);
        }
        for stmt in catch.stx.body.iter() {
          collect_stmt(
            stmt,
            descriptors,
            module_items,
            names,
            false,
            false,
            ambient,
            in_global,
            ctx,
          );
        }
      }
      if let Some(finally) = &tr.stx.finally {
        collect_block(
          finally,
          descriptors,
          module_items,
          names,
          false,
          ambient,
          in_global,
          ctx,
        );
      }
    }
    AstStmt::With(w) => {
      collect_expr(
        &w.stx.object,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_stmt(
        &w.stx.body,
        descriptors,
        module_items,
        names,
        false,
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
  module_items: &mut Vec<ModuleItem<'a>>,
  names: &mut NameInterner,
  _module_item: bool,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  for stmt in block.stx.body.iter() {
    collect_stmt(
      stmt,
      descriptors,
      module_items,
      names,
      false,
      false,
      ambient,
      in_global,
      ctx,
    );
  }
}

fn collect_for_body<'a>(
  body: &'a Node<ForBody>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  module_items: &mut Vec<ModuleItem<'a>>,
  names: &mut NameInterner,
  _module_item: bool,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  for stmt in body.stx.body.iter() {
    collect_stmt(
      stmt,
      descriptors,
      module_items,
      names,
      false,
      false,
      ambient,
      in_global,
      ctx,
    );
  }
}

fn collect_expr<'a>(
  expr: &'a Node<AstExpr>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  module_items: &mut Vec<ModuleItem<'a>>,
  names: &mut NameInterner,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  match &*expr.stx {
    AstExpr::Func(f) => {
      let (name_id, name_text) = name_from_optional(&f.stx.name, names);
      let mut desc = DefDescriptor::new(
        DefKind::Function,
        name_id,
        name_text,
        ctx.to_range(expr.loc),
        false,
        ambient,
        in_global,
        DefSource::FuncExpr(f),
      );
      desc.parent = ctx.current_parent();
      descriptors.push(desc);
      let func_raw = RawNode::from(f);
      ctx.with_parent(Some(func_raw), |ctx| {
        collect_func_params(
          &f.stx.func,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
        collect_func_body(
          &f.stx.func,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
      });
    }
    AstExpr::ArrowFunc(f) => {
      let name_id = names.intern("<arrow>");
      let mut desc = DefDescriptor::new(
        DefKind::Function,
        name_id,
        names.resolve(name_id).unwrap().to_string(),
        ctx.to_range(expr.loc),
        false,
        ambient,
        in_global,
        DefSource::ArrowFunction(f),
      );
      desc.parent = ctx.current_parent();
      descriptors.push(desc);
      let func_raw = RawNode::from(f);
      ctx.with_parent(Some(func_raw), |ctx| {
        collect_func_params(
          &f.stx.func,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
        collect_func_body(
          &f.stx.func,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
      });
    }
    AstExpr::Class(class_expr) => {
      let (name_id, text) = name_from_optional(&class_expr.stx.name, names);
      let class_raw = RawNode::from(class_expr);
      let mut desc = DefDescriptor::new(
        DefKind::Class,
        name_id,
        text,
        ctx.to_range(expr.loc),
        false,
        ambient,
        in_global,
        DefSource::ClassExpr(class_expr),
      );
      desc.type_source = Some(TypeSource::ClassExpr(class_expr));
      desc.parent = ctx.current_parent();
      descriptors.push(desc);
      ctx.with_parent(Some(class_raw), |ctx| {
        for decorator in class_expr.stx.decorators.iter() {
          collect_expr(
            &decorator.stx.expression,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
        }
        if let Some(extends) = class_expr.stx.extends.as_ref() {
          collect_expr(
            extends,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
        }
        collect_class_members(
          &class_expr.stx.members,
          class_raw,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
      });
    }
    AstExpr::Cond(cond) => {
      collect_expr(
        &cond.stx.test,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_expr(
        &cond.stx.consequent,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_expr(
        &cond.stx.alternate,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    AstExpr::Binary(bin) => {
      collect_expr(
        &bin.stx.left,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_expr(
        &bin.stx.right,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    AstExpr::Call(call) => {
      collect_expr(
        &call.stx.callee,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      for arg in call.stx.arguments.iter() {
        collect_expr(
          &arg.stx.value,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
      }
    }
    AstExpr::Member(mem) => {
      collect_expr(
        &mem.stx.left,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    AstExpr::ComputedMember(mem) => {
      collect_expr(
        &mem.stx.object,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      collect_expr(
        &mem.stx.member,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    AstExpr::TaggedTemplate(tag) => {
      collect_expr(
        &tag.stx.function,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
      for part in tag.stx.parts.iter() {
        if let parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) = part {
          collect_expr(
            expr,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
        }
      }
    }
    AstExpr::LitArr(arr) => {
      for el in arr.stx.elements.iter() {
        match el {
          parse_js::ast::expr::lit::LitArrElem::Single(expr)
          | parse_js::ast::expr::lit::LitArrElem::Rest(expr) => {
            collect_expr(
              expr,
              descriptors,
              module_items,
              names,
              ambient,
              in_global,
              ctx,
            );
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
          ObjMemberType::Valued { key, val } => match val {
            ClassOrObjVal::Prop(Some(expr)) => collect_expr(
              expr,
              descriptors,
              module_items,
              names,
              ambient,
              in_global,
              ctx,
            ),
            ClassOrObjVal::Getter(getter) => {
              let (name_id, name_text) = obj_key_name(key, names);
              let mut desc = DefDescriptor::new(
                DefKind::Getter,
                name_id,
                name_text,
                ctx.to_range(getter.loc),
                false,
                ambient,
                in_global,
                DefSource::Getter(getter),
              );
              desc.parent = ctx.current_parent();
              descriptors.push(desc);
              let getter_raw = RawNode::from(getter);
              ctx.with_parent(Some(getter_raw), |ctx| {
                collect_func_params(
                  &getter.stx.func,
                  descriptors,
                  module_items,
                  names,
                  ambient,
                  in_global,
                  ctx,
                );
                collect_func_body(
                  &getter.stx.func,
                  descriptors,
                  module_items,
                  names,
                  ambient,
                  in_global,
                  ctx,
                );
              });
            }
            ClassOrObjVal::Setter(setter) => {
              let (name_id, name_text) = obj_key_name(key, names);
              let mut desc = DefDescriptor::new(
                DefKind::Setter,
                name_id,
                name_text,
                ctx.to_range(setter.loc),
                false,
                ambient,
                in_global,
                DefSource::Setter(setter),
              );
              desc.parent = ctx.current_parent();
              descriptors.push(desc);
              let setter_raw = RawNode::from(setter);
              ctx.with_parent(Some(setter_raw), |ctx| {
                collect_func_params(
                  &setter.stx.func,
                  descriptors,
                  module_items,
                  names,
                  ambient,
                  in_global,
                  ctx,
                );
                collect_func_body(
                  &setter.stx.func,
                  descriptors,
                  module_items,
                  names,
                  ambient,
                  in_global,
                  ctx,
                );
              });
            }
            ClassOrObjVal::Method(method) => {
              let (name_id, name_text) = obj_key_name(key, names);
              let mut desc = DefDescriptor::new(
                DefKind::Method,
                name_id,
                name_text,
                ctx.to_range(method.loc),
                false,
                ambient,
                in_global,
                DefSource::Method(method),
              );
              desc.parent = ctx.current_parent();
              descriptors.push(desc);
              let method_raw = RawNode::from(method);
              ctx.with_parent(Some(method_raw), |ctx| {
                collect_func_params(
                  &method.stx.func,
                  descriptors,
                  module_items,
                  names,
                  ambient,
                  in_global,
                  ctx,
                );
                collect_func_body(
                  &method.stx.func,
                  descriptors,
                  module_items,
                  names,
                  ambient,
                  in_global,
                  ctx,
                );
              });
            }
            _ => {}
          },
          ObjMemberType::Rest { val } => collect_expr(
            val,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          ),
          ObjMemberType::Shorthand { .. } => {}
        }
      }
    }
    AstExpr::LitTemplate(tmpl) => {
      for part in tmpl.stx.parts.iter() {
        if let parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) = part {
          collect_expr(
            expr,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
        }
      }
    }
    AstExpr::ArrPat(arr) => {
      for elem in arr.stx.elements.iter().flatten() {
        collect_exprs_from_pat(
          &elem.target,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
        if let Some(default) = &elem.default_value {
          collect_expr(
            default,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
        }
      }
      if let Some(rest) = &arr.stx.rest {
        collect_exprs_from_pat(
          rest,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
      }
    }
    AstExpr::ObjPat(obj) => {
      for prop in obj.stx.properties.iter() {
        collect_exprs_from_pat(
          &prop.stx.target,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
        if let Some(default) = &prop.stx.default_value {
          collect_expr(
            default,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
        }
      }
      if let Some(rest) = &obj.stx.rest {
        collect_exprs_from_pat(
          rest,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
      }
    }
    AstExpr::TypeAssertion(assert) => {
      collect_expr(
        &assert.stx.expression,
        descriptors,
        module_items,
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
        module_items,
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
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    AstExpr::JsxElem(elem) => {
      collect_jsx_elem(
        elem,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    _ => {}
  }
}

fn collect_jsx_elem<'a>(
  elem: &'a Node<jsx::JsxElem>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  module_items: &mut Vec<ModuleItem<'a>>,
  names: &mut NameInterner,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  for attr in elem.stx.attributes.iter() {
    match attr {
      jsx::JsxAttr::Named { value, .. } => {
        if let Some(value) = value {
          match value {
            jsx::JsxAttrVal::Text(_) => {}
            jsx::JsxAttrVal::Expression(container) => {
              if !is_empty_jsx_expr_placeholder(&container.stx.value) {
                collect_expr(
                  &container.stx.value,
                  descriptors,
                  module_items,
                  names,
                  ambient,
                  in_global,
                  ctx,
                );
              }
            }
            jsx::JsxAttrVal::Element(child) => {
              collect_jsx_elem(
                child,
                descriptors,
                module_items,
                names,
                ambient,
                in_global,
                ctx,
              );
            }
          }
        }
      }
      jsx::JsxAttr::Spread { value } => {
        collect_expr(
          &value.stx.value,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
      }
    }
  }

  for child in elem.stx.children.iter() {
    match child {
      jsx::JsxElemChild::Element(child_elem) => {
        collect_jsx_elem(
          child_elem,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
      }
      jsx::JsxElemChild::Expr(container) => {
        if !is_empty_jsx_expr_placeholder(&container.stx.value) {
          collect_expr(
            &container.stx.value,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
        }
      }
      jsx::JsxElemChild::Text(_) => {}
    }
  }
}

fn obj_key_name(
  key: &parse_js::ast::class_or_object::ClassOrObjKey,
  names: &mut NameInterner,
) -> (NameId, String) {
  let name_id = match key {
    parse_js::ast::class_or_object::ClassOrObjKey::Direct(direct) => names.intern(&direct.stx.key),
    parse_js::ast::class_or_object::ClassOrObjKey::Computed(expr) => {
      let fingerprint = stable_expr_fingerprint(expr);
      let synthetic = format!("<computed:{:016x}>", fingerprint);
      names.intern(synthetic)
    }
  };
  let name_text = names.resolve(name_id).unwrap().to_string();
  (name_id, name_text)
}

fn stable_expr_fingerprint(expr: &Node<AstExpr>) -> u64 {
  // Use the debug representation of the syntax (which intentionally omits
  // locations) so fingerprints are stable across unrelated edits that shift
  // spans.
  let mut hasher = StableHasher::new();
  let debug_repr = format!("{:?}", expr.stx);
  hasher.write_str(&debug_repr);
  hasher.finish()
}

fn collect_exprs_from_pat<'a>(
  pat: &'a Node<AstPat>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  module_items: &mut Vec<ModuleItem<'a>>,
  names: &mut NameInterner,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  match &*pat.stx {
    AstPat::Arr(arr) => {
      for elem in arr.stx.elements.iter().flatten() {
        collect_exprs_from_pat(
          &elem.target,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
        if let Some(default) = &elem.default_value {
          collect_expr(
            default,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
        }
      }
      if let Some(rest) = &arr.stx.rest {
        collect_exprs_from_pat(
          rest,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
      }
    }
    AstPat::Obj(obj) => {
      for prop in obj.stx.properties.iter() {
        collect_exprs_from_pat(
          &prop.stx.target,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
        if let Some(default) = &prop.stx.default_value {
          collect_expr(
            default,
            descriptors,
            module_items,
            names,
            ambient,
            in_global,
            ctx,
          );
        }
      }
      if let Some(rest) = &obj.stx.rest {
        collect_exprs_from_pat(
          rest,
          descriptors,
          module_items,
          names,
          ambient,
          in_global,
          ctx,
        );
      }
    }
    AstPat::AssignTarget(expr) => collect_expr(
      expr,
      descriptors,
      module_items,
      names,
      ambient,
      in_global,
      ctx,
    ),
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
  module_items: &mut Vec<ModuleItem<'a>>,
  names: &mut NameInterner,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  for param in func.stx.parameters.iter() {
    for decorator in param.stx.decorators.iter() {
      collect_expr(
        &decorator.stx.expression,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
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
      collect_expr(
        default,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
  }
}

fn collect_func_body<'a>(
  func: &'a Node<Func>,
  descriptors: &mut Vec<DefDescriptor<'a>>,
  module_items: &mut Vec<ModuleItem<'a>>,
  names: &mut NameInterner,
  ambient: bool,
  in_global: bool,
  ctx: &mut LoweringContext,
) {
  match &func.stx.body {
    Some(FuncBody::Block(block)) => {
      for stmt in block.iter() {
        collect_stmt(
          stmt,
          descriptors,
          module_items,
          names,
          false,
          false,
          ambient,
          in_global,
          ctx,
        );
      }
    }
    Some(FuncBody::Expression(expr)) => {
      collect_expr(
        expr,
        descriptors,
        module_items,
        names,
        ambient,
        in_global,
        ctx,
      );
    }
    None => {}
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
  let parent = ctx.current_parent();
  for param in params.iter() {
    let id = names.intern(&param.stx.name);
    let span = ctx.to_range(param.loc);
    let mut desc = DefDescriptor::new(
      DefKind::Param,
      id,
      names.resolve(id).unwrap().to_string(),
      span,
      false,
      ambient,
      in_global,
      DefSource::None,
    );
    desc.parent = parent;
    descriptors.push(desc);
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
  let parent = ctx.current_parent();
  for (name_id, span) in collect_pat_names(&pat_decl.stx.pat, names, ctx) {
    let text = names.resolve(name_id).unwrap().to_string();
    let mut desc = DefDescriptor::new(
      kind,
      name_id,
      text,
      span,
      false,
      ambient,
      in_global,
      DefSource::None,
    );
    desc.parent = parent;
    descriptors.push(desc);
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

fn push_named_export(
  exports: &mut Vec<Export>,
  span_map: &mut SpanMap,
  next_export: &mut u32,
  next_export_spec: &mut u32,
  span: TextRange,
  name_id: NameId,
  local_def: Option<DefId>,
  is_type_only: bool,
) {
  let spec_id = ExportSpecifierId(*next_export_spec);
  *next_export_spec += 1;
  span_map.add_export_specifier(span, spec_id);
  exports.push(Export {
    id: ExportId(*next_export),
    span,
    kind: ExportKind::Named(ExportNamed {
      source: None,
      attributes: None,
      specifiers: vec![ExportSpecifier {
        id: spec_id,
        local: name_id,
        exported: name_id,
        local_def,
        is_type_only,
        span,
      }],
      is_type_only,
    }),
  });
  *next_export += 1;
}

fn body_by_id<'a>(
  body_id: BodyId,
  bodies: &'a [Arc<Body>],
  body_index: &BTreeMap<BodyId, usize>,
) -> Option<&'a Body> {
  body_index
    .get(&body_id)
    .and_then(|idx| bodies.get(*idx))
    .map(Arc::as_ref)
}

fn lower_module_item_attributes(
  attrs: &Node<AstExpr>,
  disambiguator: u32,
  names: &mut NameInterner,
  def_lookup: &DefLookup,
  types: &mut crate::hir::TypeArenasByDef,
  bodies: &mut Vec<Arc<Body>>,
  body_ids: &mut Vec<BodyId>,
  body_index: &mut BTreeMap<BodyId, usize>,
  allocated_body_ids: &mut BTreeMap<u32, BodyPath>,
  span_map: &mut SpanMap,
  ctx: &mut LoweringContext,
) -> ModuleAttributes {
  let span = ctx.to_range(attrs.loc);
  let body_id = allocate_body_id(
    BodyPath::new(DefId(ctx.file.0), BodyKind::Unknown, disambiguator),
    allocated_body_ids,
  );
  let mut builder = BodyBuilder::new(
    DefId(u32::MAX),
    span,
    body_id,
    BodyKind::Unknown,
    def_lookup,
    names,
    types,
    span_map,
  );
  let expr = lower_expr(attrs, &mut builder, ctx);
  let idx = bodies.len();
  body_ids.push(body_id);
  body_index.insert(body_id, idx);
  bodies.push(Arc::new(builder.finish_with_id(body_id)));
  ModuleAttributes {
    body: body_id,
    expr,
    span,
  }
}

fn lower_module_items(
  module_items: Vec<ModuleItem<'_>>,
  names: &mut NameInterner,
  def_lookup: &DefLookup,
  defs: &[DefData],
  _def_index: &BTreeMap<DefId, usize>,
  bodies: &mut Vec<Arc<Body>>,
  body_index: &mut BTreeMap<BodyId, usize>,
  body_ids: &mut Vec<BodyId>,
  allocated_body_ids: &mut BTreeMap<u32, BodyPath>,
  types: &mut crate::hir::TypeArenasByDef,
  span_map: &mut SpanMap,
  ctx: &mut LoweringContext,
) -> (Vec<Import>, Vec<Export>) {
  let mut imports = Vec::new();
  let mut exports = Vec::new();
  let mut next_import = 0u32;
  let mut next_import_spec = 0u32;
  let mut next_export = 0u32;
  let mut next_export_spec = 0u32;

  for item in module_items {
    match item.kind {
      ModuleItemKind::Import(import) => {
        let mut named = Vec::new();
        let mut default = None;
        let mut namespace = None;
        if let Some(def) = &import.stx.default {
          if let Some((name_id, span)) =
            collect_pat_names(&def.stx.pat, names, ctx).first().cloned()
          {
            default = Some(ImportBinding {
              local: name_id,
              local_def: find_def(defs, DefKind::ImportBinding, span).map(|d| d.id),
              span,
            });
          }
        }
        if let Some(names_list) = &import.stx.names {
          match names_list {
            ImportNames::All(pat) => {
              if let Some((name_id, span)) =
                collect_pat_names(&pat.stx.pat, names, ctx).first().cloned()
              {
                namespace = Some(ImportBinding {
                  local: name_id,
                  local_def: find_def(defs, DefKind::ImportBinding, span).map(|d| d.id),
                  span,
                });
              }
            }
            ImportNames::Specific(list) => {
              for spec in list.iter() {
                let imported = names.intern(spec.stx.importable.as_str());
                let (local, span) = collect_pat_names(&spec.stx.alias.stx.pat, names, ctx)
                  .first()
                  .cloned()
                  .unwrap_or((imported, ctx.to_range(spec.loc)));
                let spec_id = ImportSpecifierId(next_import_spec);
                next_import_spec += 1;
                span_map.add_import_specifier(span, spec_id);
                named.push(ImportNamed {
                  id: spec_id,
                  imported,
                  local,
                  local_def: find_def(defs, DefKind::ImportBinding, span).map(|d| d.id),
                  is_type_only: spec.stx.type_only || import.stx.type_only,
                  span,
                });
              }
            }
          }
        }
        let specifier = ModuleSpecifier {
          value: import.stx.module.clone(),
          span: item.span,
        };
        let attributes = import.stx.attributes.as_ref().map(|attrs| {
          lower_module_item_attributes(
            attrs,
            item.span.start,
            names,
            def_lookup,
            types,
            bodies,
            body_ids,
            body_index,
            allocated_body_ids,
            span_map,
            ctx,
          )
        });
        imports.push(Import {
          id: ImportId(next_import),
          span: item.span,
          kind: ImportKind::Es(ImportEs {
            specifier,
            attributes,
            is_type_only: import.stx.type_only,
            default,
            namespace,
            named,
          }),
        });
        next_import += 1;
      }
      ModuleItemKind::ImportType(import_type) => {
        let mut named = Vec::new();
        for name in import_type.stx.names.iter() {
          let imported = names.intern(&name.imported);
          let local_name = name
            .local
            .as_ref()
            .map(|l| names.intern(l))
            .unwrap_or(imported);
          let span = item.span;
          let spec_id = ImportSpecifierId(next_import_spec);
          next_import_spec += 1;
          span_map.add_import_specifier(span, spec_id);
          named.push(ImportNamed {
            id: spec_id,
            imported,
            local: local_name,
            local_def: find_def(defs, DefKind::ImportBinding, span).map(|d| d.id),
            is_type_only: true,
            span,
          });
        }
        let specifier = ModuleSpecifier {
          value: import_type.stx.module.clone(),
          span: item.span,
        };
        imports.push(Import {
          id: ImportId(next_import),
          span: item.span,
          kind: ImportKind::Es(ImportEs {
            specifier,
            attributes: None,
            is_type_only: true,
            default: None,
            namespace: None,
            named,
          }),
        });
        next_import += 1;
      }
      ModuleItemKind::ImportEquals(ie) => {
        let name_id = names.intern(&ie.stx.name);
        let local_def = find_def(defs, DefKind::ImportBinding, item.span).map(|d| d.id);
        let target = match &ie.stx.rhs {
          ImportEqualsRhs::Require { module } => ImportEqualsTarget::Module(ModuleSpecifier {
            value: module.clone(),
            span: item.span,
          }),
          ImportEqualsRhs::EntityName { path } => {
            ImportEqualsTarget::Path(path.iter().map(|p| names.intern(p)).collect())
          }
        };
        imports.push(Import {
          id: ImportId(next_import),
          span: item.span,
          kind: ImportKind::ImportEquals(ImportEquals {
            local: ImportBinding {
              local: name_id,
              local_def,
              span: item.span,
            },
            target,
          }),
        });
        if ie.stx.export {
          push_named_export(
            &mut exports,
            span_map,
            &mut next_export,
            &mut next_export_spec,
            item.span,
            name_id,
            local_def,
            false,
          );
        }
        next_import += 1;
      }
      ModuleItemKind::ExportList(export) => {
        let source = export.stx.from.as_ref().map(|s| ModuleSpecifier {
          value: s.clone(),
          span: item.span,
        });
        let attributes = export.stx.attributes.as_ref().map(|attrs| {
          lower_module_item_attributes(
            attrs,
            item.span.start,
            names,
            def_lookup,
            types,
            bodies,
            body_ids,
            body_index,
            allocated_body_ids,
            span_map,
            ctx,
          )
        });
        match &export.stx.names {
          ExportNames::All(alias) => {
            let alias = alias.as_ref().map(|a| ExportAlias {
              exported: names.intern(&a.stx.name),
              span: ctx.to_range(a.loc),
            });
            exports.push(Export {
              id: ExportId(next_export),
              span: item.span,
              kind: ExportKind::ExportAll(ExportAll {
                source: source.unwrap_or(ModuleSpecifier {
                  value: "".into(),
                  span: item.span,
                }),
                attributes,
                alias,
                is_type_only: export.stx.type_only,
              }),
            });
            next_export += 1;
          }
          ExportNames::Specific(list) => {
            let mut specs = Vec::new();
            for export_name in list.iter() {
              let exported = names.intern(export_name.stx.alias.stx.name.as_str());
              let local = names.intern(export_name.stx.exportable.as_str());
              let span = ctx.to_range(export_name.loc);
              let spec_id = ExportSpecifierId(next_export_spec);
              next_export_spec += 1;
              span_map.add_export_specifier(span, spec_id);
              specs.push(ExportSpecifier {
                id: spec_id,
                local,
                exported,
                local_def: find_def(defs, DefKind::ExportAlias, span).map(|d| d.id),
                is_type_only: export.stx.type_only || export_name.stx.type_only,
                span,
              });
            }
            exports.push(Export {
              id: ExportId(next_export),
              span: item.span,
              kind: ExportKind::Named(ExportNamed {
                source,
                attributes,
                specifiers: specs,
                is_type_only: export.stx.type_only,
              }),
            });
            next_export += 1;
          }
        }
      }
      ModuleItemKind::ExportType(export_type) => {
        let source = export_type.stx.module.as_ref().map(|m| ModuleSpecifier {
          value: m.clone(),
          span: item.span,
        });
        let mut specs = Vec::new();
        for name in export_type.stx.names.iter() {
          let local = names.intern(&name.local);
          let exported = name
            .exported
            .as_ref()
            .map(|n| names.intern(n))
            .unwrap_or(local);
          let spec_id = ExportSpecifierId(next_export_spec);
          next_export_spec += 1;
          span_map.add_export_specifier(item.span, spec_id);
          specs.push(ExportSpecifier {
            id: spec_id,
            local,
            exported,
            local_def: find_def(defs, DefKind::TypeAlias, item.span).map(|d| d.id),
            is_type_only: true,
            span: item.span,
          });
        }
        exports.push(Export {
          id: ExportId(next_export),
          span: item.span,
          kind: ExportKind::Named(ExportNamed {
            source,
            attributes: None,
            specifiers: specs,
            is_type_only: true,
          }),
        });
        next_export += 1;
      }
      ModuleItemKind::ExportDefaultExpr(node) => {
        if let Some(def) = def_lookup.def_for_node(node) {
          if let Some(body_id) = def_lookup.body_for(def) {
            let expr_id = body_by_id(body_id, bodies, body_index)
              .and_then(|b| b.exprs.len().checked_sub(1).map(|idx| ExprId(idx as u32)))
              .unwrap_or(ExprId(0));
            exports.push(Export {
              id: ExportId(next_export),
              span: item.span,
              kind: ExportKind::Default(ExportDefault {
                value: ExportDefaultValue::Expr {
                  expr: expr_id,
                  body: body_id,
                },
              }),
            });
            next_export += 1;
          }
        }
      }
      ModuleItemKind::ExportAssignment(assign) => {
        if let Some(def) = def_lookup.def_for_node(assign) {
          if let Some(body_id) = def_lookup.body_for(def) {
            let expr = body_by_id(body_id, bodies, body_index)
              .and_then(|b| b.exprs.len().checked_sub(1).map(|idx| ExprId(idx as u32)))
              .unwrap_or(ExprId(0));
            exports.push(Export {
              id: ExportId(next_export),
              span: item.span,
              kind: ExportKind::Assignment(ExportAssignment {
                expr,
                body: body_id,
              }),
            });
            next_export += 1;
          }
        }
      }
      ModuleItemKind::ExportAsNamespace(export_ns) => {
        let name_id = names.intern(&export_ns.stx.name);
        exports.push(Export {
          id: ExportId(next_export),
          span: item.span,
          kind: ExportKind::AsNamespace(ExportAsNamespace {
            name: name_id,
            span: item.span,
          }),
        });
        next_export += 1;
      }
      ModuleItemKind::ExportedDecl(decl) => match decl.kind {
        ExportedDeclKind::Func(func) => {
          if let Some(def) = def_lookup
            .def_for_node(func)
            .or_else(|| find_def(defs, DefKind::Function, func.loc.into()).map(|d| d.id))
          {
            let body = def_lookup.body_for(def).unwrap_or(BodyId(u32::MAX));
            if decl.default {
              exports.push(Export {
                id: ExportId(next_export),
                span: decl.span,
                kind: ExportKind::Default(ExportDefault {
                  value: ExportDefaultValue::Function {
                    def,
                    body,
                    name: func.stx.name.as_ref().map(|n| names.intern(&n.stx.name)),
                  },
                }),
              });
              next_export += 1;
            } else {
              let Some(def_data) = defs
                .iter()
                .find(|d| d.id == def)
                .or_else(|| find_def(defs, DefKind::Function, func.loc.into()))
              else {
                continue;
              };
              let name_id = def_data.path.name;
              push_named_export(
                &mut exports,
                span_map,
                &mut next_export,
                &mut next_export_spec,
                decl.span,
                name_id,
                Some(def),
                decl.type_only,
              );
            }
          }
        }
        ExportedDeclKind::Class(class_decl) => {
          if let Some(def) = def_lookup
            .def_for_node(class_decl)
            .or_else(|| find_def(defs, DefKind::Class, decl.span).map(|d| d.id))
          {
            let body = def_lookup.body_for(def).unwrap_or(BodyId(u32::MAX));
            if decl.default {
              exports.push(Export {
                id: ExportId(next_export),
                span: decl.span,
                kind: ExportKind::Default(ExportDefault {
                  value: ExportDefaultValue::Class {
                    def,
                    body,
                    name: class_decl
                      .stx
                      .name
                      .as_ref()
                      .map(|n| names.intern(&n.stx.name)),
                  },
                }),
              });
              next_export += 1;
            } else {
              let Some(def_data) = defs
                .iter()
                .find(|d| d.id == def)
                .or_else(|| find_def(defs, DefKind::Class, decl.span))
              else {
                continue;
              };
              let name_id = def_data.path.name;
              push_named_export(
                &mut exports,
                span_map,
                &mut next_export,
                &mut next_export_spec,
                decl.span,
                name_id,
                Some(def),
                decl.type_only,
              );
            }
          }
        }
        ExportedDeclKind::Var(var_decl) => {
          let mut specifiers = Vec::new();
          for declarator in var_decl.stx.declarators.iter() {
            for (name_id, span) in collect_pat_names(&declarator.pattern.stx.pat, names, ctx) {
              let spec_id = ExportSpecifierId(next_export_spec);
              next_export_spec += 1;
              span_map.add_export_specifier(span, spec_id);
              specifiers.push(ExportSpecifier {
                id: spec_id,
                local: name_id,
                exported: name_id,
                local_def: find_def(defs, DefKind::Var, span).map(|d| d.id),
                is_type_only: decl.type_only,
                span,
              });
            }
          }
          if !specifiers.is_empty() {
            exports.push(Export {
              id: ExportId(next_export),
              span: decl.span,
              kind: ExportKind::Named(ExportNamed {
                source: None,
                attributes: None,
                specifiers,
                is_type_only: decl.type_only,
              }),
            });
            next_export += 1;
          }
        }
        ExportedDeclKind::Interface(intf) => {
          if let Some(def) = find_def(defs, DefKind::Interface, decl.span) {
            let name_id = def.name;
            push_named_export(
              &mut exports,
              span_map,
              &mut next_export,
              &mut next_export_spec,
              decl.span,
              name_id,
              Some(def.id),
              true,
            );
          } else {
            let name_id = names.intern(&intf.stx.name);
            push_named_export(
              &mut exports,
              span_map,
              &mut next_export,
              &mut next_export_spec,
              decl.span,
              name_id,
              None,
              true,
            );
          }
        }
        ExportedDeclKind::TypeAlias(alias) => {
          let def = find_def(defs, DefKind::TypeAlias, decl.span);
          let name_id = def
            .map(|info| info.name)
            .unwrap_or_else(|| names.intern(&alias.stx.name));
          push_named_export(
            &mut exports,
            span_map,
            &mut next_export,
            &mut next_export_spec,
            decl.span,
            name_id,
            def.map(|d| d.id),
            true,
          );
        }
        ExportedDeclKind::Enum(en) => {
          let def = find_def(defs, DefKind::Enum, decl.span);
          let name_id = def
            .map(|info| info.name)
            .unwrap_or_else(|| names.intern(&en.stx.name));
          push_named_export(
            &mut exports,
            span_map,
            &mut next_export,
            &mut next_export_spec,
            decl.span,
            name_id,
            def.map(|d| d.id),
            decl.type_only,
          );
        }
        ExportedDeclKind::Namespace(ns) => {
          let def = find_def(defs, DefKind::Namespace, decl.span);
          let name_id = def
            .map(|info| info.name)
            .unwrap_or_else(|| names.intern(&ns.stx.name));
          push_named_export(
            &mut exports,
            span_map,
            &mut next_export,
            &mut next_export_spec,
            decl.span,
            name_id,
            def.map(|d| d.id),
            decl.type_only,
          );
        }
        ExportedDeclKind::Module(module) => {
          let def = find_def(defs, DefKind::Module, decl.span);
          let name_id = def.map(|info| info.name).unwrap_or_else(|| {
            let name_text = module_name_text(&module.stx.name);
            names.intern(&name_text)
          });
          push_named_export(
            &mut exports,
            span_map,
            &mut next_export,
            &mut next_export_spec,
            decl.span,
            name_id,
            def.map(|d| d.id),
            decl.type_only,
          );
        }
        ExportedDeclKind::AmbientVar(av) => {
          let def = find_def(defs, DefKind::Var, decl.span);
          let name_id = def
            .map(|info| info.name)
            .unwrap_or_else(|| names.intern(&av.stx.name));
          push_named_export(
            &mut exports,
            span_map,
            &mut next_export,
            &mut next_export_spec,
            decl.span,
            name_id,
            def.map(|d| d.id),
            decl.type_only,
          );
        }
        ExportedDeclKind::AmbientFunction(af) => {
          let def = find_def(defs, DefKind::Function, decl.span);
          let name_id = def
            .map(|info| info.name)
            .unwrap_or_else(|| names.intern(&af.stx.name));
          push_named_export(
            &mut exports,
            span_map,
            &mut next_export,
            &mut next_export_spec,
            decl.span,
            name_id,
            def.map(|d| d.id),
            decl.type_only,
          );
        }
        ExportedDeclKind::AmbientClass(ac) => {
          let def = find_def(defs, DefKind::Class, decl.span);
          let name_id = def
            .map(|info| info.name)
            .unwrap_or_else(|| names.intern(&ac.stx.name));
          push_named_export(
            &mut exports,
            span_map,
            &mut next_export,
            &mut next_export_spec,
            decl.span,
            name_id,
            def.map(|d| d.id),
            decl.type_only,
          );
        }
      },
    }
  }

  (imports, exports)
}

fn find_def<'a>(defs: &'a [DefData], kind: DefKind, span: TextRange) -> Option<&'a DefData> {
  defs.iter().find(|d| d.path.kind == kind && d.span == span)
}

#[cfg(test)]
mod tests {
  use crate::ids::{with_test_body_path_hasher, with_test_def_path_hasher};
  use crate::lower_from_source_with_kind;
  use crate::FileKind;
  use std::collections::{BTreeMap, HashSet};

  #[test]
  fn def_ids_are_rehashed_on_collision() {
    let source = "function first() {}\nfunction second() {}";
    let lowered = with_test_def_path_hasher(
      |_| 1,
      || lower_from_source_with_kind(FileKind::Ts, source).expect("lower"),
    );

    let ids: Vec<_> = lowered.defs.iter().map(|d| d.id).collect();
    assert_eq!(ids.len(), 2);
    assert_eq!(ids[0].0, 1, "first def should keep overridden hash");
    assert_ne!(
      ids[0], ids[1],
      "collisions must be resolved by rehashing with a salt"
    );
    let unique_ids: HashSet<_> = ids.iter().copied().collect();
    assert_eq!(
      unique_ids.len(),
      ids.len(),
      "all DefIds should be unique after rehashing"
    );

    let ids_again: Vec<_> = with_test_def_path_hasher(
      |_| 1,
      || {
        lower_from_source_with_kind(FileKind::Ts, source)
          .expect("lower deterministically")
          .defs
          .into_iter()
          .map(|def| def.id)
          .collect()
      },
    );
    assert_eq!(ids, ids_again, "rehashing must remain deterministic");

    let def_path_ids: HashSet<_> = lowered.hir.def_paths.values().copied().collect();
    assert_eq!(
      def_path_ids.len(),
      lowered.hir.def_paths.len(),
      "DefPath map should not reuse DefIds after collisions"
    );
  }

  #[test]
  fn body_ids_are_rehashed_on_collision() {
    let source = "function first() {}\nfunction second() {}";
    let lowered = || {
      with_test_body_path_hasher(
        |_| 1,
        || lower_from_source_with_kind(FileKind::Ts, source).expect("lower"),
      )
    };

    let first = lowered();
    let second = lowered();

    assert!(
      first.hir.bodies.len() > 2,
      "expected multiple bodies (including root) to exercise collision handling"
    );

    let first_ids: HashSet<_> = first.hir.bodies.iter().copied().collect();
    assert_eq!(
      first_ids.len(),
      first.hir.bodies.len(),
      "BodyIds should be rehashed to remain unique"
    );
    assert!(
      first_ids.iter().any(|id| id.0 == 1),
      "override should force the base BodyPath hash to collide"
    );
    assert_eq!(
      first.body_index.len(),
      first.hir.bodies.len(),
      "body index should track every body even when hashes collide"
    );

    let first_map: BTreeMap<_, _> = first
      .defs
      .iter()
      .filter_map(|def| def.body.map(|body| (def.path, body)))
      .collect();
    let second_map: BTreeMap<_, _> = second
      .defs
      .iter()
      .filter_map(|def| def.body.map(|body| (def.path, body)))
      .collect();
    assert_eq!(
      first_map, second_map,
      "BodyId allocation should be deterministic under collisions"
    );

    let second_ids: HashSet<_> = second.hir.bodies.iter().copied().collect();
    assert_eq!(
      first_ids, second_ids,
      "BodyIds should remain stable across runs when collisions are forced"
    );
  }
}
