use crate::ids::BodyId;
use crate::ids::DefId;
use crate::ids::DefPath;
use crate::ids::ExportId;
use crate::ids::ExportSpecifierId;
use crate::ids::ExprId;
use crate::ids::ImportId;
use crate::ids::ImportSpecifierId;
use crate::ids::NameId;
use crate::ids::PatId;
use crate::ids::StmtId;
use crate::ids::TypeExprId;
use crate::ids::TypeMemberId;
use crate::ids::TypeParamId;
use crate::intern::NameInterner;
use crate::span_map::SpanMap;
use diagnostics::FileId;
use diagnostics::TextRange;
use std::collections::BTreeMap;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileKind {
  Js,
  Jsx,
  Ts,
  Tsx,
  Dts,
}

#[derive(Debug, Clone, PartialEq)]
pub struct HirFile {
  pub file: FileId,
  pub file_kind: FileKind,
  pub root_body: BodyId,
  pub items: Vec<DefId>,
  pub bodies: Vec<BodyId>,
  pub def_paths: BTreeMap<DefPath, DefId>,
  pub imports: Vec<Import>,
  pub exports: Vec<Export>,
  pub span_map: SpanMap,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ModuleSpecifier {
  pub value: String,
  pub span: TextRange,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Import {
  pub id: ImportId,
  pub span: TextRange,
  pub kind: ImportKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ImportKind {
  Es(ImportEs),
  ImportEquals(ImportEquals),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImportEs {
  pub specifier: ModuleSpecifier,
  pub is_type_only: bool,
  pub default: Option<ImportBinding>,
  pub namespace: Option<ImportBinding>,
  pub named: Vec<ImportNamed>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImportBinding {
  pub local: NameId,
  pub local_def: Option<DefId>,
  pub span: TextRange,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImportNamed {
  pub id: ImportSpecifierId,
  pub imported: NameId,
  pub local: NameId,
  pub local_def: Option<DefId>,
  pub is_type_only: bool,
  pub span: TextRange,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImportEquals {
  pub local: ImportBinding,
  pub target: ImportEqualsTarget,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ImportEqualsTarget {
  Module(ModuleSpecifier),
  Path(Vec<NameId>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Export {
  pub id: ExportId,
  pub span: TextRange,
  pub kind: ExportKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExportKind {
  Named(ExportNamed),
  ExportAll(ExportAll),
  Default(ExportDefault),
  Assignment(ExportAssignment),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExportNamed {
  pub source: Option<ModuleSpecifier>,
  pub specifiers: Vec<ExportSpecifier>,
  pub is_type_only: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExportSpecifier {
  pub id: ExportSpecifierId,
  pub local: NameId,
  pub exported: NameId,
  pub local_def: Option<DefId>,
  pub is_type_only: bool,
  pub span: TextRange,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExportAll {
  pub source: ModuleSpecifier,
  pub alias: Option<ExportAlias>,
  pub is_type_only: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExportAlias {
  pub exported: NameId,
  pub span: TextRange,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExportDefault {
  pub value: ExportDefaultValue,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExportDefaultValue {
  Expr {
    expr: ExprId,
    body: BodyId,
  },
  Class {
    def: DefId,
    body: BodyId,
    name: Option<NameId>,
  },
  Function {
    def: DefId,
    body: BodyId,
    name: Option<NameId>,
  },
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExportAssignment {
  pub expr: ExprId,
  pub body: BodyId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DefData {
  pub id: DefId,
  pub name: NameId,
  pub path: DefPath,
  pub parent: Option<DefId>,
  pub span: TextRange,
  pub is_static: bool,
  pub is_ambient: bool,
  pub in_global: bool,
  pub is_exported: bool,
  pub is_default_export: bool,
  pub body: Option<BodyId>,
  pub type_info: Option<DefTypeInfo>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LowerResult {
  pub hir: Arc<HirFile>,
  pub defs: Vec<DefData>,
  pub bodies: Vec<Arc<Body>>,
  pub types: TypeArenas,
  pub names: Arc<NameInterner>,
  pub def_index: BTreeMap<DefId, usize>,
  pub body_index: BTreeMap<BodyId, usize>,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct TypeArenas {
  pub type_exprs: Vec<TypeExpr>,
  pub type_members: Vec<TypeMember>,
  pub type_params: Vec<TypeParam>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeExpr {
  pub span: TextRange,
  pub kind: TypeExprKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeExprKind {
  Any,
  Unknown,
  Never,
  Void,
  String,
  Number,
  Boolean,
  BigInt,
  Symbol,
  UniqueSymbol,
  Object,
  Null,
  Undefined,
  This,
  Literal(TypeLiteral),
  TypeRef(TypeRef),
  Array(TypeArray),
  Tuple(TypeTuple),
  Union(Vec<TypeExprId>),
  Intersection(Vec<TypeExprId>),
  Function(TypeFunction),
  Constructor(TypeFunction),
  TypeLiteral(TypeLiteralType),
  Parenthesized(TypeExprId),
  TypeQuery(TypeName),
  KeyOf(TypeExprId),
  IndexedAccess {
    object_type: TypeExprId,
    index_type: TypeExprId,
  },
  Conditional(ConditionalType),
  Infer(TypeParamId),
  Mapped(TypeMapped),
  TemplateLiteral(TypeTemplateLiteral),
  TypePredicate(TypePredicate),
  Import(TypeImport),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeRef {
  pub name: TypeName,
  pub type_args: Vec<TypeExprId>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeName {
  Ident(NameId),
  Qualified(Vec<NameId>),
  Import(TypeImportName),
  ImportExpr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeImportName {
  pub module: Option<String>,
  pub qualifier: Option<Vec<NameId>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeLiteral {
  String(String),
  Number(String),
  BigInt(String),
  Boolean(bool),
  Null,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeArray {
  pub readonly: bool,
  pub element: TypeExprId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeTuple {
  pub readonly: bool,
  pub elements: Vec<TypeTupleElement>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeTupleElement {
  pub label: Option<NameId>,
  pub optional: bool,
  pub rest: bool,
  pub ty: TypeExprId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeFunction {
  pub type_params: Vec<TypeParamId>,
  pub params: Vec<TypeFnParam>,
  pub ret: TypeExprId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeFnParam {
  pub name: Option<NameId>,
  pub ty: TypeExprId,
  pub optional: bool,
  pub rest: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeLiteralType {
  pub members: Vec<TypeMemberId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeMember {
  pub span: TextRange,
  pub kind: TypeMemberKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeMemberKind {
  Property(TypePropertySignature),
  Method(TypeMethodSignature),
  Constructor(TypeSignature),
  CallSignature(TypeSignature),
  IndexSignature(TypeIndexSignature),
  Getter(TypeGetterSignature),
  Setter(TypeSetterSignature),
  Mapped(TypeMapped),
}

#[derive(Debug, Clone, PartialEq)]
pub enum PropertyName {
  Ident(NameId),
  String(String),
  Number(String),
  Computed,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypePropertySignature {
  pub readonly: bool,
  pub optional: bool,
  pub name: PropertyName,
  pub type_annotation: Option<TypeExprId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeMethodSignature {
  pub optional: bool,
  pub name: PropertyName,
  pub type_params: Vec<TypeParamId>,
  pub params: Vec<TypeFnParam>,
  pub return_type: Option<TypeExprId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeSignature {
  pub type_params: Vec<TypeParamId>,
  pub params: Vec<TypeFnParam>,
  pub return_type: Option<TypeExprId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeIndexSignature {
  pub readonly: bool,
  pub parameter_name: NameId,
  pub parameter_type: TypeExprId,
  pub type_annotation: TypeExprId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeGetterSignature {
  pub name: PropertyName,
  pub return_type: Option<TypeExprId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeSetterSignature {
  pub name: PropertyName,
  pub parameter: TypeFnParam,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClassMemberAccessibility {
  Public,
  Protected,
  Private,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClassMemberSig {
  pub span: TextRange,
  pub static_: bool,
  pub accessibility: Option<ClassMemberAccessibility>,
  pub readonly: bool,
  pub optional: bool,
  pub kind: ClassMemberSigKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ClassMemberSigKind {
  Field {
    name: PropertyName,
    type_annotation: Option<TypeExprId>,
  },
  Method {
    name: PropertyName,
    signature: TypeSignature,
  },
  Getter {
    name: PropertyName,
    return_type: Option<TypeExprId>,
  },
  Setter {
    name: PropertyName,
    parameter: TypeFnParam,
  },
  Constructor(TypeSignature),
  CallSignature(TypeSignature),
  IndexSignature(TypeIndexSignature),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnumMemberValue {
  Number,
  String,
  Computed,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumMemberInfo {
  pub name: NameId,
  pub span: TextRange,
  pub value: EnumMemberValue,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeMapped {
  pub type_param: TypeParamId,
  pub constraint: TypeExprId,
  pub name_type: Option<TypeExprId>,
  pub value_type: TypeExprId,
  pub readonly: Option<TypeMappedModifier>,
  pub optional: Option<TypeMappedModifier>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TypeMappedModifier {
  Plus,
  Minus,
  None,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeTemplateLiteral {
  pub head: String,
  pub spans: Vec<TypeTemplateLiteralSpan>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeTemplateLiteralSpan {
  pub type_expr: TypeExprId,
  pub literal: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConditionalType {
  pub check_type: TypeExprId,
  pub extends_type: TypeExprId,
  pub true_type: TypeExprId,
  pub false_type: TypeExprId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypePredicate {
  pub asserts: bool,
  pub parameter: NameId,
  pub type_annotation: Option<TypeExprId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeImport {
  pub module: String,
  pub qualifier: Option<TypeName>,
  pub type_args: Vec<TypeExprId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeParam {
  pub span: TextRange,
  pub name: NameId,
  pub constraint: Option<TypeExprId>,
  pub default: Option<TypeExprId>,
  pub variance: Option<TypeVariance>,
  pub const_: bool,
  pub is_infer: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeVariance {
  In,
  Out,
  InOut,
}

#[derive(Debug, Clone, PartialEq)]
pub enum DefTypeInfo {
  TypeAlias {
    type_expr: TypeExprId,
    type_params: Vec<TypeParamId>,
  },
  Interface {
    type_params: Vec<TypeParamId>,
    extends: Vec<TypeExprId>,
    members: Vec<TypeMemberId>,
  },
  Class {
    type_params: Vec<TypeParamId>,
    extends: Option<TypeExprId>,
    implements: Vec<TypeExprId>,
    members: Vec<ClassMemberSig>,
  },
  Enum {
    members: Vec<EnumMemberInfo>,
  },
  Namespace {
    members: Vec<DefId>,
  },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Body {
  pub owner: DefId,
  pub kind: BodyKind,
  pub exprs: Vec<Expr>,
  pub stmts: Vec<Stmt>,
  pub pats: Vec<Pat>,
  /// Statements that form the body in source order. Nested statements are
  /// referenced by [`StmtKind`] variants.
  pub root_stmts: Vec<StmtId>,
  /// Metadata for function-like bodies. Only populated when `kind` is
  /// [`BodyKind::Function`].
  pub function: Option<FunctionData>,
  /// Reserved for the checker; filled in by later phases.
  pub expr_types: Option<Vec<()>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum BodyKind {
  /// Root body for a file or module.
  TopLevel,
  /// Executable body of a function-like item (functions, methods, accessors).
  Function,
  /// Body attached to a class definition. Root statements correspond to static
  /// initialization blocks.
  Class,
  /// Body synthesized for initializer expressions (e.g. `const x = 1;`).
  Initializer,
  /// Catch-all for unsupported or unknown body sources.
  Unknown,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
  pub pat: PatId,
  pub default: Option<ExprId>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum FunctionBody {
  Block(Vec<StmtId>),
  Expr(ExprId),
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionData {
  pub params: Vec<Param>,
  pub async_: bool,
  pub generator: bool,
  pub is_arrow: bool,
  pub body: FunctionBody,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
  pub span: TextRange,
  pub kind: ExprKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
  Missing,
  Ident(NameId),
  This,
  Super,
  Literal(Literal),
  Unary {
    op: UnaryOp,
    expr: ExprId,
  },
  Update {
    op: UpdateOp,
    expr: ExprId,
    prefix: bool,
  },
  Binary {
    op: BinaryOp,
    left: ExprId,
    right: ExprId,
  },
  Assignment {
    op: AssignOp,
    target: PatId,
    value: ExprId,
  },
  Call(CallExpr),
  Member(MemberExpr),
  Conditional {
    test: ExprId,
    consequent: ExprId,
    alternate: ExprId,
  },
  Array(ArrayLiteral),
  Object(ObjectLiteral),
  FunctionExpr {
    def: DefId,
    body: BodyId,
    name: Option<NameId>,
    is_arrow: bool,
  },
  ClassExpr {
    def: DefId,
    body: BodyId,
    name: Option<NameId>,
  },
  Template(TemplateLiteral),
  TaggedTemplate {
    tag: ExprId,
    template: TemplateLiteral,
  },
  Await {
    expr: ExprId,
  },
  Yield {
    expr: Option<ExprId>,
    delegate: bool,
  },
  TypeAssertion {
    expr: ExprId,
  },
  NonNull {
    expr: ExprId,
  },
  Satisfies {
    expr: ExprId,
  },
  ImportCall {
    argument: ExprId,
    attributes: Option<ExprId>,
  },
  ImportMeta,
  NewTarget,
  Jsx(JsxElement),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
  Number(String),
  String(String),
  Boolean(bool),
  Null,
  Undefined,
  BigInt(String),
  Regex(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
  Not,
  BitNot,
  Plus,
  Minus,
  Typeof,
  Void,
  Delete,
  Await,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UpdateOp {
  Increment,
  Decrement,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
  Add,
  Subtract,
  Multiply,
  Divide,
  Remainder,
  Exponent,
  ShiftLeft,
  ShiftRight,
  ShiftRightUnsigned,
  BitOr,
  BitAnd,
  BitXor,
  LogicalOr,
  LogicalAnd,
  NullishCoalescing,
  Equality,
  Inequality,
  StrictEquality,
  StrictInequality,
  LessThan,
  LessEqual,
  GreaterThan,
  GreaterEqual,
  In,
  Instanceof,
  Comma,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
  Assign,
  AddAssign,
  SubAssign,
  MulAssign,
  DivAssign,
  RemAssign,
  ShiftLeftAssign,
  ShiftRightAssign,
  ShiftRightUnsignedAssign,
  BitOrAssign,
  BitAndAssign,
  BitXorAssign,
  LogicalAndAssign,
  LogicalOrAssign,
  NullishAssign,
  ExponentAssign,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallArg {
  pub expr: ExprId,
  pub spread: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExpr {
  pub callee: ExprId,
  pub args: Vec<CallArg>,
  pub optional: bool,
  pub is_new: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ObjectKey {
  Ident(NameId),
  String(String),
  Number(String),
  Computed(ExprId),
}

#[derive(Debug, Clone, PartialEq)]
pub struct MemberExpr {
  pub object: ExprId,
  pub property: ObjectKey,
  pub optional: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArrayLiteral {
  pub elements: Vec<ArrayElement>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ArrayElement {
  Expr(ExprId),
  Spread(ExprId),
  Empty,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ObjectLiteral {
  pub properties: Vec<ObjectProperty>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ObjectProperty {
  KeyValue {
    key: ObjectKey,
    value: ExprId,
    method: bool,
    shorthand: bool,
  },
  Getter {
    key: ObjectKey,
    body: BodyId,
  },
  Setter {
    key: ObjectKey,
    body: BodyId,
  },
  Spread(ExprId),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TemplateLiteral {
  pub head: String,
  pub spans: Vec<TemplateLiteralSpan>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TemplateLiteralSpan {
  pub expr: ExprId,
  pub literal: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pat {
  pub span: TextRange,
  pub kind: PatKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PatKind {
  Ident(NameId),
  Array(ArrayPat),
  Object(ObjectPat),
  Rest(Box<PatId>),
  Assign {
    target: PatId,
    default_value: ExprId,
  },
  AssignTarget(ExprId),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArrayPat {
  pub elements: Vec<Option<ArrayPatElement>>,
  pub rest: Option<PatId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArrayPatElement {
  pub pat: PatId,
  pub default_value: Option<ExprId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ObjectPat {
  pub props: Vec<ObjectPatProp>,
  pub rest: Option<PatId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ObjectPatProp {
  pub key: ObjectKey,
  pub value: PatId,
  pub shorthand: bool,
  pub default_value: Option<ExprId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Stmt {
  pub span: TextRange,
  pub kind: StmtKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StmtKind {
  Expr(ExprId),
  Decl(DefId),
  Return(Option<ExprId>),
  Block(Vec<StmtId>),
  If {
    test: ExprId,
    consequent: StmtId,
    alternate: Option<StmtId>,
  },
  While {
    test: ExprId,
    body: StmtId,
  },
  DoWhile {
    test: ExprId,
    body: StmtId,
  },
  For {
    init: Option<ForInit>,
    test: Option<ExprId>,
    update: Option<ExprId>,
    body: StmtId,
  },
  ForIn {
    left: ForHead,
    right: ExprId,
    body: StmtId,
    is_for_of: bool,
    await_: bool,
  },
  Switch {
    discriminant: ExprId,
    cases: Vec<SwitchCase>,
  },
  Try {
    block: StmtId,
    catch: Option<CatchClause>,
    finally_block: Option<StmtId>,
  },
  Throw(ExprId),
  Break(Option<NameId>),
  Continue(Option<NameId>),
  Var(VarDecl),
  Labeled {
    label: NameId,
    body: StmtId,
  },
  With {
    object: ExprId,
    body: StmtId,
  },
  Empty,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarDecl {
  pub kind: VarDeclKind,
  pub declarators: Vec<VarDeclarator>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarDeclKind {
  Var,
  Let,
  Const,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarDeclarator {
  pub pat: PatId,
  pub init: Option<ExprId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CatchClause {
  pub param: Option<PatId>,
  pub body: StmtId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SwitchCase {
  pub test: Option<ExprId>,
  pub consequent: Vec<StmtId>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ForInit {
  Expr(ExprId),
  Var(VarDecl),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ForHead {
  Pat(PatId),
  Var(VarDecl),
}

#[derive(Debug, Clone, PartialEq)]
pub struct JsxElement {
  pub kind: JsxElementKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum JsxElementKind {
  Element(NameId),
  Member(Vec<NameId>),
  Fragment,
  Text(String),
  Expr(ExprId),
  Spread(ExprId),
  Name(NameId),
}

impl HirFile {
  pub fn new(
    file: FileId,
    file_kind: FileKind,
    root_body: BodyId,
    items: Vec<DefId>,
    bodies: Vec<BodyId>,
    def_paths: BTreeMap<DefPath, DefId>,
    imports: Vec<Import>,
    exports: Vec<Export>,
    span_map: SpanMap,
  ) -> Self {
    Self {
      file,
      file_kind,
      root_body,
      items,
      bodies,
      def_paths,
      imports,
      exports,
      span_map,
    }
  }
}

impl LowerResult {
  pub fn def(&self, id: DefId) -> Option<&DefData> {
    self.def_index.get(&id).and_then(|idx| self.defs.get(*idx))
  }

  pub fn body(&self, id: BodyId) -> Option<&Body> {
    self
      .body_index
      .get(&id)
      .and_then(|idx| self.bodies.get(*idx))
      .map(Arc::as_ref)
  }

  pub fn def_id_for_path(&self, path: &DefPath) -> Option<DefId> {
    self.hir.def_paths.get(path).copied()
  }

  pub fn root_body(&self) -> BodyId {
    self.hir.root_body
  }
}
