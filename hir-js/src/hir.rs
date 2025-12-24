use crate::ids::BodyId;
use crate::ids::DefId;
use crate::ids::DefPath;
use crate::ids::ExprId;
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
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq)]
pub struct HirFile {
  pub file: FileId,
  pub items: Vec<DefId>,
  pub bodies: Vec<BodyId>,
  pub span_map: SpanMap,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DefData {
  pub id: DefId,
  pub path: DefPath,
  pub span: TextRange,
  pub body: Option<BodyId>,
  pub type_info: Option<DefTypeInfo>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LowerResult {
  pub hir: Arc<HirFile>,
  pub defs: Vec<DefData>,
  pub bodies: Vec<Arc<Body>>, // BodyId indexes into this vec.
  pub types: TypeArenas,
  pub names: Arc<NameInterner>,
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

#[derive(Debug, Clone, PartialEq)]
pub struct TypeMapped {
  pub type_param: TypeParamId,
  pub constraint: TypeExprId,
  pub name_type: Option<TypeExprId>,
  pub value_type: TypeExprId,
  pub readonly: TypeMappedModifier,
  pub optional: TypeMappedModifier,
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
}

#[derive(Debug, Clone, PartialEq)]
pub struct Body {
  pub owner: DefId,
  pub kind: BodyKind,
  pub exprs: Vec<Expr>,
  pub stmts: Vec<Stmt>,
  pub pats: Vec<Pat>,
  /// Reserved for the checker; filled in by later phases.
  pub expr_types: Option<Vec<()>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BodyKind {
  TopLevel,
  Function,
  Class,
  Initializer,
  Unknown,
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
  Literal,
  Binary {
    left: ExprId,
    right: ExprId,
  },
  Call {
    callee: ExprId,
    args: Vec<ExprId>,
    optional: bool,
  },
  Member {
    object: ExprId,
    property: NameId,
    optional: bool,
  },
  Conditional {
    test: ExprId,
    consequent: ExprId,
    alternate: ExprId,
  },
  Assignment {
    target: PatId,
    value: ExprId,
  },
  FunctionExpr {
    body: BodyId,
  },
  ClassExpr {
    body: BodyId,
    name: Option<NameId>,
  },
  This,
  Super,
  Await {
    expr: ExprId,
  },
  Object,
  Array,
  Other,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pat {
  pub span: TextRange,
  pub kind: PatKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PatKind {
  Ident(NameId),
  Rest(Box<PatId>),
  Destructure(Vec<PatId>),
  AssignTarget(ExprId),
  Unknown,
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
  Empty,
  Other,
}

impl HirFile {
  pub fn new(file: FileId, items: Vec<DefId>, bodies: Vec<BodyId>, span_map: SpanMap) -> Self {
    Self {
      file,
      items,
      bodies,
      span_map,
    }
  }
}
