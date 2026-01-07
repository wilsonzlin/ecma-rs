use super::expr::Expr;
use super::expr::ImportExpr;
use super::node::Node;
use derive_visitor::Drive;
use derive_visitor::DriveMut;

/// Main type expression enum covering all TypeScript type constructs
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
#[cfg_attr(feature = "serde", serde(tag = "$t"))]
pub enum TypeExpr {
  // Primitive types
  Any(Node<TypeAny>),
  Unknown(Node<TypeUnknown>),
  Never(Node<TypeNever>),
  Void(Node<TypeVoid>),
  String(Node<TypeString>),
  Number(Node<TypeNumber>),
  Boolean(Node<TypeBoolean>),
  BigInt(Node<TypeBigInt>),
  Symbol(Node<TypeSymbol>),
  UniqueSymbol(Node<TypeUniqueSymbol>),
  Object(Node<TypeObject>),
  Null(Node<TypeNull>),
  Undefined(Node<TypeUndefined>),
  Intrinsic(Node<TypeIntrinsic>),

  // Reference and complex types
  TypeReference(Node<TypeReference>),
  LiteralType(Node<TypeLiteral>),
  ArrayType(Node<TypeArray>),
  TupleType(Node<TypeTuple>),
  UnionType(Node<TypeUnion>),
  IntersectionType(Node<TypeIntersection>),
  FunctionType(Node<TypeFunction>),
  ConstructorType(Node<TypeConstructor>),
  ObjectType(Node<TypeObjectLiteral>),
  ParenthesizedType(Node<TypeParenthesized>),

  // Type operators
  TypeQuery(Node<TypeQuery>),
  KeyOfType(Node<TypeKeyOf>),
  IndexedAccessType(Node<TypeIndexedAccess>),
  ConditionalType(Node<TypeConditional>),
  InferType(Node<TypeInfer>),
  MappedType(Node<TypeMapped>),
  TemplateLiteralType(Node<TypeTemplateLiteral>),

  // Type predicates
  TypePredicate(Node<TypePredicate>),

  // Special
  ThisType(Node<TypeThis>),
  ImportType(Node<TypeImport>),
}

/// Primitive type: any
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeAny {}

/// Primitive type: unknown
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeUnknown {}

/// Primitive type: never
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeNever {}

/// Primitive type: void
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeVoid {}

/// Primitive type: string
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeString {}

/// Primitive type: number
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeNumber {}

/// Primitive type: boolean
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeBoolean {}

/// Primitive type: bigint
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeBigInt {}

/// Primitive type: symbol
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeSymbol {}

/// Primitive type: unique symbol
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeUniqueSymbol {}

/// Primitive type: object
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeObject {}

/// Primitive type: null
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeNull {}

/// Primitive type: undefined
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeUndefined {}

/// Special type: intrinsic
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeIntrinsic {}

/// Type reference: Foo, Foo<T>, A.B.C<T, U>
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeReference {
  pub name: TypeEntityName,
  pub type_arguments: Option<Vec<Node<TypeExpr>>>,
}

/// Entity name in type reference (can be qualified)
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
#[cfg_attr(feature = "serde", serde(tag = "$t", content = "v"))]
pub enum TypeEntityName {
  Identifier(#[drive(skip)] String),
  Qualified(Box<TypeQualifiedName>),
  Import(Node<ImportExpr>),
}

/// Qualified name: A.B.C
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeQualifiedName {
  pub left: TypeEntityName,
  #[drive(skip)]
  pub right: String,
}

/// Literal type: "foo", 42, true, false, etc.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
#[cfg_attr(feature = "serde", serde(tag = "$t", content = "v"))]
pub enum TypeLiteral {
  String(#[drive(skip)] String),
  Number(#[drive(skip)] String),
  BigInt(#[drive(skip)] String),
  Boolean(#[drive(skip)] bool),
  Null,
}

/// Array type: T[] or readonly T[]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeArray {
  #[drive(skip)]
  pub readonly: bool,
  pub element_type: Box<Node<TypeExpr>>,
}

/// Tuple type: [T, U], [string, ...number[]] or readonly [T, U]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeTuple {
  #[drive(skip)]
  pub readonly: bool,
  pub elements: Vec<Node<TypeTupleElement>>,
}

/// Tuple element with optional name and modifiers
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeTupleElement {
  #[drive(skip)]
  pub label: Option<String>,
  #[drive(skip)]
  pub optional: bool,
  #[drive(skip)]
  pub rest: bool,
  pub type_expr: Node<TypeExpr>,
}

/// Union type: T | U | V
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeUnion {
  pub types: Vec<Node<TypeExpr>>,
}

/// Intersection type: T & U & V
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeIntersection {
  pub types: Vec<Node<TypeExpr>>,
}

/// Function type: (x: T, y: U) => R
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeFunction {
  pub type_parameters: Option<Vec<Node<TypeParameter>>>,
  pub parameters: Vec<Node<TypeFunctionParameter>>,
  pub return_type: Box<Node<TypeExpr>>,
}

/// Constructor type: new (x: T) => R
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeConstructor {
  pub type_parameters: Option<Vec<Node<TypeParameter>>>,
  pub parameters: Vec<Node<TypeFunctionParameter>>,
  pub return_type: Box<Node<TypeExpr>>,
}

/// Function type parameter
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeFunctionParameter {
  #[drive(skip)]
  pub name: Option<String>,
  #[drive(skip)]
  pub optional: bool,
  #[drive(skip)]
  pub rest: bool,
  pub type_expr: Node<TypeExpr>,
}

/// Variance annotation for type parameters
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Copy, Clone)]
pub enum Variance {
  In,    // contravariant
  Out,   // covariant
  InOut, // invariant (both in and out)
}

/// Type parameter: T, T extends U, T = DefaultType, in T, out T, in out T, const T
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeParameter {
  #[drive(skip)]
  pub const_: bool, // TypeScript: const type parameter
  #[drive(skip)]
  pub variance: Option<Variance>,
  #[drive(skip)]
  pub name: String,
  pub constraint: Option<Box<Node<TypeExpr>>>,
  pub default: Option<Box<Node<TypeExpr>>>,
}

/// Object type literal: { x: T; y: U; }
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeObjectLiteral {
  pub members: Vec<Node<TypeMember>>,
}

/// Type member in object type or interface
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
#[cfg_attr(feature = "serde", serde(tag = "$t"))]
pub enum TypeMember {
  Property(Node<TypePropertySignature>),
  Method(Node<TypeMethodSignature>),
  Constructor(Node<TypeConstructSignature>),
  CallSignature(Node<TypeCallSignature>),
  IndexSignature(Node<TypeIndexSignature>),
  GetAccessor(Node<TypeGetAccessor>),
  SetAccessor(Node<TypeSetAccessor>),
  MappedProperty(Node<TypeMapped>),
}

/// Property signature: x: T, readonly x?: T
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypePropertySignature {
  #[drive(skip)]
  pub readonly: bool,
  #[drive(skip)]
  pub optional: bool,
  pub key: TypePropertyKey,
  pub type_annotation: Option<Node<TypeExpr>>,
}

/// Method signature: foo(x: T): U
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeMethodSignature {
  #[drive(skip)]
  pub optional: bool,
  pub key: TypePropertyKey,
  pub type_parameters: Option<Vec<Node<TypeParameter>>>,
  pub parameters: Vec<Node<TypeFunctionParameter>>,
  pub return_type: Option<Node<TypeExpr>>,
}

/// Constructor signature: new (x: T): U
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeConstructSignature {
  pub type_parameters: Option<Vec<Node<TypeParameter>>>,
  pub parameters: Vec<Node<TypeFunctionParameter>>,
  pub return_type: Option<Node<TypeExpr>>,
}

/// Call signature: (x: T): U
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeCallSignature {
  pub type_parameters: Option<Vec<Node<TypeParameter>>>,
  pub parameters: Vec<Node<TypeFunctionParameter>>,
  pub return_type: Option<Node<TypeExpr>>,
}

/// Index signature: [key: string]: T, [key: number]: T
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeIndexSignature {
  #[drive(skip)]
  pub readonly: bool,
  #[drive(skip)]
  pub parameter_name: String,
  pub parameter_type: Node<TypeExpr>,
  pub type_annotation: Node<TypeExpr>,
}

/// Get accessor signature: get x(): T
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeGetAccessor {
  pub key: TypePropertyKey,
  pub return_type: Option<Node<TypeExpr>>,
}

/// Set accessor signature: set x(value: T)
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeSetAccessor {
  pub key: TypePropertyKey,
  pub parameter: Node<TypeFunctionParameter>,
}

/// Property key in type members
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
#[cfg_attr(feature = "serde", serde(tag = "$t", content = "v"))]
pub enum TypePropertyKey {
  Identifier(#[drive(skip)] String),
  String(#[drive(skip)] String),
  Number(#[drive(skip)] String),
  Computed(Box<Node<Expr>>),
}

/// Parenthesized type: (T)
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeParenthesized {
  pub type_expr: Box<Node<TypeExpr>>,
}

/// Type query: typeof x, typeof foo.bar
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeQuery {
  pub expr_name: TypeEntityName,
}

/// KeyOf type: keyof T
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeKeyOf {
  pub type_expr: Box<Node<TypeExpr>>,
}

/// Indexed access type: T[K], T["prop"]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeIndexedAccess {
  pub object_type: Box<Node<TypeExpr>>,
  pub index_type: Box<Node<TypeExpr>>,
}

/// Conditional type: T extends U ? X : Y
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeConditional {
  pub check_type: Box<Node<TypeExpr>>,
  pub extends_type: Box<Node<TypeExpr>>,
  pub true_type: Box<Node<TypeExpr>>,
  pub false_type: Box<Node<TypeExpr>>,
}

/// Infer type: infer R, infer R extends U
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeInfer {
  #[drive(skip)]
  pub type_parameter: String,
  pub constraint: Option<Box<Node<TypeExpr>>>, // TypeScript: infer T extends U
}

/// Mapped type: { [K in keyof T]: T[K] }, { readonly [K in T]?: U }, { [K in T as NewK]: U }
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeMapped {
  #[drive(skip)]
  pub readonly_modifier: Option<MappedTypeModifier>,
  #[drive(skip)]
  pub type_parameter: String,
  pub constraint: Box<Node<TypeExpr>>,
  pub name_type: Option<Box<Node<TypeExpr>>>, // as clause for key remapping
  #[drive(skip)]
  pub optional_modifier: Option<MappedTypeModifier>,
  pub type_expr: Box<Node<TypeExpr>>,
}

/// Mapped type modifier: +, -, or none
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MappedTypeModifier {
  Plus,
  Minus,
  None,
}

/// Template literal type: `foo${T}bar`
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeTemplateLiteral {
  #[drive(skip)]
  pub head: String,
  pub spans: Vec<Node<TypeTemplateLiteralSpan>>,
}

/// Template literal span
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeTemplateLiteralSpan {
  pub type_expr: Node<TypeExpr>,
  #[drive(skip)]
  pub literal: String,
}

/// Type predicate: x is T, asserts x, asserts x is T
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypePredicate {
  #[drive(skip)]
  pub asserts: bool,
  #[drive(skip)]
  pub parameter_name: String,
  pub type_annotation: Option<Box<Node<TypeExpr>>>,
}

/// This type: this
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeThis {}

/// Import type: import("module").Type
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TypeImport {
  #[drive(skip)]
  pub module_specifier: String,
  pub qualifier: Option<TypeEntityName>,
  pub type_arguments: Option<Vec<Node<TypeExpr>>>,
}
