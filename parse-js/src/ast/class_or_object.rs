use super::expr::Decorator;
use super::expr::Expr;
use super::expr::IdExpr;
use super::func::Func;
use super::node::Node;
use super::stmt::decl::Accessibility;
use super::type_expr::TypeExpr;
use crate::token::TT;
use derive_more::derive::From;
use derive_visitor::Drive;
use derive_visitor::DriveMut;

/// Index signature in class: [key: string]: Type
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ClassIndexSignature {
  #[drive(skip)]
  pub parameter_name: String,
  pub parameter_type: Node<TypeExpr>,
  pub type_annotation: Node<TypeExpr>,
}

/// This is a node as the key may not the same as source[node.loc], due to decoding/normalization.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ClassOrObjMemberDirectKey {
  #[drive(skip)]
  pub key: String,
  // The original token type is stored here to determine if it was a valid keyword/identifier, useful for shorthands.
  #[drive(skip)]
  pub tt: TT,
}

// WARNING: This enum must exist, and the two variants cannot be merged by representing Direct with an IdentifierExpr, as it's not a usage of a variable.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub enum ClassOrObjKey {
  // Identifier, keyword, string, or number.
  // NOTE: This isn't used by ObjectMemberType::Shorthand.
  Direct(Node<ClassOrObjMemberDirectKey>),
  Computed(Node<Expr>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ClassOrObjGetter {
  pub func: Node<Func>, // `params` is empty.
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ClassOrObjMethod {
  pub func: Node<Func>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ClassOrObjSetter {
  pub func: Node<Func>, // `params` contains exactly one ParamDecl with no `default_value` or `rest`.
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ClassStaticBlock {
  pub body: Vec<Node<super::stmt::Stmt>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut, From)]
pub enum ClassOrObjVal {
  Getter(Node<ClassOrObjGetter>),
  Setter(Node<ClassOrObjSetter>),
  Method(Node<ClassOrObjMethod>),
  // Must be Some if object, as shorthands are covered by ObjectMemberType::Shorthand (and are initialised).
  // Unlike the others, this is not its own struct as if None, there is no source range.
  Prop(Option<Node<Expr>>),
  // TypeScript: index signature in classes
  IndexSignature(Node<ClassIndexSignature>),
  // Static initialization block
  StaticBlock(Node<ClassStaticBlock>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub enum ObjMemberType {
  Valued {
    key: ClassOrObjKey,
    val: ClassOrObjVal,
  },
  Shorthand {
    id: Node<IdExpr>,
  },
  Rest {
    val: Node<Expr>,
  },
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ClassMember {
  pub decorators: Vec<Node<Decorator>>,
  pub key: ClassOrObjKey,
  #[drive(skip)]
  pub static_: bool,
  #[drive(skip)]
  pub abstract_: bool,
  #[drive(skip)]
  pub readonly: bool,
  #[drive(skip)]
  pub accessor: bool,
  #[drive(skip)]
  pub optional: bool,
  #[drive(skip)]
  pub override_: bool,
  #[drive(skip)]
  pub definite_assignment: bool, // TypeScript: prop!: Type
  pub accessibility: Option<Accessibility>,
  pub type_annotation: Option<Node<TypeExpr>>, // For properties only
  pub val: ClassOrObjVal,
}

// This is a node instead of an enum so that we can replace it when minifying e.g. expanding shorthand to `key: value`.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct ObjMember {
  pub typ: ObjMemberType,
}
