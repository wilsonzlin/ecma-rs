use derive_more::derive::From;
use derive_visitor::{Drive, DriveMut};
use serde::{Serialize};

use crate::token::TT;

use super::{expr::{Decorator, Expr, IdExpr}, func::Func, node::Node, stmt::decl::Accessibility, type_expr::TypeExpr};

/// Index signature in class: [key: string]: Type
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ClassIndexSignature {
  #[drive(skip)]
  pub parameter_name: String,
  pub parameter_type: Node<TypeExpr>,
  pub type_annotation: Node<TypeExpr>,
}

/// This is a node as the key may not the same as source[node.loc], due to decoding/normalization.
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ClassOrObjMemberDirectKey {
  #[drive(skip)]
  pub key: String,
  // The original token type is stored here to determine if it was a valid keyword/identifier, useful for shorthands.
  #[drive(skip)]
  pub tt: TT,
}

// WARNING: This enum must exist, and the two variants cannot be merged by representing Direct with an IdentifierExpr, as it's not a usage of a variable.
#[derive(Debug, Drive, DriveMut, Serialize)]
pub enum ClassOrObjKey {
  // Identifier, keyword, string, or number.
  // NOTE: This isn't used by ObjectMemberType::Shorthand.
  Direct(Node<ClassOrObjMemberDirectKey>),
  Computed(Node<Expr>),
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ClassOrObjGetter {
  pub func: Node<Func>, // `params` is empty.
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ClassOrObjMethod {
  pub func: Node<Func>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ClassOrObjSetter {
  pub func: Node<Func>, // `params` contains exactly one ParamDecl with no `default_value` or `rest`.
}

#[derive(Debug, Drive, DriveMut, From, Serialize)]
pub enum ClassOrObjVal {
  Getter(Node<ClassOrObjGetter>),
  Setter(Node<ClassOrObjSetter>),
  Method(Node<ClassOrObjMethod>),
  // Must be Some if object, as shorthands are covered by ObjectMemberType::Shorthand (and are initialised).
  // Unlike the others, this is not its own struct as if None, there is no source range.
  Prop(Option<Node<Expr>>),
  // TypeScript: index signature in classes
  IndexSignature(Node<ClassIndexSignature>),
}

#[derive(Debug, Drive, DriveMut, Serialize)]
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

#[derive(Debug, Drive, DriveMut, Serialize)]
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
#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ObjMember {
  pub typ: ObjMemberType,
}
