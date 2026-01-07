#![deny(missing_debug_implementations)]

//! Deterministic, interned TypeScript type representation.
//!
//! [`TypeStore`] interns canonicalized [`TypeKind`] values into stable IDs
//! (`TypeId`, `ShapeId`, `ObjectId`, `SignatureId`, `NameId`, ...). IDs are
//! derived from stable hashes of canonical data, making them deterministic and
//! thread-scheduling independent **assuming no hash collisions**.
//!
//! ## Hash collisions and determinism
//!
//! Hash collisions are astronomically unlikely with the default 128-bit
//! fingerprints, but the store still has a salt-based rehashing fallback for
//! robustness. This fallback is deterministic for a *fixed insertion sequence*,
//! however it does **not** define a canonical, order-independent ID assignment
//! under collisions: the first value inserted keeps the lowest-salt ID, because
//! already-returned IDs must never change.
//!
//! Downstream code that wants strict schedule-independence even in the presence
//! of collisions can enable the `strict-determinism` feature to treat collisions
//! as an internal error.
//!
//! # Example
//! ```
//! use types_ts_interned::{TypeDisplay, TypeStore};
//!
//! let store = TypeStore::new();
//! let primitives = store.primitive_ids();
//! assert_eq!(
//!   TypeDisplay::new(store.as_ref(), primitives.number).to_string(),
//!   "number"
//! );
//! ```

mod cache;
mod display;
mod eval;
#[cfg(feature = "fuzzing")]
mod fuzz;
mod ids;
mod kind;
mod options;
mod relate;
mod shape;
mod signature;
mod store;

pub use cache::{CacheConfig, CacheStats, ShardedCache};
pub use display::TypeDisplay;
pub use eval::EvaluatorCacheStats;
pub use eval::EvaluatorCaches;
pub use eval::EvaluatorLimits;
pub use eval::ExpandedType;
pub use eval::TypeEvaluator;
pub use eval::TypeExpander;
#[cfg(feature = "fuzzing")]
pub use fuzz::fuzz_type_graph;
pub use ids::DefId;
pub use ids::NameId;
pub use ids::ObjectId;
pub use ids::ShapeId;
pub use ids::SignatureId;
pub use ids::TypeId;
pub use ids::TypeParamId;
pub use kind::IntrinsicKind;
pub use kind::MappedModifier;
pub use kind::MappedType;
pub use kind::TemplateChunk;
pub use kind::TemplateLiteralType;
pub use kind::TupleElem;
pub use kind::TypeKind;
pub use options::TypeOptions;
pub use relate::ReasonNode;
pub use relate::RelateCtx;
pub use relate::RelateHooks;
pub use relate::RelateTypeExpander;
pub use relate::RelationCache;
pub use relate::RelationKind;
pub use relate::RelationLimits;
pub use relate::RelationMode;
pub use relate::RelationResult;
pub use shape::Accessibility;
pub use shape::Indexer;
pub use shape::ObjectType;
pub use shape::PropData;
pub use shape::PropKey;
pub use shape::Property;
pub use shape::Shape;
pub use signature::Param;
pub use signature::Signature;
pub use signature::TypeParamDecl;
pub use signature::TypeParamVariance;
pub use store::PrimitiveIds;
pub use store::TypeStore;
pub use store::TypeStoreSnapshot;
