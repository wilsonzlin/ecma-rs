#![deny(missing_debug_implementations)]

//! Deterministic, interned TypeScript type representation.
//!
//! [`TypeStore`] interns canonicalized [`TypeKind`] values into stable IDs
//! (`TypeId`, `ShapeId`, `ObjectId`, `SignatureId`, ...). IDs are derived from
//! stable hashes so insertion order (and parallelism) does not affect results.
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
