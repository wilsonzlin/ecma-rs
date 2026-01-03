//! Compatibility wrapper for the Node/TypeScript resolver.
//!
//! The canonical implementation lives in [`crate::resolve::ts_node`]. This
//! module preserves the original `resolve::node::*` paths used by downstream
//! hosts.

pub use super::ts_node::{RealFs, ResolveFs, ResolveOptions, Resolver, DEFAULT_EXTENSIONS};

/// Backwards-compatible alias for [`Resolver`].
pub type NodeResolver<F = RealFs> = Resolver<F>;
