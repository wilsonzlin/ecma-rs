//! Association helpers for data attached to `parse-js` AST nodes.
//!
//! This module is split by language mode to avoid collisions between JS-only
//! and TS-only identifiers. Downstream users should pick the helpers that
//! match the binder they ran (`assoc::js` for [`crate::js`], `assoc::ts` for
//! [`crate::ts`]).

pub mod js;
pub mod ts;
