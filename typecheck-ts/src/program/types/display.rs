use super::*;

/// Helper returned from [`Program::display_type`].
///
/// When the optional `serde` feature is enabled this serializes to the rendered
/// string form for easy inclusion in JSON outputs.
#[derive(Clone)]
pub struct TypeDisplay {
  pub(in super::super) store: Arc<tti::TypeStore>,
  pub(in super::super) ty: tti::TypeId,
  pub(in super::super) resolver: Option<Arc<dyn Fn(tti::DefId) -> Option<String> + Send + Sync>>,
}

/// Structured explanation for why one type is not assignable to another.
///
/// This is powered by the `types-ts-interned` relation engine and is intended
/// for diagnostics, debugging, and tooling (e.g. CLI output).
pub type ExplainTree = tti::ReasonNode;

impl std::fmt::Display for TypeDisplay {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let display = if let Some(resolver) = self.resolver.as_ref() {
      tti::TypeDisplay::new(&self.store, self.ty).with_ref_resolver(Arc::clone(resolver))
    } else {
      tti::TypeDisplay::new(&self.store, self.ty)
    };
    display.fmt(f)
  }
}

#[cfg(feature = "serde")]
impl serde::Serialize for TypeDisplay {
  fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(&self.to_string())
  }
}
