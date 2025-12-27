use std::sync::Arc;

use crate::Host;

/// Immutable handle to the host used by query evaluation.
///
/// The host is treated as an external dependency: if resolution behaviour
/// changes, a new program/database instance must be created so cached query
/// results remain valid.
#[derive(Clone)]
pub(crate) struct HostStorage {
  host: Arc<dyn Host>,
}

impl HostStorage {
  pub(crate) fn new(host: Arc<dyn Host>) -> Self {
    Self { host }
  }

  pub(crate) fn host(&self) -> &Arc<dyn Host> {
    &self.host
  }
}
