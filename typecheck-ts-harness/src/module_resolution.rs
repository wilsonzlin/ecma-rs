use crate::runner::HarnessFileSet;
use typecheck_ts::FileKey;

/// Public wrapper around the harness module resolver.
///
/// The harness itself resolves through `HarnessFileSet::resolve_import`; this type
/// exists so integration tests can exercise the same logic without reaching into
/// crate-private helpers.
#[derive(Debug, Default, Clone, Copy)]
pub struct ModuleResolver;

impl ModuleResolver {
  pub fn new() -> Self {
    Self
  }

  pub fn resolve(
    &self,
    files: &HarnessFileSet,
    from: &FileKey,
    specifier: &str,
  ) -> Option<FileKey> {
    files.resolve_import(from, specifier)
  }
}
