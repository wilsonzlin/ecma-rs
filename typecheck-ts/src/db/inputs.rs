use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use diagnostics::{Diagnostic, FileId};

use crate::lib_support::{CompilerOptions, FileKind};
use crate::BodyId;
use crate::FileKey;

/// Wrapper around an atomic cancellation flag that can participate in salsa's
/// change detection.
///
/// Equality is based on the `Arc` identity so the revision only changes when a
/// new token is swapped in. Toggling the atomic flag is expected to happen
/// without notifying salsa and should still be observed by readers of the
/// shared [`Arc<AtomicBool>`](AtomicBool).
#[derive(Clone)]
pub struct CancellationToken(pub Arc<AtomicBool>);

impl CancellationToken {
  pub fn new(flag: Arc<AtomicBool>) -> Self {
    Self(flag)
  }
}

impl std::fmt::Debug for CancellationToken {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("CancellationToken")
      .field("set", &self.0.load(std::sync::atomic::Ordering::Relaxed))
      .finish()
  }
}

impl PartialEq for CancellationToken {
  fn eq(&self, other: &Self) -> bool {
    Arc::ptr_eq(&self.0, &other.0)
  }
}

impl Eq for CancellationToken {}

unsafe impl salsa::Update for CancellationToken {
  unsafe fn maybe_update(old_pointer: *mut Self, new_value: Self) -> bool {
    let old_ref = &mut *old_pointer;
    let changed = !Arc::ptr_eq(&old_ref.0, &new_value.0);
    *old_ref = new_value;
    changed
  }
}

#[salsa::input]
pub struct CompilerOptionsInput {
  pub options: CompilerOptions,
}

#[salsa::input]
pub struct RootsInput {
  pub roots: Arc<[FileKey]>,
}

#[salsa::input]
pub struct CancelledInput {
  pub token: CancellationToken,
}

#[salsa::input]
pub struct FileInput {
  pub file_id: FileId,
  pub key: FileKey,
  pub kind: FileKind,
  pub text: Arc<str>,
}

#[salsa::input]
pub struct ModuleResolutionInput {
  pub from_file: FileId,
  pub specifier: Arc<str>,
  pub resolved: Option<FileId>,
}

#[salsa::input]
pub struct BodyResultInput {
  pub body: BodyId,
  #[return_ref]
  pub result: Arc<crate::BodyCheckResult>,
}

#[salsa::input]
pub struct ExtraDiagnosticsInput {
  #[return_ref]
  pub diagnostics: Arc<[Diagnostic]>,
}
