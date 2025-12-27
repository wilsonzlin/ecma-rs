use crate::api::{FileId, FileKey};
use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

const FALLBACK_START: u32 = 1 << 31;

fn preferred_file_id(key: &FileKey) -> Option<u32> {
  let name = key.as_str();
  let remainder = name.strip_prefix("file")?;
  let stripped = remainder
    .strip_suffix(".ts")
    .or_else(|| remainder.strip_suffix(".tsx"))?;
  stripped.parse::<u32>().ok()
}

fn stable_hash(key: &FileKey) -> u64 {
  let mut hasher = DefaultHasher::new();
  key.as_str().hash(&mut hasher);
  hasher.finish()
}

/// Deterministic registry mapping [`FileKey`]s to [`FileId`]s.
///
/// IDs are stable for the lifetime of the registry and derived purely from the
/// key to avoid order-dependent allocation. Keys matching the `file{N}.ts` or
/// `file{N}.tsx` pattern reserve `FileId(N)` when available; all other keys use a
/// stable hash-based fallback in a high numeric range to avoid colliding with
/// small test IDs.
#[derive(Clone, Debug, Default)]
pub(crate) struct FileRegistry {
  key_to_id: HashMap<FileKey, FileId>,
  id_to_key: HashMap<FileId, FileKey>,
}

impl FileRegistry {
  pub(crate) fn new() -> Self {
    Self::default()
  }

  pub(crate) fn lookup_key(&self, id: FileId) -> Option<FileKey> {
    self.id_to_key.get(&id).cloned()
  }

  pub(crate) fn lookup_id(&self, key: &FileKey) -> Option<FileId> {
    self.key_to_id.get(key).copied()
  }

  pub(crate) fn intern(&mut self, key: &FileKey) -> FileId {
    if let Some(id) = self.lookup_id(key) {
      return id;
    }
    let id = if let Some(preferred) = preferred_file_id(key) {
      let preferred_id = FileId(preferred);
      if !self.id_to_key.contains_key(&preferred_id) {
        preferred_id
      } else {
        self.allocate_fallback(key)
      }
    } else {
      self.allocate_fallback(key)
    };
    self.key_to_id.insert(key.clone(), id);
    self.id_to_key.insert(id, key.clone());
    id
  }

  fn allocate_fallback(&mut self, key: &FileKey) -> FileId {
    let mut candidate = (stable_hash(key) as u32) | FALLBACK_START;
    if candidate == u32::MAX {
      candidate = FALLBACK_START;
    }
    while self.id_to_key.contains_key(&FileId(candidate)) {
      candidate = candidate.wrapping_add(1);
      if candidate < FALLBACK_START {
        candidate = FALLBACK_START;
      }
    }
    FileId(candidate)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn deterministic_across_interning_order() {
    let file0 = FileKey::new("file0.ts");
    let file10 = FileKey::new("file10.ts");
    let other = FileKey::new("x.ts");

    let mut registry_a = FileRegistry::new();
    registry_a.intern(&file10);
    registry_a.intern(&other);
    registry_a.intern(&file0);

    let mut registry_b = FileRegistry::new();
    registry_b.intern(&file0);
    registry_b.intern(&file10);
    registry_b.intern(&other);

    assert_eq!(registry_a.lookup_id(&file0), Some(FileId(0)));
    assert_eq!(registry_b.lookup_id(&file0), Some(FileId(0)));
    assert_eq!(registry_a.lookup_id(&file10), Some(FileId(10)));
    assert_eq!(registry_b.lookup_id(&file10), Some(FileId(10)));

    let other_id_a = registry_a.lookup_id(&other).expect("other file id");
    let other_id_b = registry_b.lookup_id(&other).expect("other file id");
    assert_eq!(other_id_a, other_id_b);
    assert_eq!(registry_a.lookup_key(other_id_a), Some(other.clone()));
    assert_eq!(registry_b.lookup_key(other_id_b), Some(other));
  }
}
