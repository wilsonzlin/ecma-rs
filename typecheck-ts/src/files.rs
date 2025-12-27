use crate::api::{FileId, FileKey};
use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

const FALLBACK_START: u32 = 1 << 31;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FileOrigin {
  Source,
  Lib,
}

#[derive(Clone, Debug)]
struct FileEntry {
  key: FileKey,
  origin: FileOrigin,
}

fn preferred_file_id(key: &FileKey) -> Option<u32> {
  let name = key.as_str();
  let remainder = name.strip_prefix("file")?;
  let stripped = remainder
    .strip_suffix(".ts")
    .or_else(|| remainder.strip_suffix(".tsx"))?;
  stripped.parse::<u32>().ok()
}

fn stable_hash(key: &FileKey, origin: FileOrigin) -> u64 {
  let mut hasher = DefaultHasher::new();
  origin.hash(&mut hasher);
  key.as_str().hash(&mut hasher);
  hasher.finish()
}

/// Deterministic registry mapping [`FileKey`]s to [`FileId`]s with distinct
/// identities for source and library files.
///
/// IDs are stable for the lifetime of the registry and derived purely from the
/// key and origin to avoid order-dependent allocation. Source keys matching the
/// `file{N}.ts` or `file{N}.tsx` pattern reserve `FileId(N)` when available; all
/// other keys use a stable hash-based fallback in a high numeric range to avoid
/// colliding with small test IDs.
#[derive(Clone, Debug, Default)]
pub(crate) struct FileRegistry {
  key_to_ids: HashMap<FileKey, Vec<FileId>>,
  id_to_entry: HashMap<FileId, FileEntry>,
  key_origin_to_id: HashMap<(FileKey, FileOrigin), FileId>,
}

impl FileRegistry {
  pub(crate) fn new() -> Self {
    Self::default()
  }

  pub(crate) fn lookup_key(&self, id: FileId) -> Option<FileKey> {
    self.id_to_entry.get(&id).map(|entry| entry.key.clone())
  }

  pub(crate) fn lookup_id(&self, key: &FileKey) -> Option<FileId> {
    self
      .key_to_ids
      .get(key)
      .and_then(|ids| ids.first().copied())
  }

  pub(crate) fn lookup_ids(&self, key: &FileKey) -> Vec<FileId> {
    let mut ids = self.key_to_ids.get(key).cloned().unwrap_or_default();
    Self::sort_ids(&mut ids, &self.id_to_entry);
    ids
  }

  pub(crate) fn origin(&self, id: FileId) -> Option<FileOrigin> {
    self.id_to_entry.get(&id).map(|entry| entry.origin)
  }

  pub(crate) fn intern(&mut self, key: &FileKey, origin: FileOrigin) -> FileId {
    if let Some(id) = self.key_origin_to_id.get(&(key.clone(), origin)).copied() {
      return id;
    }
    let id = self.allocate_id(key, origin);
    self.id_to_entry.insert(
      id,
      FileEntry {
        key: key.clone(),
        origin,
      },
    );
    self.key_origin_to_id.insert((key.clone(), origin), id);
    let ids = self.key_to_ids.entry(key.clone()).or_default();
    ids.push(id);
    Self::sort_ids(ids, &self.id_to_entry);
    ids.dedup();
    id
  }

  fn allocate_id(&mut self, key: &FileKey, origin: FileOrigin) -> FileId {
    if matches!(origin, FileOrigin::Source) {
      if let Some(preferred) = preferred_file_id(key) {
        let preferred_id = FileId(preferred);
        if !self.id_to_entry.contains_key(&preferred_id) {
          return preferred_id;
        }
      }
    }
    self.allocate_fallback(key, origin)
  }

  fn allocate_fallback(&mut self, key: &FileKey, origin: FileOrigin) -> FileId {
    let mut candidate = (stable_hash(key, origin) as u32) | FALLBACK_START;
    if candidate == u32::MAX {
      candidate = FALLBACK_START;
    }
    while self.id_to_entry.contains_key(&FileId(candidate)) {
      candidate = candidate.wrapping_add(1);
      if candidate < FALLBACK_START {
        candidate = FALLBACK_START;
      }
    }
    FileId(candidate)
  }

  fn sort_ids(ids: &mut Vec<FileId>, entries: &HashMap<FileId, FileEntry>) {
    ids.sort_by_key(|id| {
      let origin = entries
        .get(id)
        .map(|entry| entry.origin)
        .unwrap_or(FileOrigin::Source);
      (origin, id.0)
    });
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
    registry_a.intern(&file10, FileOrigin::Source);
    registry_a.intern(&other, FileOrigin::Source);
    registry_a.intern(&file0, FileOrigin::Source);

    let mut registry_b = FileRegistry::new();
    registry_b.intern(&file0, FileOrigin::Source);
    registry_b.intern(&file10, FileOrigin::Source);
    registry_b.intern(&other, FileOrigin::Source);

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

  #[test]
  fn allows_colliding_keys_with_origins() {
    let key = FileKey::new("lib:lib.es2020.d.ts");
    let mut registry = FileRegistry::new();
    let lib_id = registry.intern(&key, FileOrigin::Lib);
    let source_id = registry.intern(&key, FileOrigin::Source);
    assert_ne!(lib_id, source_id);
    assert_eq!(registry.lookup_id(&key), Some(source_id));
    let mut ids = registry.lookup_ids(&key);
    ids.sort_by_key(|id| id.0);
    assert_eq!(ids.len(), 2);
  }
}
