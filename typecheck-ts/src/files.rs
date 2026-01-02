use crate::api::{FileId, FileKey};
use ahash::AHashMap;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const FALLBACK_START: u32 = 1 << 31;

/// Distinguish between user-provided source files and library inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FileOrigin {
  Source,
  Lib,
}

impl FileOrigin {
  fn stable_discriminant(&self) -> u8 {
    match self {
      FileOrigin::Source => 0,
      FileOrigin::Lib => 1,
    }
  }
}

fn preferred_file_id(key: &FileKey) -> Option<u32> {
  let name = key.as_str();
  let remainder = name.strip_prefix("file")?;
  let stripped = remainder
    .strip_suffix(".ts")
    .or_else(|| remainder.strip_suffix(".tsx"))?;
  stripped.parse::<u32>().ok()
}

fn stable_hash(key: &FileKey, origin: FileOrigin, salt: u64) -> u64 {
  let mut hasher = DefaultHasher::new();
  hasher.write_u8(origin.stable_discriminant());
  hasher.write_u64(salt);
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
  keys: AHashMap<FileKey, FileRegistryEntry>,
  id_to_key: AHashMap<FileId, FileKey>,
  id_to_origin: AHashMap<FileId, FileOrigin>,
}

#[derive(Clone, Debug, Default)]
struct FileRegistryEntry {
  source: Option<FileId>,
  lib: Option<FileId>,
}

impl FileRegistry {
  pub(crate) fn new() -> Self {
    Self::default()
  }

  pub(crate) fn lookup_key(&self, id: FileId) -> Option<FileKey> {
    self.id_to_key.get(&id).cloned()
  }

  pub(crate) fn lookup_origin(&self, id: FileId) -> Option<FileOrigin> {
    self.id_to_origin.get(&id).copied()
  }

  pub(crate) fn lookup_id(&self, key: &FileKey) -> Option<FileId> {
    let entry = self.keys.get(key)?;
    entry.source.or(entry.lib)
  }

  pub(crate) fn lookup_id_with_origin(&self, key: &FileKey, origin: FileOrigin) -> Option<FileId> {
    let entry = self.keys.get(key)?;
    match origin {
      FileOrigin::Source => entry.source,
      FileOrigin::Lib => entry.lib,
    }
  }

  pub(crate) fn ids_for_key(&self, key: &FileKey) -> Vec<FileId> {
    let entry = self.keys.get(key);
    let mut ids = Vec::new();
    if let Some(entry) = entry {
      if let Some(id) = entry.source {
        ids.push(id);
      }
      if let Some(id) = entry.lib {
        ids.push(id);
      }
    }
    ids
  }

  pub(crate) fn intern(&mut self, key: &FileKey, origin: FileOrigin) -> FileId {
    if let Some(id) = self.lookup_id_with_origin(key, origin) {
      return id;
    }

    let id = match origin {
      FileOrigin::Source => {
        if let Some(preferred) = preferred_file_id(key) {
          let preferred_id = FileId(preferred);
          if !self.id_to_key.contains_key(&preferred_id) {
            preferred_id
          } else {
            self.allocate_fallback(key, origin)
          }
        } else {
          self.allocate_fallback(key, origin)
        }
      }
      FileOrigin::Lib => self.allocate_fallback(key, origin),
    };

    let entry = self.keys.entry(key.clone()).or_default();
    match origin {
      FileOrigin::Source => entry.source = Some(id),
      FileOrigin::Lib => entry.lib = Some(id),
    }
    self.id_to_key.insert(id, key.clone());
    self.id_to_origin.insert(id, origin);
    id
  }

  fn allocate_fallback(&mut self, key: &FileKey, origin: FileOrigin) -> FileId {
    let mut salt = 0u64;
    loop {
      let raw = stable_hash(key, origin, salt);
      let mut candidate = (raw as u32) | FALLBACK_START;
      if candidate == u32::MAX {
        candidate = FALLBACK_START;
      }
      if !self.id_to_key.contains_key(&FileId(candidate)) {
        return FileId(candidate);
      }
      salt = salt.wrapping_add(1);
    }
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
  fn origin_distinguishes_colliding_keys() {
    let key = FileKey::new("lib:lib.es5.d.ts");
    let mut registry = FileRegistry::new();
    let source = registry.intern(&key, FileOrigin::Source);
    let lib = registry.intern(&key, FileOrigin::Lib);
    assert_ne!(source, lib);
    assert_eq!(registry.lookup_id(&key), Some(source));
    assert_eq!(registry.ids_for_key(&key), vec![source, lib]);
  }
}
