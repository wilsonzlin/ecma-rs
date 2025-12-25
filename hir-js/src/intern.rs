use crate::ids::{NameId, StableHasher};
use std::collections::BTreeMap;

const NAME_HASH_DOMAIN: u64 = 0x6e616d65; // "name"

#[derive(Debug, Clone)]
pub struct NameInterner {
  by_name: BTreeMap<String, NameId>,
  by_id: BTreeMap<NameId, String>,
  hash: fn(&str, u64) -> NameId,
}

impl PartialEq for NameInterner {
  fn eq(&self, other: &Self) -> bool {
    self.by_name == other.by_name && self.by_id == other.by_id
  }
}

impl Eq for NameInterner {}

impl Default for NameInterner {
  fn default() -> Self {
    Self::new(Self::hash_name)
  }
}

impl NameInterner {
  fn new(hash: fn(&str, u64) -> NameId) -> Self {
    Self {
      by_name: BTreeMap::new(),
      by_id: BTreeMap::new(),
      hash,
    }
  }

  fn hash_name(name: &str, salt: u64) -> NameId {
    let mut hasher = StableHasher::new();
    hasher.write_u64(NAME_HASH_DOMAIN);
    hasher.write_str(name);
    hasher.write_u64(salt);
    NameId(hasher.finish())
  }

  #[cfg(test)]
  fn with_hasher(hash: fn(&str, u64) -> NameId) -> Self {
    Self::new(hash)
  }

  pub fn intern(&mut self, name: impl AsRef<str>) -> NameId {
    let name_ref = name.as_ref();
    if let Some(existing) = self.by_name.get(name_ref) {
      return *existing;
    }
    let owned = name_ref.to_string();
    let mut salt = 0u64;
    loop {
      let id = (self.hash)(name_ref, salt);
      match self.by_id.get(&id) {
        None => {
          self.by_name.insert(owned.clone(), id);
          self.by_id.insert(id, owned);
          return id;
        }
        Some(existing) if existing == name_ref => {
          self.by_name.insert(owned.clone(), id);
          return id;
        }
        Some(_) => salt = salt.wrapping_add(1),
      }
    }
  }

  pub fn resolve(&self, id: NameId) -> Option<&str> {
    self.by_id.get(&id).map(|s| s.as_str())
  }

  pub fn len(&self) -> usize {
    debug_assert_eq!(self.by_name.len(), self.by_id.len());
    self.by_name.len()
  }
}

#[cfg(test)]
mod tests {
  use super::NameInterner;
  use crate::ids::NameId;

  #[test]
  fn interning_is_deduplicated() {
    let mut interner = NameInterner::default();
    let a = interner.intern("foo");
    let b = interner.intern("foo");
    assert_eq!(a, b);
    assert_eq!(interner.len(), 1);
  }

  #[test]
  fn resolves_collisions_deterministically() {
    fn constant_hash(_: &str, salt: u64) -> NameId {
      NameId(42 + salt)
    }

    let mut interner = NameInterner::with_hasher(constant_hash);
    let first = interner.intern("first");
    let second = interner.intern("second");
    let third = interner.intern("third");

    assert_eq!(first, NameId(42));
    assert_eq!(second, NameId(43));
    assert_eq!(third, NameId(44));

    assert_eq!(interner.intern("second"), second);
    assert_eq!(interner.resolve(first), Some("first"));
    assert_eq!(interner.resolve(second), Some("second"));
    assert_eq!(interner.resolve(third), Some("third"));

    let mut interner_again = NameInterner::with_hasher(constant_hash);
    assert_eq!(interner_again.intern("first"), first);
    assert_eq!(interner_again.intern("second"), second);
    assert_eq!(interner_again.intern("third"), third);
  }
}
