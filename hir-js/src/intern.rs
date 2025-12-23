use crate::ids::NameId;
use ahash::AHashMap;

#[derive(Debug, Default, Clone, PartialEq)]
pub struct NameInterner {
  names: Vec<String>,
  map: AHashMap<String, NameId>,
}

impl NameInterner {
  pub fn intern(&mut self, name: impl AsRef<str>) -> NameId {
    let name_ref = name.as_ref();
    if let Some(existing) = self.map.get(name_ref) {
      return *existing;
    }
    let id = NameId(self.names.len() as u32);
    self.names.push(name_ref.to_string());
    self.map.insert(name_ref.to_string(), id);
    id
  }

  pub fn resolve(&self, id: NameId) -> Option<&str> {
    self.names.get(id.0 as usize).map(|s| s.as_str())
  }

  pub fn len(&self) -> usize {
    self.names.len()
  }
}

#[cfg(test)]
mod tests {
  use super::NameInterner;

  #[test]
  fn interning_is_deduplicated() {
    let mut interner = NameInterner::default();
    let a = interner.intern("foo");
    let b = interner.intern("foo");
    assert_eq!(a, b);
    assert_eq!(interner.len(), 1);
  }
}
