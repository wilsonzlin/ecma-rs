use rustc_hash::FxHashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NameId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NameTable {
  pub(crate) names: Vec<String>,
  pub(crate) index: FxHashMap<String, NameId>,
}

impl NameTable {
  pub fn resolve(&self, id: NameId) -> Option<&str> {
    self.names.get(id.0 as usize).map(|s| s.as_str())
  }

  pub fn id(&self, name: &str) -> Option<NameId> {
    self.index.get(name).copied()
  }
}

impl Default for NameTable {
  fn default() -> Self {
    Self {
      names: Vec::new(),
      index: FxHashMap::default(),
    }
  }
}

#[derive(Default, Clone, Debug)]
pub struct NameInterner {
  names: Vec<String>,
  index: FxHashMap<String, NameId>,
}

impl NameInterner {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn intern(&mut self, name: impl Into<String>) -> NameId {
    let name = name.into();
    if let Some(id) = self.index.get(&name) {
      return *id;
    }
    let id = NameId(self.names.len() as u32);
    self.names.push(name.clone());
    self.index.insert(name, id);
    id
  }

  pub fn resolve(&self, id: NameId) -> Option<&str> {
    self.names.get(id.0 as usize).map(|s| s.as_str())
  }

  pub fn into_table(self) -> NameTable {
    NameTable {
      names: self.names,
      index: self.index,
    }
  }
}
