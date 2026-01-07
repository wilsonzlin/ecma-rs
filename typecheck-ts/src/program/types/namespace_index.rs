use super::*;

#[derive(Clone, Debug, Default)]
pub(crate) struct NamespaceMemberIndex {
  // (parent def, namespace bit) -> (member name -> candidate defs)
  by_parent: HashMap<(DefId, sem_ts::Namespace), HashMap<String, Vec<DefId>>>,
}

impl NamespaceMemberIndex {
  pub(in super::super) fn insert(
    &mut self,
    parent: DefId,
    ns: sem_ts::Namespace,
    name: String,
    def: DefId,
  ) {
    self
      .by_parent
      .entry((parent, ns))
      .or_default()
      .entry(name)
      .or_default()
      .push(def);
  }

  pub(in super::super) fn members(
    &self,
    parent: DefId,
    ns: sem_ts::Namespace,
    name: &str,
  ) -> Option<&[DefId]> {
    self
      .by_parent
      .get(&(parent, ns))
      .and_then(|map| map.get(name))
      .map(|defs| defs.as_slice())
  }

  pub(in super::super) fn finalize(&mut self) {
    for map in self.by_parent.values_mut() {
      for defs in map.values_mut() {
        defs.sort_by_key(|id| id.0);
        defs.dedup();
      }
    }
  }
}
