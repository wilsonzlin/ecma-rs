use super::*;

impl ProgramTypeResolver {
  pub(super) fn resolve_namespace_symbol_defs(&self, name: &str) -> Option<Vec<DefId>> {
    if let Some(local_def) = self.resolve_local(name, sem_ts::Namespace::NAMESPACE) {
      if let Some(symbol) = self
        .semantics
        .symbol_for_def(local_def, sem_ts::Namespace::NAMESPACE)
      {
        let defs = self.collect_symbol_decls(symbol, sem_ts::Namespace::NAMESPACE);
        if !defs.is_empty() {
          return Some(defs);
        }
      }
      return Some(vec![local_def]);
    }

    let symbol = self
      .semantics
      .resolve_in_module(
        sem_ts::FileId(self.current_file.0),
        name,
        sem_ts::Namespace::NAMESPACE,
      )
      .or_else(|| self.global_symbol(name, sem_ts::Namespace::NAMESPACE))?;
    let defs = self.collect_symbol_decls(symbol, sem_ts::Namespace::NAMESPACE);
    (!defs.is_empty()).then_some(defs)
  }

  pub(super) fn resolve_namespace_member_path(
    &self,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    if path.len() < 2 {
      return None;
    }
    let mut parents = self.resolve_namespace_symbol_defs(&path[0])?;
    // Resolve intermediate namespace segments (excluding final segment).
    for segment in path.iter().take(path.len() - 1).skip(1) {
      let mut next: Vec<DefId> = Vec::new();
      let mut seen: HashSet<DefId> = HashSet::new();
      for parent in parents.iter().copied() {
        if let Some(members) =
          self
            .namespace_members
            .members(parent, sem_ts::Namespace::NAMESPACE, segment)
        {
          for member in members.iter().copied() {
            if seen.insert(member) {
              next.push(member);
            }
          }
        }
      }
      if next.is_empty() {
        return None;
      }
      next.sort_by_key(|id| id.0);
      next.dedup();
      parents = next;
    }

    let final_segment = path.last()?;
    let mut candidates: Vec<DefId> = Vec::new();
    let mut seen: HashSet<DefId> = HashSet::new();
    for parent in parents.iter().copied() {
      if let Some(members) = self
        .namespace_members
        .members(parent, final_ns, final_segment)
      {
        for member in members.iter().copied() {
          if seen.insert(member) {
            candidates.push(member);
          }
        }
      }
    }
    self.pick_best_def(candidates, final_ns)
  }

  pub(super) fn resolve_namespace_symbol_defs_in_file(
    &self,
    file: sem_ts::FileId,
    name: &str,
  ) -> Option<Vec<DefId>> {
    let symbol = self
      .semantics
      .resolve_in_module(file, name, sem_ts::Namespace::NAMESPACE)
      .or_else(|| self.global_symbol(name, sem_ts::Namespace::NAMESPACE))?;
    let defs = self.collect_symbol_decls(symbol, sem_ts::Namespace::NAMESPACE);
    (!defs.is_empty()).then_some(defs)
  }

  pub(super) fn resolve_namespace_member_path_in_file(
    &self,
    file: sem_ts::FileId,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    if path.len() < 2 {
      return None;
    }
    let mut parents = self.resolve_namespace_symbol_defs_in_file(file, &path[0])?;
    for segment in path.iter().take(path.len() - 1).skip(1) {
      let mut next: Vec<DefId> = Vec::new();
      let mut seen: HashSet<DefId> = HashSet::new();
      for parent in parents.iter().copied() {
        if let Some(members) =
          self
            .namespace_members
            .members(parent, sem_ts::Namespace::NAMESPACE, segment)
        {
          for member in members.iter().copied() {
            if seen.insert(member) {
              next.push(member);
            }
          }
        }
      }
      if next.is_empty() {
        return None;
      }
      next.sort_by_key(|id| id.0);
      next.dedup();
      parents = next;
    }

    let final_segment = path.last()?;
    let mut candidates: Vec<DefId> = Vec::new();
    let mut seen: HashSet<DefId> = HashSet::new();
    for parent in parents.iter().copied() {
      if let Some(members) = self
        .namespace_members
        .members(parent, final_ns, final_segment)
      {
        for member in members.iter().copied() {
          if seen.insert(member) {
            candidates.push(member);
          }
        }
      }
    }
    self.pick_best_def(candidates, final_ns)
  }

  pub(super) fn resolve_namespace_symbol_defs_in_ambient_module(
    &self,
    specifier: &str,
    name: &str,
  ) -> Option<Vec<DefId>> {
    let group = self
      .semantics
      .ambient_module_symbols()
      .get(specifier)?
      .get(name)?;
    let symbol = group.symbol_for(sem_ts::Namespace::NAMESPACE, self.semantics.symbols())?;
    let defs = self.collect_symbol_decls(symbol, sem_ts::Namespace::NAMESPACE);
    (!defs.is_empty()).then_some(defs)
  }

  pub(super) fn resolve_namespace_member_path_in_ambient_module(
    &self,
    specifier: &str,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    if path.len() < 2 {
      return None;
    }
    let mut parents = self.resolve_namespace_symbol_defs_in_ambient_module(specifier, &path[0])?;
    for segment in path.iter().take(path.len() - 1).skip(1) {
      let mut next: Vec<DefId> = Vec::new();
      let mut seen: HashSet<DefId> = HashSet::new();
      for parent in parents.iter().copied() {
        if let Some(members) =
          self
            .namespace_members
            .members(parent, sem_ts::Namespace::NAMESPACE, segment)
        {
          for member in members.iter().copied() {
            if seen.insert(member) {
              next.push(member);
            }
          }
        }
      }
      if next.is_empty() {
        return None;
      }
      next.sort_by_key(|id| id.0);
      next.dedup();
      parents = next;
    }

    let final_segment = path.last()?;
    let mut candidates: Vec<DefId> = Vec::new();
    let mut seen: HashSet<DefId> = HashSet::new();
    for parent in parents.iter().copied() {
      if let Some(members) = self
        .namespace_members
        .members(parent, final_ns, final_segment)
      {
        for member in members.iter().copied() {
          if seen.insert(member) {
            candidates.push(member);
          }
        }
      }
    }
    self.pick_best_def(candidates, final_ns)
  }
}
