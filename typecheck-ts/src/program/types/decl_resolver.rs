use super::*;

#[derive(Clone)]
pub(in super::super) struct DeclTypeResolver {
  file: FileId,
  defs: Arc<HashMap<(FileId, String), DefId>>,
  qualified_def_members: Arc<HashMap<(DefId, String, sem_ts::Namespace), DefId>>,
  by_name: HashMap<String, DefId>,
}

impl DeclTypeResolver {
  pub(in super::super) fn new(
    file: FileId,
    defs: Arc<HashMap<(FileId, String), DefId>>,
    qualified_def_members: Arc<HashMap<(DefId, String, sem_ts::Namespace), DefId>>,
  ) -> Self {
    let mut by_name = HashMap::new();
    let mut ordered: Vec<(FileId, String, DefId)> = defs
      .iter()
      .map(|((file, name), def)| (*file, name.clone(), *def))
      .collect();
    ordered.sort_by(|a, b| (a.1.as_str(), a.0 .0, a.2 .0).cmp(&(b.1.as_str(), b.0 .0, b.2 .0)));
    for (_file, name, def) in ordered.into_iter() {
      by_name.entry(name).or_insert(def);
    }
    DeclTypeResolver {
      file,
      defs,
      qualified_def_members,
      by_name,
    }
  }

  fn resolve_name(&self, name: &str) -> Option<DefId> {
    self
      .defs
      .get(&(self.file, name.to_string()))
      .copied()
      .or_else(|| self.by_name.get(name).copied())
  }

  fn resolve_qualified(&self, path: &[String], final_ns: sem_ts::Namespace) -> Option<DefId> {
    let (first, rest) = path.split_first()?;
    let mut current = self.resolve_name(first)?;
    for (idx, segment) in rest.iter().enumerate() {
      let is_last = idx + 1 == rest.len();
      let ns = if is_last {
        final_ns
      } else {
        sem_ts::Namespace::NAMESPACE
      };
      current = *self
        .qualified_def_members
        .get(&(current, segment.clone(), ns))?;
    }
    Some(current)
  }
}

impl TypeResolver for DeclTypeResolver {
  fn resolve_type_name(&self, path: &[String]) -> Option<tti::DefId> {
    if path.len() < 2 {
      path.last().and_then(|name| self.resolve_name(name))
    } else {
      self.resolve_qualified(path, sem_ts::Namespace::TYPE)
    }
  }

  fn resolve_typeof(&self, path: &[String]) -> Option<tti::DefId> {
    if path.len() < 2 {
      self.resolve_type_name(path)
    } else {
      self.resolve_qualified(path, sem_ts::Namespace::VALUE)
    }
  }
}
