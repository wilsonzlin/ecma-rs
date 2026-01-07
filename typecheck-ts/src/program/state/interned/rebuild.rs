use super::*;

impl ProgramState {
  pub(in super::super) fn rebuild_module_namespace_defs(&mut self) {
    self.module_namespace_defs.clear();
    let mut taken_ids: HashSet<DefId> = self.def_data.keys().copied().collect();
    let mut files: Vec<FileId> = self.files.keys().copied().collect();
    files.sort_by_key(|file| file.0);
    for file in files {
      let key = self
        .file_key_for_id(file)
        .unwrap_or_else(|| FileKey::new(format!("file{}.ts", file.0)));
      let def =
        alloc_synthetic_def_id(file, &mut taken_ids, &("ts_module_namespace", key.as_str()));
      self.module_namespace_defs.insert(file, def);
    }
  }

}
