use super::*;

impl ProgramState {
  pub(in super::super) fn rebuild_body_owners(&mut self) {
    self.body_owners.clear();
    let mut defs: Vec<_> = self.def_data.iter().collect();
    defs.sort_by_key(|(id, data)| (data.file.0, data.span.start, data.span.end, id.0));
    for (def_id, data) in defs {
      match &data.kind {
        DefKind::Function(func) => {
          if let Some(body) = func.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Var(var) => {
          if var.body != MISSING_BODY {
            self.body_owners.insert(var.body, *def_id);
          }
        }
        DefKind::VarDeclarator(var) => {
          if let Some(body) = var.body {
            self.body_owners.entry(body).or_insert(*def_id);
          }
        }
        DefKind::Class(class) => {
          if let Some(body) = class.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Enum(en) => {
          if let Some(body) = en.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Namespace(ns) => {
          if let Some(body) = ns.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Module(ns) => {
          if let Some(body) = ns.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Import(_)
        | DefKind::ImportAlias(_)
        | DefKind::Interface(_)
        | DefKind::TypeAlias(_) => {}
      }
    }
  }
}
