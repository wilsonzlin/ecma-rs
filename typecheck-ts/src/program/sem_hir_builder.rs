extern crate semantic_js as semantic_js_crate;

use crate::api::{DefId, FileId, TextRange};
use hir_js::{BodyKind as HirBodyKind, DefKind as HirDefKind};
use semantic_js_crate::ts as sem_ts;
use std::collections::HashSet;
use std::hash::{Hash, Hasher};

use super::DefKind;

#[derive(Clone, Debug)]
pub(super) struct SemHirBuilder {
  pub(super) file: FileId,
  pub(super) file_kind: sem_ts::FileKind,
  pub(super) is_ambient: bool,
  pub(super) decls: Vec<sem_ts::Decl>,
  pub(super) imports: Vec<sem_ts::Import>,
  pub(super) import_equals: Vec<sem_ts::ImportEquals>,
  pub(super) exports: Vec<sem_ts::Export>,
  pub(super) ambient_modules: Vec<sem_ts::AmbientModule>,
}

impl SemHirBuilder {
  pub(super) fn new(file: FileId, file_kind: sem_ts::FileKind) -> Self {
    SemHirBuilder {
      file,
      file_kind,
      is_ambient: false,
      decls: Vec::new(),
      imports: Vec::new(),
      import_equals: Vec::new(),
      exports: Vec::new(),
      ambient_modules: Vec::new(),
    }
  }

  pub(super) fn new_ambient(file: FileId, file_kind: sem_ts::FileKind) -> Self {
    SemHirBuilder {
      is_ambient: true,
      ..SemHirBuilder::new(file, file_kind)
    }
  }

  pub(super) fn add_decl(
    &mut self,
    def: DefId,
    name: String,
    kind: sem_ts::DeclKind,
    exported: sem_ts::Exported,
    span: TextRange,
  ) {
    self.decls.push(sem_ts::Decl {
      def_id: sem_ts::DefId(def.0),
      name,
      kind,
      is_ambient: self.is_ambient,
      is_global: false,
      exported,
      span,
    });
  }

  pub(super) fn add_import(&mut self, import: sem_ts::Import) {
    self.imports.push(import);
  }

  pub(super) fn add_import_equals(&mut self, import_equals: sem_ts::ImportEquals) {
    self.import_equals.push(import_equals);
  }

  pub(super) fn add_ambient_module(&mut self, module: sem_ts::AmbientModule) {
    self.ambient_modules.push(module);
  }

  pub(super) fn add_named_export(
    &mut self,
    specifier: Option<String>,
    specifier_span: Option<TextRange>,
    items: Vec<sem_ts::ExportSpecifier>,
    is_type_only: bool,
  ) {
    if items.is_empty() {
      return;
    }
    self
      .exports
      .push(sem_ts::Export::Named(sem_ts::NamedExport {
        specifier,
        specifier_span,
        items,
        is_type_only,
      }));
  }

  pub(super) fn add_export_all(
    &mut self,
    specifier: String,
    specifier_span: TextRange,
    is_type_only: bool,
    alias: Option<(String, TextRange)>,
  ) {
    self.exports.push(sem_ts::Export::All(sem_ts::ExportAll {
      specifier,
      is_type_only,
      specifier_span,
      alias: alias.as_ref().map(|(name, _)| name.clone()),
      alias_span: alias.as_ref().map(|(_, span)| *span),
    }));
  }

  pub(super) fn finish(self) -> sem_ts::HirFile {
    sem_ts::HirFile {
      file_id: sem_ts::FileId(self.file.0),
      module_kind: sem_ts::ModuleKind::Module,
      file_kind: self.file_kind,
      decls: self.decls,
      imports: self.imports,
      type_imports: Vec::new(),
      import_equals: self.import_equals,
      exports: self.exports,
      export_as_namespace: Vec::new(),
      ambient_modules: self.ambient_modules,
    }
  }

  pub(super) fn into_ambient(self, name: String, name_span: TextRange) -> sem_ts::AmbientModule {
    sem_ts::AmbientModule {
      name,
      name_span,
      decls: self.decls,
      imports: self.imports,
      type_imports: Vec::new(),
      import_equals: self.import_equals,
      exports: self.exports,
      export_as_namespace: Vec::new(),
      ambient_modules: self.ambient_modules,
    }
  }
}

#[derive(Clone, Copy, Debug)]
pub(super) struct BodyMeta {
  pub(super) file: FileId,
  pub(super) hir: Option<hir_js::BodyId>,
  pub(super) kind: HirBodyKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum DefMatchKind {
  Function,
  Var,
  VarDeclarator,
  Class,
  Enum,
  Namespace,
  Module,
  Interface,
  TypeAlias,
  Import,
  Other,
}

pub(super) fn match_kind_from_def(kind: &DefKind) -> DefMatchKind {
  match kind {
    DefKind::Function(_) => DefMatchKind::Function,
    DefKind::Var(_) => DefMatchKind::Var,
    DefKind::VarDeclarator(_) => DefMatchKind::VarDeclarator,
    DefKind::Class(_) => DefMatchKind::Class,
    DefKind::Enum(_) => DefMatchKind::Enum,
    DefKind::Namespace(_) => DefMatchKind::Namespace,
    DefKind::Module(_) => DefMatchKind::Module,
    DefKind::Import(_) => DefMatchKind::Import,
    DefKind::ImportAlias(_) => DefMatchKind::Import,
    DefKind::Interface(_) => DefMatchKind::Interface,
    DefKind::TypeAlias(_) => DefMatchKind::TypeAlias,
  }
}

pub(super) fn match_kind_from_hir(kind: HirDefKind) -> DefMatchKind {
  match kind {
    HirDefKind::Function | HirDefKind::Method | HirDefKind::Constructor => DefMatchKind::Function,
    HirDefKind::ImportBinding => DefMatchKind::Import,
    HirDefKind::Class => DefMatchKind::Class,
    HirDefKind::Enum => DefMatchKind::Enum,
    HirDefKind::Namespace => DefMatchKind::Namespace,
    HirDefKind::Module => DefMatchKind::Module,
    HirDefKind::VarDeclarator => DefMatchKind::VarDeclarator,
    HirDefKind::Var | HirDefKind::Field | HirDefKind::Param | HirDefKind::ExportAlias => {
      DefMatchKind::Var
    }
    HirDefKind::Interface => DefMatchKind::Interface,
    HirDefKind::TypeAlias => DefMatchKind::TypeAlias,
    _ => DefMatchKind::Other,
  }
}

fn stable_hash_u32<T: Hash>(value: &T) -> u32 {
  struct StableHasher(u64);

  impl StableHasher {
    const OFFSET: u64 = 0xcbf29ce484222325;
    const PRIME: u64 = 0x100000001b3;

    fn new() -> Self {
      StableHasher(Self::OFFSET)
    }
  }

  impl Hasher for StableHasher {
    fn finish(&self) -> u64 {
      self.0
    }

    fn write(&mut self, bytes: &[u8]) {
      for b in bytes {
        self.0 ^= *b as u64;
        self.0 = self.0.wrapping_mul(Self::PRIME);
      }
    }
  }

  let mut hasher = StableHasher::new();
  value.hash(&mut hasher);
  let hash = hasher.finish();
  (hash ^ (hash >> 32)) as u32
}

pub(super) fn alloc_synthetic_def_id<T: Hash>(
  file: FileId,
  taken: &mut HashSet<DefId>,
  seed: &T,
) -> DefId {
  for salt in 0u32.. {
    let candidate = if salt == 0 {
      stable_hash_u32(seed)
    } else {
      stable_hash_u32(&(seed, salt))
    };
    let id = DefId::new(file, candidate);
    if taken.insert(id) {
      return id;
    }
  }
  unreachable!("exhausted u32 space allocating synthetic def id")
}
