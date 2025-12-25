use diagnostics::FileId;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct DefId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct BodyId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ExprId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct PatId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct StmtId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct TypeExprId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct TypeParamId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct TypeMemberId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ImportId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ImportSpecifierId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ExportId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ExportSpecifierId(pub u32);

/// Content-addressed identifier for an interned name.
///
/// Unlike sequential indices, this value is derived from the name text (see
/// [`NameInterner`](crate::intern::NameInterner)) so it remains stable even if
/// other identifiers are introduced earlier in the file.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct NameId(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u8)]
pub enum DefKind {
  Module,
  Namespace,
  Class,
  Function,
  Method,
  Constructor,
  Field,
  Var,
  Param,
  TypeAlias,
  Interface,
  Enum,
  EnumMember,
  ImportBinding,
  ExportAlias,
  TypeParam,
  Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefPath {
  pub module: FileId,
  pub kind: DefKind,
  pub name: NameId,
  pub disambiguator: u32,
}

impl DefPath {
  pub fn new(module: FileId, kind: DefKind, name: NameId, disambiguator: u32) -> Self {
    Self {
      module,
      kind,
      name,
      disambiguator,
    }
  }

  pub fn stable_hash(&self) -> u64 {
    let mut hasher = StableHasher::new();
    hasher.write_u64(self.module.0 as u64);
    hasher.write_u64(self.kind as u64);
    hasher.write_u64(self.disambiguator as u64);
    hasher.write_u64(self.name.0);
    hasher.finish()
  }

  pub fn stable_hash_u32(&self) -> u32 {
    let mut hasher = StableHasher::new();
    hasher.write_u64(self.module.0 as u64);
    hasher.write_u64(self.kind as u64);
    hasher.write_u64(self.disambiguator as u64);
    hasher.write_u64(self.name.0);
    hasher.finish_u32()
  }
}

const STABLE_HASH_OFFSET: u64 = 0xcbf29ce484222325;
const STABLE_HASH_PRIME: u64 = 0x100000001b3;

pub(crate) struct StableHasher(u64);

impl StableHasher {
  pub fn new() -> Self {
    Self(STABLE_HASH_OFFSET)
  }

  pub fn write_u64(&mut self, value: u64) {
    for byte in value.to_le_bytes() {
      self.write_byte(byte);
    }
  }

  pub fn write_str(&mut self, value: &str) {
    for byte in value.as_bytes() {
      self.write_byte(*byte);
    }
  }

  pub fn finish(self) -> u64 {
    self.0
  }

  pub fn finish_u32(self) -> u32 {
    let hash = self.finish();
    (hash ^ (hash >> 32)) as u32
  }

  fn write_byte(&mut self, byte: u8) {
    self.0 ^= byte as u64;
    self.0 = self.0.wrapping_mul(STABLE_HASH_PRIME);
  }
}
