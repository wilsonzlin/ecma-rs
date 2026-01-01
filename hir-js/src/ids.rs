use crate::hir::BodyKind;
use diagnostics::FileId;

#[cfg(test)]
use std::cell::Cell;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Stable identifier for a lowered definition.
///
/// `DefId` values are derived from hashing a [`DefPath`] with a deterministic,
/// platform-independent hasher and truncating the result to 32 bits. Because
/// truncation can theoretically collide, lowering keeps a map of allocated
/// identifiers and will re-hash the `DefPath` with an incrementing salt until
/// an unused value is found. The list of definition descriptors is sorted
/// before allocation, so collision handling is deterministic for a given
/// source file.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct DefId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct BodyId(pub u32);

/// Content-addressed identifier for a lowered body.
///
/// `BodyId` values are derived from their owning [`DefId`], the body kind, and
/// an optional disambiguator (see [`BodyPath`]) to remain stable even when new
/// bodies are introduced elsewhere in the file. Allocation will re-hash the
/// path with a deterministic salt if the 32-bit hash collides, mirroring
/// [`DefId`] allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BodyPath {
  pub owner: DefId,
  pub kind: BodyKind,
  pub disambiguator: u32,
}

impl BodyPath {
  pub fn new(owner: DefId, kind: BodyKind, disambiguator: u32) -> Self {
    Self {
      owner,
      kind,
      disambiguator,
    }
  }

  pub fn stable_hash(&self) -> u64 {
    self.stable_hash_impl(None).finish()
  }

  pub fn stable_hash_u32(&self) -> u32 {
    #[cfg(test)]
    if let Some(hash) = test_body_path_hash_override(self) {
      return hash;
    }

    self.stable_hash_with_salt(0)
  }

  /// Compute a stable hash with an additional deterministic salt to derive an
  /// alternative `BodyId` when the base hash collides.
  pub fn stable_hash_with_salt(&self, salt: u64) -> u32 {
    self.stable_hash_impl(Some(salt)).finish_u32()
  }

  fn stable_hash_impl(&self, salt: Option<u64>) -> StableHasher {
    let mut hasher = StableHasher::new();
    hasher.write_u64(self.owner.0 as u64);
    hasher.write_u64(self.kind as u64);
    hasher.write_u64(self.disambiguator as u64);
    if let Some(salt) = salt.filter(|s| *s != 0) {
      hasher.write_u64(salt);
    }
    hasher
  }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ExprId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct PatId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct StmtId(pub u32);

/// Identifier for a type expression within a single definition's type arenas.
///
/// The numeric index is local to the owning [`DefId`]; combine it with the
/// definition to look up spans or resolve the corresponding [`TypeExpr`]
/// payload.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct TypeExprId(pub u32);

/// Identifier for a type parameter within a single definition's type arenas.
///
/// Values are only meaningful when used with the [`DefId`] that owns the
/// surrounding declaration.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct TypeParamId(pub u32);

/// Identifier for a type member (e.g. property or signature) scoped to a
/// single definition's type arenas.
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
  Getter,
  Setter,
  StaticBlock,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefPath {
  pub module: FileId,
  pub parent: Option<DefId>,
  pub kind: DefKind,
  pub name: NameId,
  pub disambiguator: u32,
}

impl DefPath {
  pub fn new(
    module: FileId,
    parent: Option<DefId>,
    kind: DefKind,
    name: NameId,
    disambiguator: u32,
  ) -> Self {
    Self {
      module,
      parent,
      kind,
      name,
      disambiguator,
    }
  }

  pub fn stable_hash(&self) -> u64 {
    let hasher = self.stable_hash_impl(None);
    hasher.finish()
  }

  pub fn stable_hash_u32(&self) -> u32 {
    #[cfg(test)]
    if let Some(hash) = test_def_path_hash_override(self) {
      return hash;
    }

    self.stable_hash_with_salt(0)
  }

  /// Compute a stable hash with an additional deterministic salt to derive an
  /// alternative `DefId` when the base hash collides.
  pub fn stable_hash_with_salt(&self, salt: u64) -> u32 {
    self.stable_hash_impl(Some(salt)).finish_u32()
  }

  fn stable_hash_impl(&self, salt: Option<u64>) -> StableHasher {
    let mut hasher = StableHasher::new();
    hasher.write_u64(self.module.0 as u64);
    hasher.write_u64(self.parent.map_or(0, |id| id.0 as u64 + 1));
    hasher.write_u64(self.kind as u64);
    hasher.write_u64(self.disambiguator as u64);
    hasher.write_u64(self.name.0);
    if let Some(salt) = salt.filter(|s| *s != 0) {
      hasher.write_u64(salt);
    }
    hasher
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

#[cfg(test)]
thread_local! {
  static TEST_DEF_PATH_HASH_OVERRIDE: Cell<Option<fn(&DefPath) -> u32>> = Cell::new(None);
}

#[cfg(test)]
fn test_def_path_hash_override(def_path: &DefPath) -> Option<u32> {
  TEST_DEF_PATH_HASH_OVERRIDE.with(|cell| cell.get().map(|hasher| hasher(def_path)))
}

#[cfg(test)]
thread_local! {
  static TEST_BODY_PATH_HASH_OVERRIDE: Cell<Option<fn(&BodyPath) -> u32>> = Cell::new(None);
}

#[cfg(test)]
fn test_body_path_hash_override(body_path: &BodyPath) -> Option<u32> {
  TEST_BODY_PATH_HASH_OVERRIDE.with(|cell| cell.get().map(|hasher| hasher(body_path)))
}

/// Run `f` with a test-only override for `BodyPath::stable_hash_u32`.
///
/// The override is thread-local to avoid affecting other tests running in
/// parallel; it is cleared before returning.
#[cfg(test)]
pub(crate) fn with_test_body_path_hasher<R>(
  hasher: fn(&BodyPath) -> u32,
  f: impl FnOnce() -> R,
) -> R {
  TEST_BODY_PATH_HASH_OVERRIDE.with(|cell| {
    let prev = cell.replace(Some(hasher));
    let result = f();
    cell.set(prev);
    result
  })
}

/// Run `f` with a test-only override for `DefPath::stable_hash_u32`.
///
/// The override is thread-local to avoid affecting other tests running in
/// parallel; it is cleared before returning.
#[cfg(test)]
pub(crate) fn with_test_def_path_hasher<R>(
  hasher: fn(&DefPath) -> u32,
  f: impl FnOnce() -> R,
) -> R {
  TEST_DEF_PATH_HASH_OVERRIDE.with(|cell| {
    let prev = cell.replace(Some(hasher));
    let result = f();
    cell.set(prev);
    result
  })
}
