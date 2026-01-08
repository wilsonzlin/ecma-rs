use crate::{GcObject, RootId, Scope, Value, VmError};

/// The set of ECMAScript intrinsics for a realm.
///
/// For now this is a minimal placeholder set; it will grow as `vm-js` implements more of the
/// standard library.
#[derive(Debug, Clone, Copy)]
pub struct Intrinsics {
  object_prototype: GcObject,
  array_prototype: GcObject,
}

impl Intrinsics {
  pub(crate) fn init(scope: &mut Scope<'_>, roots: &mut Vec<RootId>) -> Result<Self, VmError> {
    let object_prototype = Self::alloc_rooted_object(scope, roots)?;
    let array_prototype = Self::alloc_rooted_object(scope, roots)?;
    Ok(Self {
      object_prototype,
      array_prototype,
    })
  }

  fn alloc_rooted_object(scope: &mut Scope<'_>, roots: &mut Vec<RootId>) -> Result<GcObject, VmError> {
    let obj = scope.alloc_object()?;
    let root = scope.heap_mut().add_root(Value::Object(obj));
    roots.push(root);
    Ok(obj)
  }

  /// The `%Object.prototype%` intrinsic.
  pub fn object_prototype(&self) -> GcObject {
    self.object_prototype
  }

  /// The `%Array.prototype%` intrinsic.
  pub fn array_prototype(&self) -> GcObject {
    self.array_prototype
  }
}

