//! `import.meta` host hooks and helper for constructing the `import.meta` object.
//!
//! ECMA-262 defines `import.meta` evaluation in terms of two host hooks:
//! - `HostGetImportMetaProperties` (<https://tc39.es/ecma262/#sec-hostgetimportmetaproperties>)
//! - `HostFinalizeImportMeta` (<https://tc39.es/ecma262/#sec-hostfinalizeimportmeta>)
//!
//! Even before a full module evaluator exists, host embeddings (or a future module graph loader)
//! need a stable surface to provide `import.meta` data such as `url`.
//!
//! Spec references:
//! - <https://tc39.es/ecma262/#sec-meta-properties-runtime-semantics-evaluation>

use crate::GcObject;
use crate::ModuleId;
use crate::PropertyDescriptor;
use crate::PropertyKey;
use crate::PropertyKind;
use crate::Scope;
use crate::Value;
use crate::Vm;
use crate::VmError;

/// An `import.meta` property contributed by the host.
#[derive(Debug, Clone, Copy)]
pub struct ImportMetaProperty {
  pub key: PropertyKey,
  pub value: Value,
}

/// Host hooks used by `import.meta` evaluation.
pub trait VmImportMetaHostHooks {
  /// Returns the list of initial properties to define on the `import.meta` object for `module`.
  ///
  /// Spec reference: `HostGetImportMetaProperties`:
  /// <https://tc39.es/ecma262/#sec-hostgetimportmetaproperties>.
  fn host_get_import_meta_properties(
    &mut self,
    _vm: &mut Vm,
    _scope: &mut Scope<'_>,
    _module: ModuleId,
  ) -> Result<Vec<ImportMetaProperty>, VmError> {
    Ok(Vec::new())
  }

  /// Gives the host a chance to finalize the `import.meta` object after initial properties have
  /// been defined.
  ///
  /// Spec reference: `HostFinalizeImportMeta`:
  /// <https://tc39.es/ecma262/#sec-hostfinalizeimportmeta>.
  fn host_finalize_import_meta(
    &mut self,
    _vm: &mut Vm,
    _scope: &mut Scope<'_>,
    _import_meta: GcObject,
    _module: ModuleId,
  ) -> Result<(), VmError> {
    Ok(())
  }
}

fn data_property(value: Value) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable: true,
    configurable: true,
    kind: PropertyKind::Data {
      value,
      writable: true,
    },
  }
}

/// Creates the `import.meta` object for `module` using `hooks`.
///
/// This is a reusable helper that implements the spec-level `ImportMeta` object construction:
/// - Creates an object with a `null` prototype (`OrdinaryObjectCreate(null)`).
/// - Defines any host-provided own data properties.
/// - Calls the host finalization hook.
pub fn create_import_meta_object(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  hooks: &mut dyn VmImportMetaHostHooks,
  module: ModuleId,
) -> Result<GcObject, VmError> {
  let mut scope = scope.reborrow();

  // OrdinaryObjectCreate(null).
  let import_meta = scope.alloc_object()?;
  scope.push_root(Value::Object(import_meta))?;

  let properties = hooks.host_get_import_meta_properties(vm, &mut scope, module)?;

  // Root all keys/values so they remain valid across GC while we define properties.
  for prop in &properties {
    match prop.key {
      PropertyKey::String(s) => {
        scope.push_root(Value::String(s))?;
      }
      PropertyKey::Symbol(s) => {
        scope.push_root(Value::Symbol(s))?;
      }
    }
    scope.push_root(prop.value)?;
  }

  for prop in properties {
    scope.define_property(import_meta, prop.key, data_property(prop.value))?;
  }

  hooks.host_finalize_import_meta(vm, &mut scope, import_meta, module)?;
  Ok(import_meta)
}
