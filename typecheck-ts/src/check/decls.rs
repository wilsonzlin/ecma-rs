use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::{codes, FileKey, Host};
use diagnostics::{Diagnostic, FileId, Span, TextRange};
use hir_js::{
  DefId as HirDefId, DefKind as HirDefKind, DefTypeInfo, FunctionData, LowerResult, TypeArenas,
  TypeArenasByDef, TypeExprId, TypeExprKind, TypeFnParam, TypeMemberId, TypeMemberKind, TypeName,
  TypeParamId as HirTypeParamId, TypeSignature,
};
use num_bigint::BigInt;
use ordered_float::OrderedFloat;
use semantic_js::ts::{ModuleRef, Namespace, SymbolOrigin, SymbolOwner, TsProgramSemantics};
use types_ts_interned::{
  DefId, Indexer, MappedModifier, MappedType, ObjectType, Param, PredicateParam, PropData, PropKey,
  Property, Shape, Signature, TupleElem, TypeDisplay, TypeId, TypeKind, TypeParamDecl, TypeParamId,
  TypeParamVariance, TypeStore,
};

use super::type_expr::TypeResolver;

/// Result of lowering a value-side [`FunctionData`] signature from HIR.
#[derive(Debug, Clone, Default)]
pub struct ValueFunctionSignature {
  pub params: Vec<Param>,
  pub return_ann: Option<TypeId>,
  pub type_params: Vec<TypeParamDecl>,
  pub this_param: Option<TypeId>,
  /// Per value-parameter annotation (`None` when HIR had no annotation). Excludes
  /// a leading `this` parameter.
  pub param_types_for_binder: Vec<Option<TypeId>>,
}

/// Narrow, object-safe view of [`Host`] used during declaration lowering.
///
/// Unlike `Host` this trait carries no `Send + Sync + 'static` bounds, so
/// short-lived, thread-local implementations (e.g. a borrowed wrapper over the
/// salsa database inside a tracked query) can implement it safely — no raw
/// pointers or manual `Send`/`Sync` claims required.
pub trait DeclHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, crate::HostError>;
  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey>;
}

impl<H: Host + ?Sized> DeclHost for H {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, crate::HostError> {
    Host::file_text(self, file)
  }

  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey> {
    Host::resolve(self, from, specifier)
  }
}

/// Per-file index of HIR defs by name, with one slot per namespace.
///
/// TypeScript declaration merging lets the same name live in different
/// namespaces (`interface NumberFormat` in TYPE, `var NumberFormat` in VALUE).
/// A flat name → def map collides: whichever def is indexed last shadows the
/// other, so a TYPE-position reference (e.g. `prototype: NumberFormat`) can
/// bind to the VALUE-side var and pull the var's unrelated annotation type
/// into the interface's expansion. Keeping one slot per namespace lets each
/// reference bind to a def that actually has presence in the requested
/// namespace, falling back to the other namespaces only when the name has no
/// def there (preserving the previous lenient behavior).
#[derive(Clone, Debug, Default)]
pub struct LocalDefIndex {
  by_name: HashMap<String, LocalDefSlots>,
}

#[derive(Clone, Copy, Debug, Default)]
struct LocalDefSlots {
  type_: Option<HirDefId>,
  value: Option<HirDefId>,
  namespace: Option<HirDefId>,
}

impl LocalDefIndex {
  pub fn from_lowered(lowered: &LowerResult) -> Self {
    let mut by_name: HashMap<String, LocalDefSlots> = HashMap::new();
    for def in lowered.defs.iter() {
      let Some(name) = lowered.names.resolve(def.name) else {
        continue;
      };
      let slots = by_name.entry(name.to_string()).or_default();
      let namespaces = local_def_namespaces(def.path.kind);
      if namespaces.contains(Namespace::TYPE) {
        slots.type_ = Some(def.id);
      }
      if namespaces.contains(Namespace::VALUE) {
        slots.value = Some(def.id);
      }
      if namespaces.contains(Namespace::NAMESPACE) {
        slots.namespace = Some(def.id);
      }
    }
    Self { by_name }
  }

  /// Resolve a name to a local def, preferring defs with presence in `ns`.
  pub fn get(&self, name: &str, ns: Namespace) -> Option<HirDefId> {
    let slots = self.by_name.get(name)?;
    let ordered = if ns == Namespace::VALUE {
      [slots.value, slots.namespace, slots.type_]
    } else {
      [slots.type_, slots.namespace, slots.value]
    };
    ordered.into_iter().flatten().next()
  }

  /// Reverse lookup: the name a local def was indexed under.
  pub fn name_of(&self, def: HirDefId) -> Option<String> {
    self.by_name.iter().find_map(|(name, slots)| {
      (slots.type_ == Some(def) || slots.value == Some(def) || slots.namespace == Some(def))
        .then(|| name.clone())
    })
  }
}

/// Namespace presence of a HIR def kind (mirrors `def_namespaces` /
/// `hir_namespaces` in `program/state`).
fn local_def_namespaces(kind: HirDefKind) -> Namespace {
  match kind {
    HirDefKind::Class | HirDefKind::Enum => Namespace::VALUE | Namespace::TYPE,
    HirDefKind::Interface | HirDefKind::TypeAlias => Namespace::TYPE,
    HirDefKind::Namespace | HirDefKind::Module => Namespace::VALUE | Namespace::NAMESPACE,
    HirDefKind::ImportBinding => Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE,
    _ => Namespace::VALUE,
  }
}

/// Lower HIR type expressions and declarations into interned types.
pub struct HirDeclLowerer<'a, 'diag> {
  store: Arc<TypeStore>,
  arenas: &'a TypeArenasByDef,
  current_arenas: Option<&'a TypeArenas>,
  semantics: Option<&'a TsProgramSemantics>,
  defs: HashMap<(FileId, String), DefId>,
  file: FileId,
  file_key: Option<FileKey>,
  local_defs: LocalDefIndex,
  diagnostics: &'diag mut Vec<Diagnostic>,
  type_params: HashMap<HirTypeParamId, TypeParamId>,
  type_param_names: HashMap<hir_js::NameId, TypeParamId>,
  next_type_param: u32,
  def_map: Option<&'a HashMap<DefId, DefId>>,
  def_by_name: Option<&'a HashMap<(FileId, String), DefId>>,
  host: Option<&'a dyn DeclHost>,
  key_to_id: Option<&'a dyn Fn(&FileKey) -> Option<FileId>>,
  module_namespace_defs: Option<&'a HashMap<FileId, DefId>>,
  value_defs: Option<&'a HashMap<DefId, DefId>>,
  /// Optional program-grade name resolver (e.g. [`crate::program::types::ProgramTypeResolver`])
  /// used for qualified / import-equals paths that the local semantic walk misses.
  type_name_resolver: Option<&'a dyn Fn(&[String]) -> Option<DefId>>,
  /// Body-check `TypeResolver` (owned/`Arc`) so lowering does not borrow a short-lived
  /// closure against the arenas lifetime.
  type_resolver: Option<Arc<dyn TypeResolver>>,
  /// Live checker bindings for `typeof x` where `x` is a body-local value (TypeId,
  /// not a module `DefId`).
  typeof_bindings: HashMap<String, TypeId>,
}

impl<'a, 'diag> HirDeclLowerer<'a, 'diag> {
  pub fn new(
    store: Arc<TypeStore>,
    arenas: &'a TypeArenasByDef,
    semantics: Option<&'a TsProgramSemantics>,
    defs: HashMap<(FileId, String), DefId>,
    file: FileId,
    file_key: Option<FileKey>,
    local_defs: LocalDefIndex,
    diagnostics: &'diag mut Vec<Diagnostic>,
    def_map: Option<&'a HashMap<DefId, DefId>>,
    def_by_name: Option<&'a HashMap<(FileId, String), DefId>>,
    host: Option<&'a dyn DeclHost>,
    key_to_id: Option<&'a dyn Fn(&FileKey) -> Option<FileId>>,
    module_namespace_defs: Option<&'a HashMap<FileId, DefId>>,
    value_defs: Option<&'a HashMap<DefId, DefId>>,
  ) -> Self {
    Self {
      store,
      arenas,
      semantics,
      defs,
      file,
      file_key,
      local_defs,
      diagnostics,
      type_params: HashMap::new(),
      type_param_names: HashMap::new(),
      next_type_param: 0,
      current_arenas: None,
      def_map,
      def_by_name,
      host,
      key_to_id,
      module_namespace_defs,
      value_defs,
      type_name_resolver: None,
      type_resolver: None,
      typeof_bindings: HashMap::new(),
    }
  }

  /// Attach a program-grade type-name resolver for qualified references.
  pub fn with_type_name_resolver(
    mut self,
    resolver: &'a dyn Fn(&[String]) -> Option<DefId>,
  ) -> Self {
    self.type_name_resolver = Some(resolver);
    self
  }

  /// Attach a body/program [`TypeResolver`] (named refs + `typeof` DefIds).
  pub fn with_type_resolver(mut self, resolver: Arc<dyn TypeResolver>) -> Self {
    self.type_resolver = Some(resolver);
    self
  }

  /// Seed body-local value bindings consulted by `typeof` queries.
  pub fn with_typeof_bindings(mut self, bindings: HashMap<String, TypeId>) -> Self {
    self.typeof_bindings = bindings;
    self
  }

  /// Seed type-parameter name → [`TypeParamId`] bindings (e.g. from the body
  /// checker's AST `TypeLowerer` scopes) so generic param/return annotations
  /// resolve to the same ids as the surrounding checker.
  pub fn with_type_param_bindings(
    mut self,
    bindings: HashMap<hir_js::NameId, TypeParamId>,
    next_type_param: u32,
  ) -> Self {
    self.type_param_names = bindings;
    self.next_type_param = next_type_param;
    self
  }

  fn arenas(&self) -> &TypeArenas {
    self
      .current_arenas
      .expect("type arenas should be set before lowering")
  }

  /// Lower a single annotation from a definition's type arenas (body checking).
  ///
  /// Used when HIR `VarDeclarator.type_annotation` / function param/return
  /// annotations are preferred over walking parse-js `TypeExpr` AST nodes.
  /// Preserves seeded [`with_type_param_bindings`] so `T` in `f<T>(x: T)`
  /// matches the body checker's type-parameter ids.
  pub fn lower_body_annotation(
    &mut self,
    owner: HirDefId,
    type_expr: TypeExprId,
    names: &hir_js::NameInterner,
  ) -> TypeId {
    self.current_arenas = self.arenas.get(&owner);
    let Some(_) = self.current_arenas else {
      return self.store.primitive_ids().unknown;
    };
    let ty = self.lower_type_expr(type_expr, names);
    self.current_arenas = None;
    ty
  }

  /// Lower a single type expression owned by `owner`'s type arenas.
  ///
  /// Used for value-side annotations stored on [`hir_js::DefData::declared_type`]
  /// (notably class fields) that are not part of a [`DefTypeInfo`] shape.
  ///
  /// When `enclosing_class` is set, that class's type parameters are registered
  /// first so annotations like `#foo: T` on `class C<T>` resolve (per-field
  /// arenas do not own the class type-parameter list).
  pub fn lower_declared_type(
    &mut self,
    owner: HirDefId,
    type_expr: TypeExprId,
    names: &hir_js::NameInterner,
  ) -> TypeId {
    self.lower_declared_type_with_class_params(owner, type_expr, None, names)
  }

  pub fn lower_declared_type_with_class_params(
    &mut self,
    owner: HirDefId,
    type_expr: TypeExprId,
    enclosing_class: Option<(HirDefId, &[HirTypeParamId])>,
    names: &hir_js::NameInterner,
  ) -> TypeId {
    self.type_params.clear();
    self.type_param_names.clear();
    self.next_type_param = 0;
    if let Some((class_owner, params)) = enclosing_class {
      if !params.is_empty() {
        self.current_arenas = self.arenas.get(&class_owner);
        if self.current_arenas.is_some() {
          let _ = self.lower_type_param_decls(params, names);
        }
      }
    }
    self.current_arenas = self.arenas.get(&owner);
    let Some(_) = self.current_arenas else {
      self.type_params.clear();
      self.type_param_names.clear();
      self.current_arenas = None;
      return self.store.primitive_ids().unknown;
    };
    let ty = self.lower_type_expr(type_expr, names);
    self.type_params.clear();
    self.type_param_names.clear();
    self.current_arenas = None;
    ty
  }

  /// Lower value-side function param/return annotations from [`FunctionData`].
  ///
  /// Missing param annotations become `any` (TS default for value signatures);
  /// missing return stays `None` so callers can infer from the body. Used by
  /// binder-seeded `FuncData` paths that no longer walk parse-js AST type
  /// expressions.
  ///
  /// `enclosing_class` seeds `class C<T>` type params for methods/constructors/
  /// accessors so `#bar(): T` / `constructor(t: T)` do not emit false TC2008.
  pub fn lower_value_function_signature(
    &mut self,
    owner: HirDefId,
    func: &FunctionData,
    body: &hir_js::Body,
    names: &hir_js::NameInterner,
  ) -> ValueFunctionSignature {
    self.lower_value_function_signature_with_class_params(owner, func, body, None, names)
  }

  pub fn lower_value_function_signature_with_class_params(
    &mut self,
    owner: HirDefId,
    func: &FunctionData,
    body: &hir_js::Body,
    enclosing_class: Option<(HirDefId, &[HirTypeParamId])>,
    names: &hir_js::NameInterner,
  ) -> ValueFunctionSignature {
    self.type_params.clear();
    self.type_param_names.clear();
    self.next_type_param = 0;
    if let Some((class_owner, params)) = enclosing_class {
      if !params.is_empty() {
        self.current_arenas = self.arenas.get(&class_owner);
        if self.current_arenas.is_some() {
          let _ = self.lower_type_param_decls(params, names);
        }
      }
    }
    self.current_arenas = self.arenas.get(&owner);
    let Some(_) = self.current_arenas else {
      self.type_params.clear();
      self.type_param_names.clear();
      self.current_arenas = None;
      return ValueFunctionSignature::default();
    };
    let type_params = self.lower_type_param_decls(&func.type_params, names);
    let prim = self.store.primitive_ids();
    let mut params = Vec::new();
    let mut param_types_for_binder = Vec::new();
    let mut this_param = None;
    for (idx, param) in func.params.iter().enumerate() {
      let name = body
        .pats
        .get(param.pat.0 as usize)
        .and_then(|pat| match &pat.kind {
          hir_js::PatKind::Ident(name_id) => names.resolve(*name_id).map(|n| n.to_string()),
          _ => None,
        });
      let annotated = param
        .type_annotation
        .map(|ann| self.lower_type_expr(ann, names));
      let mut ty = annotated.unwrap_or(prim.any);
      if param.rest {
        ty = self.normalize_rest_param_type(ty);
      }
      if idx == 0 && matches!(name.as_deref(), Some("this")) {
        this_param = Some(ty);
        continue;
      }
      param_types_for_binder.push(annotated);
      params.push(Param {
        name: name.map(|n| self.store.intern_name(n)),
        ty,
        optional: param.optional,
        rest: param.rest,
      });
    }
    let return_ann = match func.return_type {
      Some(ret_id) => {
        let ret_kind = self
          .arenas()
          .type_exprs
          .get(ret_id.0 as usize)
          .map(|expr| expr.kind.clone());
        Some(match ret_kind {
          Some(TypeExprKind::TypePredicate(pred)) => {
            self.lower_type_predicate_in_signature(&pred, &params, names)
          }
          _ => self.lower_type_expr(ret_id, names),
        })
      }
      None => None,
    };
    self.type_params.clear();
    self.type_param_names.clear();
    self.current_arenas = None;
    ValueFunctionSignature {
      params,
      return_ann,
      type_params,
      this_param,
      param_types_for_binder,
    }
  }

  pub fn lower_type_info(
    &mut self,
    owner: HirDefId,
    info: &DefTypeInfo,
    names: &hir_js::NameInterner,
  ) -> (TypeId, Vec<TypeParamDecl>) {
    self.type_params.clear();
    self.type_param_names.clear();
    self.next_type_param = 0;
    self.current_arenas = self.arenas.get(&owner);
    let Some(_) = self.current_arenas else {
      return (self.store.primitive_ids().unknown, Vec::new());
    };
    let result = match info {
      DefTypeInfo::TypeAlias {
        type_expr,
        type_params,
      } => {
        let params = self.lower_type_param_decls(type_params, names);
        let ty = self.lower_type_expr(*type_expr, names);
        self.validate_variance_annotations(type_params, ty, names);
        (ty, params)
      }
      DefTypeInfo::Interface {
        type_params,
        extends,
        members,
      } => {
        let params = self.lower_type_param_decls(type_params, names);
        let own = self.lower_interface_own_object(members, names);
        let mut types: Vec<TypeId> = Vec::new();
        if let Some(own) = own {
          types.push(own);
        }

        for base in extends.iter() {
          types.push(self.lower_type_expr(*base, names));
        }

        let ty = match types.len() {
          // Empty interfaces still contribute an object-like type. Returning
          // `any` here makes declaration merging lossy: many upstream lib
          // augmentations only contain computed properties (e.g.
          // `[Symbol.toStringTag]`), which we currently skip lowering. Treat
          // those as empty object types so later merges with the "real" shape
          // (e.g. `Promise.then`) remain intact.
          0 => {
            let shape_id = self.store.intern_shape(Shape::new());
            let obj = self.store.intern_object(ObjectType { shape: shape_id });
            self.store.intern_type(TypeKind::Object(obj))
          }
          1 => types[0],
          _ => self.store.intersection(types),
        };
        self.validate_variance_annotations(type_params, ty, names);
        (ty, params)
      }
      DefTypeInfo::Class { type_params, .. } => {
        let class_name = self.local_defs.name_of(owner);
        let (params, jsdoc_tp_map) =
          self.class_type_param_decls(type_params, names, class_name.as_deref());
        let (instance, _value) = self.lower_class_instance_and_value(
          owner,
          info,
          names,
          self.store.primitive_ids().unknown,
          class_name.as_deref(),
          &params,
          &jsdoc_tp_map,
        );
        self.validate_variance_annotations(type_params, instance, names);
        (instance, params)
      }
      DefTypeInfo::Enum { .. } => (self.lower_enum_type(info, names), Vec::new()),
      DefTypeInfo::Namespace { .. } => (self.store.primitive_ids().unknown, Vec::new()),
    };
    self.type_params.clear();
    self.type_param_names.clear();
    self.current_arenas = None;
    result
  }

  fn lower_interface_own_object(
    &mut self,
    members: &[TypeMemberId],
    names: &hir_js::NameInterner,
  ) -> Option<TypeId> {
    let mut shape = Shape::new();
    for member in members.iter() {
      self.lower_member(&mut shape, *member, names);
    }
    if shape.properties.is_empty()
      && shape.call_signatures.is_empty()
      && shape.construct_signatures.is_empty()
      && shape.indexers.is_empty()
    {
      return None;
    }
    let shape_id = self.store.intern_shape(shape);
    let obj = self.store.intern_object(ObjectType { shape: shape_id });
    Some(self.store.intern_type(TypeKind::Object(obj)))
  }

  pub fn lower_class_instance_and_value_types(
    &mut self,
    owner: HirDefId,
    info: &DefTypeInfo,
    names: &hir_js::NameInterner,
  ) -> Option<(TypeId, TypeId, Vec<TypeParamDecl>)> {
    self.type_params.clear();
    self.type_param_names.clear();
    self.current_arenas = self.arenas.get(&owner);
    let Some(_) = self.current_arenas else {
      self.current_arenas = None;
      return None;
    };

    let DefTypeInfo::Class { type_params, .. } = info else {
      self.current_arenas = None;
      return None;
    };
    let unknown = self.store.primitive_ids().unknown;
    let class_name = self.local_defs.name_of(owner);
    let (params, jsdoc_tp_map) =
      self.class_type_param_decls(type_params, names, class_name.as_deref());
    let (instance, value) = self.lower_class_instance_and_value(
      owner,
      info,
      names,
      unknown,
      class_name.as_deref(),
      &params,
      &jsdoc_tp_map,
    );
    self.validate_variance_annotations(type_params, instance, names);

    self.type_params.clear();
    self.type_param_names.clear();
    self.current_arenas = None;
    Some((instance, value, params))
  }

  pub fn lower_enum_type_and_value(
    &mut self,
    owner: HirDefId,
    info: &DefTypeInfo,
    names: &hir_js::NameInterner,
  ) -> Option<(TypeId, TypeId)> {
    self.current_arenas = self.arenas.get(&owner);
    let Some(_) = self.current_arenas else {
      self.current_arenas = None;
      return None;
    };
    let value = self.lower_enum_value(owner, info, names);
    let ty = self.lower_enum_type(info, names);
    self.current_arenas = None;
    Some((ty, value))
  }

  fn lower_enum_type(&mut self, info: &DefTypeInfo, _names: &hir_js::NameInterner) -> TypeId {
    let prim = self.store.primitive_ids();
    let DefTypeInfo::Enum { members } = info else {
      return prim.any;
    };
    // Prefer a union of member literals so `Record<E, T>` / mapped types get
    // required properties (`assignmentCompatWithEnumIndexer.ts`). Fall back to
    // the coarse number/string union when any member is computed.
    let mut lits = Vec::with_capacity(members.len());
    let mut has_number = false;
    let mut has_string = false;
    let mut has_computed = false;
    for member in members.iter() {
      match &member.value {
        hir_js::EnumMemberValue::Number(n) => {
          has_number = true;
          lits.push(
            self
              .store
              .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(*n))),
          );
        }
        hir_js::EnumMemberValue::String(s) => {
          has_string = true;
          let name = self.store.intern_name(s.clone());
          lits.push(self.store.intern_type(TypeKind::StringLiteral(name)));
        }
        hir_js::EnumMemberValue::Computed => {
          has_computed = true;
          has_number = true;
          has_string = true;
        }
      }
    }
    if !has_computed && !lits.is_empty() {
      return self.store.union(lits);
    }
    match (has_number, has_string) {
      (true, true) => self.store.union(vec![prim.number, prim.string]),
      (true, false) => prim.number,
      (false, true) => prim.string,
      (false, false) => prim.any,
    }
  }

  fn lower_enum_value(
    &mut self,
    owner: HirDefId,
    info: &DefTypeInfo,
    names: &hir_js::NameInterner,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    let DefTypeInfo::Enum { members } = info else {
      return prim.unknown;
    };
    // Member access `E.A` is typed as the enum type (tsc), not the underlying
    // literal — otherwise distinct enums that share member values (both `0`)
    // become mutually assignable and first-match overloads pick the wrong sig.
    let ref_def = self
      .def_map
      .and_then(|m| m.get(&owner).copied())
      .unwrap_or(owner);
    let enum_ty = self.store.intern_type(TypeKind::Ref {
      def: ref_def,
      args: Vec::new(),
    });
    let mut shape = Shape::new();
    for member in members.iter() {
      let Some(name) = names.resolve(member.name) else {
        continue;
      };
      let key = PropKey::String(self.store.intern_name(name.to_string()));
      let ty = match &member.value {
        hir_js::EnumMemberValue::Number(_) | hir_js::EnumMemberValue::String(_) => enum_ty,
        hir_js::EnumMemberValue::Computed => prim.any,
      };
      shape.properties.push(Property {
        key,
        data: PropData {
          ty,
          optional: false,
          readonly: true,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      });
    }
    let shape_id = self.store.intern_shape(shape);
    let obj = self.store.intern_object(ObjectType { shape: shape_id });
    self.store.intern_type(TypeKind::Object(obj))
  }

  /// Lower HIR class type params, falling back to checkJs `@template` tags when
  /// the class has no TS type-parameter list.
  fn class_type_param_decls(
    &mut self,
    hir_params: &[HirTypeParamId],
    names: &hir_js::NameInterner,
    class_name: Option<&str>,
  ) -> (Vec<TypeParamDecl>, HashMap<String, TypeParamId>) {
    let mut params = self.lower_type_param_decls(hir_params, names);
    let mut jsdoc_tp_map = HashMap::new();
    if !params.is_empty() {
      // HIR params already registered in `type_param_names`; expose a string map
      // so JSDoc `@param {T}` on constructors can resolve the same ids.
      for tp in hir_params.iter() {
        let Some(data) = self.arenas().type_params.get(tp.0 as usize) else {
          continue;
        };
        let Some(name) = names.resolve(data.name) else {
          continue;
        };
        if let Some(id) = self.type_params.get(tp).copied() {
          jsdoc_tp_map.insert(name.to_owned(), id);
        }
      }
      return (params, jsdoc_tp_map);
    }
    let Some(class_name) = class_name else {
      return (params, jsdoc_tp_map);
    };
    let Some(host) = self.host else {
      return (params, jsdoc_tp_map);
    };
    let Some(file_key) = self.file_key.as_ref() else {
      return (params, jsdoc_tp_map);
    };
    let Ok(source) = host.file_text(file_key) else {
      return (params, jsdoc_tp_map);
    };
    let Some(tags) = crate::jsdoc::class_leading_jsdoc_tags(source.as_ref(), class_name) else {
      return (params, jsdoc_tp_map);
    };
    if tags.templates.is_empty() {
      return (params, jsdoc_tp_map);
    }
    // Two-pass: allocate names first so constraints may reference siblings.
    for t in tags.templates.iter() {
      let id = TypeParamId(self.next_type_param);
      self.next_type_param = self.next_type_param.wrapping_add(1);
      jsdoc_tp_map.insert(t.name.to_owned(), id);
      params.push(TypeParamDecl {
        id,
        constraint: None,
        default: None,
        variance: None,
        const_: false,
      });
    }
    let typedefs = crate::jsdoc::collect_file_typedefs(source.as_ref());
    let env = crate::jsdoc::JsdocLowerEnv::new()
      .with_typedefs((!typedefs.is_empty()).then_some(&typedefs))
      .with_type_params(Some(&jsdoc_tp_map));
    for (decl, t) in params.iter_mut().zip(tags.templates.iter()) {
      if let Some(raw) = t.constraint {
        decl.constraint = Some(crate::jsdoc::lower_jsdoc_type_with(
          self.store.as_ref(),
          raw,
          &env,
        ));
      }
    }
    (params, jsdoc_tp_map)
  }

  fn lower_class_instance_and_value(
    &mut self,
    owner: HirDefId,
    info: &DefTypeInfo,
    names: &hir_js::NameInterner,
    unknown: TypeId,
    class_name: Option<&str>,
    class_type_params: &[TypeParamDecl],
    jsdoc_tp_map: &HashMap<String, TypeParamId>,
  ) -> (TypeId, TypeId) {
    let DefTypeInfo::Class {
      extends,
      implements: _,
      members,
      ..
    } = info
    else {
      return (unknown, unknown);
    };

    let mut instance_shape = Shape::new();
    let mut static_shape = Shape::new();
    let mut ctor_signatures: Vec<TypeSignature> = Vec::new();

    for member in members.iter() {
      match &member.kind {
        hir_js::ClassMemberSigKind::Constructor(sig) => {
          ctor_signatures.push(sig.clone());
        }
        hir_js::ClassMemberSigKind::CallSignature(sig) => {
          let lowered = self.lower_signature(sig, names);
          let sig_id = self.store.intern_signature(lowered);
          if member.static_ {
            static_shape.call_signatures.push(sig_id);
          } else {
            instance_shape.call_signatures.push(sig_id);
          }
        }
        hir_js::ClassMemberSigKind::IndexSignature(idx) => {
          let key_type = self.lower_type_expr(idx.parameter_type, names);
          let value_type = self.lower_type_expr(idx.type_annotation, names);
          let indexer = Indexer {
            key_type,
            value_type,
            readonly: idx.readonly,
          };
          if member.static_ {
            static_shape.indexers.push(indexer);
          } else {
            instance_shape.indexers.push(indexer);
          }
        }
        hir_js::ClassMemberSigKind::Field {
          name,
          type_annotation,
        } => {
          let Some(key) = self.prop_key_from_name(name, names) else {
            continue;
          };
          let ty = type_annotation
            .map(|t| self.lower_type_expr(t, names))
            .unwrap_or(unknown);
          let (accessibility, declared_on) =
            self.class_member_prop_access(name, names, member.accessibility, owner);
          let prop = Property {
            key,
            data: PropData {
              ty,
              optional: member.optional,
              readonly: member.readonly,
              accessibility,
              is_method: false,
              origin: None,
              declared_on,
            },
          };
          if member.static_ {
            static_shape.properties.push(prop);
          } else {
            instance_shape.properties.push(prop);
          }
        }
        hir_js::ClassMemberSigKind::Method { name, signature } => {
          let Some(key) = self.prop_key_from_name(name, names) else {
            continue;
          };
          let sig = self.lower_signature(signature, names);
          let sig_id = self.store.intern_signature(sig);
          let ty = self.store.intern_type(TypeKind::Callable {
            overloads: vec![sig_id],
          });
          let (accessibility, declared_on) =
            self.class_member_prop_access(name, names, member.accessibility, owner);
          let prop = Property {
            key,
            data: PropData {
              ty,
              optional: member.optional,
              readonly: member.readonly,
              accessibility,
              is_method: true,
              origin: None,
              declared_on,
            },
          };
          if member.static_ {
            static_shape.properties.push(prop);
          } else {
            instance_shape.properties.push(prop);
          }
        }
        hir_js::ClassMemberSigKind::Getter { name, return_type } => {
          let Some(key) = self.prop_key_from_name(name, names) else {
            continue;
          };
          let ty = return_type
            .map(|t| self.lower_type_expr(t, names))
            .unwrap_or(unknown);
          let (accessibility, declared_on) =
            self.class_member_prop_access(name, names, member.accessibility, owner);
          let prop = Property {
            key,
            data: PropData {
              ty,
              optional: member.optional,
              readonly: true,
              accessibility,
              is_method: false,
              origin: None,
              declared_on,
            },
          };
          if member.static_ {
            static_shape.properties.push(prop);
          } else {
            instance_shape.properties.push(prop);
          }
        }
        hir_js::ClassMemberSigKind::Setter { name, parameter } => {
          let Some(key) = self.prop_key_from_name(name, names) else {
            continue;
          };
          let ty = self.lower_type_expr(parameter.ty, names);
          let (accessibility, declared_on) =
            self.class_member_prop_access(name, names, member.accessibility, owner);
          let prop = Property {
            key,
            data: PropData {
              ty,
              optional: member.optional || parameter.optional,
              readonly: false,
              accessibility,
              is_method: false,
              origin: None,
              declared_on,
            },
          };
          if member.static_ {
            static_shape.properties.push(prop);
          } else {
            instance_shape.properties.push(prop);
          }
        }
      }
    }

    // checkJs: `this.prop = …` in constructors adds instance properties.
    self.merge_js_class_this_props(
      class_name,
      &ctor_signatures,
      names,
      &mut instance_shape,
      unknown,
      jsdoc_tp_map,
    );

    let instance_obj = self
      .store
      .intern_type(TypeKind::Object(self.store.intern_object(ObjectType {
        shape: self.store.intern_shape(instance_shape),
      })));
    let mut instance_parts = vec![instance_obj];
    if let Some(ext) = extends {
      instance_parts.push(self.lower_type_expr(*ext, names));
    }
    let instance = if instance_parts.len() == 1 {
      instance_parts[0]
    } else {
      self.store.intersection(instance_parts)
    };

    let mut ctor_sig_ids: Vec<types_ts_interned::SignatureId> = Vec::new();
    for sig in ctor_signatures.iter() {
      let mut lowered = self.lower_signature(sig, names);
      self.apply_jsdoc_constructor_param_types(&mut lowered, class_name, jsdoc_tp_map);
      // Class type parameters belong on the construct signature so `new Foo(arg)`
      // can infer/instantiate them (tsc / checkJs `@template` parity).
      if lowered.type_params.is_empty() && !class_type_params.is_empty() {
        lowered.type_params = class_type_params.to_vec();
      }
      lowered.ret = instance;
      lowered.this_param = None;
      ctor_sig_ids.push(self.store.intern_signature(lowered));
    }
    if ctor_sig_ids.is_empty() {
      let sig = Signature {
        params: Vec::new(),
        ret: instance,
        type_params: class_type_params.to_vec(),
        this_param: None,
      };
      ctor_sig_ids.push(self.store.intern_signature(sig));
    }
    static_shape.construct_signatures.extend(ctor_sig_ids);

    let value = self
      .store
      .intern_type(TypeKind::Object(self.store.intern_object(ObjectType {
        shape: self.store.intern_shape(static_shape),
      })));

    (instance, value)
  }

  /// Overlay checkJs constructor `@param {T} name` types onto a lowered
  /// construct signature (and resolve `@template` names via `jsdoc_tp_map`).
  fn apply_jsdoc_constructor_param_types(
    &self,
    sig: &mut Signature,
    class_name: Option<&str>,
    jsdoc_tp_map: &HashMap<String, TypeParamId>,
  ) {
    let Some(class_name) = class_name else {
      return;
    };
    let Some(host) = self.host else {
      return;
    };
    let Some(file_key) = self.file_key.as_ref() else {
      return;
    };
    let Ok(source) = host.file_text(file_key) else {
      return;
    };
    let Some(tags) = crate::jsdoc::constructor_leading_jsdoc_tags(source.as_ref(), class_name)
    else {
      return;
    };
    if tags.params.is_empty() {
      return;
    }
    let typedefs = crate::jsdoc::collect_file_typedefs(source.as_ref());
    let env = crate::jsdoc::JsdocLowerEnv::new()
      .with_typedefs((!typedefs.is_empty()).then_some(&typedefs))
      .with_type_params((!jsdoc_tp_map.is_empty()).then_some(jsdoc_tp_map));
    let owned: Vec<crate::jsdoc::OwnedJsdocParam> = tags
      .params
      .iter()
      .map(|p| crate::jsdoc::OwnedJsdocParam {
        ty: p.ty.to_owned(),
        name: p.name.map(str::to_owned),
        optional: p.optional,
      })
      .collect();
    let (resolved, _) = crate::jsdoc::resolve_jsdoc_params(self.store.as_ref(), &owned, &env);
    for p in sig.params.iter_mut() {
      let Some(name_id) = p.name else {
        continue;
      };
      let name = self.store.name(name_id);
      if let Some(resolved) = resolved.get(&name) {
        p.ty = resolved.ty;
        p.optional = p.optional || resolved.optional;
      }
    }
  }

  /// Merge `this.prop = rhs` assignments from a JS class constructor into the
  /// instance shape (checkJs). Property types come from matching constructor
  /// parameter names when possible (including JSDoc `@param` overlays).
  fn merge_js_class_this_props(
    &mut self,
    class_name: Option<&str>,
    ctor_signatures: &[TypeSignature],
    names: &hir_js::NameInterner,
    instance_shape: &mut Shape,
    fallback: TypeId,
    jsdoc_tp_map: &HashMap<String, TypeParamId>,
  ) {
    let Some(class_name) = class_name else {
      return;
    };
    let Some(host) = self.host else {
      return;
    };
    let Some(file_key) = self.file_key.as_ref() else {
      return;
    };
    let Ok(source) = host.file_text(file_key) else {
      return;
    };
    let map = crate::jsdoc::collect_js_class_this_props(&source);
    let Some(props) = map.get(class_name) else {
      return;
    };
    // Map constructor param name → type (first ctor sig wins).
    let mut param_tys: HashMap<String, TypeId> = HashMap::new();
    if let Some(sig) = ctor_signatures.first() {
      let mut lowered = self.lower_signature(sig, names);
      self.apply_jsdoc_constructor_param_types(&mut lowered, Some(class_name), jsdoc_tp_map);
      for p in lowered.params.iter() {
        if let Some(name_id) = p.name {
          let name = self.store.name(name_id);
          if !name.is_empty() {
            param_tys.insert(name, p.ty);
          }
        }
      }
    }
    let existing: HashSet<String> = instance_shape
      .properties
      .iter()
      .filter_map(|p| match &p.key {
        PropKey::String(id) => {
          let n = self.store.name(*id);
          (!n.is_empty()).then_some(n)
        }
        _ => None,
      })
      .collect();
    for (prop, rhs) in props.iter() {
      if existing.contains(prop) {
        continue;
      }
      let ty = param_tys.get(rhs).copied().unwrap_or(fallback);
      instance_shape.properties.push(Property {
        key: PropKey::String(self.store.intern_name(prop.clone())),
        data: PropData {
          ty,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      });
    }
  }

  fn prop_key_from_name(
    &mut self,
    name: &hir_js::PropertyName,
    names: &hir_js::NameInterner,
  ) -> Option<PropKey> {
    match name {
      hir_js::PropertyName::Ident(id) => {
        let name = names.resolve(*id)?;
        let interned = self.store.intern_name(name.to_string());
        if name.starts_with("Symbol.") {
          Some(PropKey::Symbol(interned))
        } else {
          Some(PropKey::String(interned))
        }
      }
      hir_js::PropertyName::String(s) => Some(PropKey::String(self.store.intern_name(s.clone()))),
      hir_js::PropertyName::Number(n) => Some(match n.parse::<i64>() {
        Ok(parsed) => PropKey::Number(parsed),
        // Fractional numeric keys are string keys (`{ 1.1: string }`) — never
        // drop the member (`objectTypeWithNumericProperty.ts`).
        Err(_) => PropKey::String(self.store.intern_name(n.clone())),
      }),
      hir_js::PropertyName::Symbol(id) => Some(PropKey::Symbol(
        self.store.intern_name(names.resolve(*id)?.to_string()),
      )),
      hir_js::PropertyName::Computed => None,
    }
  }

  fn map_value_def(&self, def: DefId) -> DefId {
    self
      .value_defs
      .and_then(|map| map.get(&def).copied())
      .unwrap_or(def)
  }

  fn lower_type_expr(&mut self, id: TypeExprId, names: &hir_js::NameInterner) -> TypeId {
    let Some(ty) = self.arenas().type_exprs.get(id.0 as usize).cloned() else {
      return self.store.primitive_ids().unknown;
    };
    match ty.kind {
      TypeExprKind::Any => self.store.primitive_ids().any,
      TypeExprKind::Unknown => self.store.primitive_ids().unknown,
      TypeExprKind::Never => self.store.primitive_ids().never,
      TypeExprKind::Void => self.store.primitive_ids().void,
      TypeExprKind::Null => self.store.primitive_ids().null,
      TypeExprKind::Undefined => self.store.primitive_ids().undefined,
      TypeExprKind::Intrinsic => self.store.primitive_ids().unknown,
      TypeExprKind::Object => {
        let shape = Shape::new();
        let shape_id = self.store.intern_shape(shape);
        let obj = self.store.intern_object(ObjectType { shape: shape_id });
        self.store.intern_type(TypeKind::Object(obj))
      }
      TypeExprKind::Boolean => self.store.primitive_ids().boolean,
      TypeExprKind::Number => self.store.primitive_ids().number,
      TypeExprKind::String => self.store.primitive_ids().string,
      TypeExprKind::BigInt => self.store.primitive_ids().bigint,
      TypeExprKind::Symbol => self.store.primitive_ids().symbol,
      TypeExprKind::UniqueSymbol => self.store.primitive_ids().unique_symbol,
      TypeExprKind::This => self.store.intern_type(TypeKind::This),
      TypeExprKind::Literal(lit) => match lit {
        hir_js::TypeLiteral::Boolean(b) => self.store.intern_type(TypeKind::BooleanLiteral(b)),
        hir_js::TypeLiteral::Number(n) => {
          let parsed = n.parse::<f64>().unwrap_or(0.0);
          self
            .store
            .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(parsed)))
        }
        hir_js::TypeLiteral::String(s) => {
          let name = self.store.intern_name(s.clone());
          self.store.intern_type(TypeKind::StringLiteral(name))
        }
        hir_js::TypeLiteral::BigInt(n) => {
          let trimmed = n.trim_end_matches('n');
          let value = trimmed.parse::<BigInt>().unwrap_or_default();
          self.store.intern_type(TypeKind::BigIntLiteral(value))
        }
        hir_js::TypeLiteral::Null => self.store.primitive_ids().null,
      },
      TypeExprKind::Array(arr) => {
        let elem = self.lower_type_expr(arr.element, names);
        self.store.intern_type(TypeKind::Array {
          ty: elem,
          readonly: arr.readonly,
        })
      }
      TypeExprKind::Tuple(tuple) => {
        let mut elems = Vec::new();
        for elem in tuple.elements.iter() {
          elems.push(TupleElem {
            ty: self.lower_type_expr(elem.ty, names),
            optional: elem.optional,
            rest: elem.rest,
            readonly: tuple.readonly,
          });
        }
        self.store.intern_type(TypeKind::Tuple(elems))
      }
      TypeExprKind::Union(members) => {
        let lowered = members
          .iter()
          .map(|m| self.lower_type_expr(*m, names))
          .collect();
        self.store.union(lowered)
      }
      TypeExprKind::Intersection(members) => {
        let lowered = members
          .iter()
          .map(|m| self.lower_type_expr(*m, names))
          .collect();
        self.store.intersection(lowered)
      }
      TypeExprKind::Function(func) => {
        let sig = self.lower_function_type(&func, names);
        let sig_id = self.store.intern_signature(sig);
        self.store.intern_type(TypeKind::Callable {
          overloads: vec![sig_id],
        })
      }
      TypeExprKind::Constructor(func) => {
        // `new (x: T) => R` is a construct signature, not a call signature
        // (`assignmentCompatWithConstructSignatures*.ts`).
        let sig = self.lower_function_type(&func, names);
        let sig_id = self.store.intern_signature(sig);
        let mut shape = Shape::new();
        shape.construct_signatures.push(sig_id);
        let shape_id = self.store.intern_shape(shape);
        let obj = self.store.intern_object(ObjectType { shape: shape_id });
        self.store.intern_type(TypeKind::Object(obj))
      }
      TypeExprKind::TypeLiteral(obj) => {
        if obj.members.is_empty() {
          self.store.intern_type(TypeKind::EmptyObject)
        } else {
          let mut shape = Shape::new();
          for member in obj.members.iter() {
            self.lower_member(&mut shape, *member, names);
          }
          let shape_id = self.store.intern_shape(shape);
          let obj = self.store.intern_object(ObjectType { shape: shape_id });
          self.store.intern_type(TypeKind::Object(obj))
        }
      }
      TypeExprKind::Parenthesized(inner) => self.lower_type_expr(inner, names),
      TypeExprKind::TypeRef(r) => self.lower_type_ref(&r, names, ty.span),
      TypeExprKind::TypeQuery(name) => self.lower_type_query(&name, names),
      TypeExprKind::KeyOf(inner) => {
        let ty = self.lower_type_expr(inner, names);
        self.store.intern_type(TypeKind::KeyOf(ty))
      }
      TypeExprKind::IndexedAccess {
        object_type,
        index_type,
      } => {
        let obj = self.lower_type_expr(object_type, names);
        let idx = self.lower_type_expr(index_type, names);
        // ES private fields are not visible to string indexed access
        // (`C["#bar"]` → TS2339), even though the shape stores `#bar`.
        if let Some(prop) = self.private_ident_string_index_prop(index_type) {
          let index_span = self
            .current_arenas
            .and_then(|a| a.type_exprs.get(index_type.0 as usize))
            .map(|t| t.span)
            .unwrap_or(ty.span);
          let obj_display = TypeDisplay::new(self.store.as_ref(), obj).to_string();
          self.diagnostics.push(codes::PROPERTY_DOES_NOT_EXIST.error(
            format!("Property '{prop}' does not exist on type '{obj_display}'."),
            Span {
              file: self.file,
              range: index_span,
            },
          ));
          // tsc recovers with an error type (assignment does not cascade TS2322).
          return self.store.primitive_ids().any;
        }
        self
          .store
          .intern_type(TypeKind::IndexedAccess { obj, index: idx })
      }
      TypeExprKind::Conditional(cond) => {
        let distributive = self.is_naked_type_param(cond.check_type);
        let prev_params = self.type_params.clone();
        let prev_names = self.type_param_names.clone();
        let check = self.lower_type_expr(cond.check_type, names);
        let extends = self.lower_type_expr(cond.extends_type, names);
        let true_ty = self.lower_type_expr(cond.true_type, names);
        let false_ty = self.lower_type_expr(cond.false_type, names);
        self.type_params = prev_params;
        self.type_param_names = prev_names;
        self.store.intern_type(TypeKind::Conditional {
          check,
          extends,
          true_ty,
          false_ty,
          distributive,
        })
      }
      TypeExprKind::Mapped(mapped) => self.lower_mapped_type(&mapped, names),
      TypeExprKind::TemplateLiteral(tpl) => {
        let mut spans = Vec::new();
        for span in tpl.spans.iter() {
          spans.push(types_ts_interned::TemplateChunk {
            literal: span.literal.clone(),
            ty: self.lower_type_expr(span.type_expr, names),
          });
        }
        self.store.intern_type(TypeKind::TemplateLiteral(
          types_ts_interned::TemplateLiteralType {
            head: tpl.head,
            spans,
          },
        ))
      }
      TypeExprKind::Infer(param) => self.lower_infer_type(param, names),
      TypeExprKind::TypePredicate(pred) => {
        let asserted = pred
          .type_annotation
          .map(|ty| self.lower_type_expr(ty, names));
        let parameter = names
          .resolve(pred.parameter)
          .and_then(|name| (name == "this").then_some(PredicateParam::This));
        self.store.intern_type(TypeKind::Predicate {
          parameter,
          asserted,
          asserts: pred.asserts,
        })
      }
      TypeExprKind::Import(import) => self.lower_import_type(&import, names),
    }
  }

  fn lower_mapped_type(
    &mut self,
    mapped: &hir_js::TypeMapped,
    names: &hir_js::NameInterner,
  ) -> TypeId {
    let tp = self.alloc_type_param(mapped.type_param);
    let constraint = self.lower_type_expr(mapped.constraint, names);
    let value = self.lower_type_expr(mapped.value_type, names);
    let name_type = mapped
      .name_type
      .as_ref()
      .map(|n| self.lower_type_expr(*n, names));
    let mapped_kind = MappedType {
      param: tp,
      source: constraint,
      value,
      readonly: self.map_modifier(mapped.readonly),
      optional: self.map_modifier(mapped.optional),
      name_type,
      as_type: name_type,
      homomorphic_var: MappedType::homomorphic_var_of(&self.store, constraint),
    };
    let mapped_ty = self.store.intern_type(TypeKind::Mapped(mapped_kind));
    mapped_ty
  }

  fn lower_infer_type(&mut self, id: HirTypeParamId, names: &hir_js::NameInterner) -> TypeId {
    let param = self.alloc_type_param(id);
    let constraint = self
      .arenas()
      .type_params
      .get(id.0 as usize)
      .and_then(|tp| tp.constraint)
      .map(|c| self.lower_type_expr(c, names));
    self
      .store
      .intern_type(TypeKind::Infer { param, constraint })
  }

  fn is_naked_type_param(&self, expr: TypeExprId) -> bool {
    let ty = &self.arenas().type_exprs[expr.0 as usize];
    match &ty.kind {
      TypeExprKind::TypeRef(reference) if reference.type_args.is_empty() => {
        matches!(
          reference.name,
          TypeName::Ident(name) if self.type_param_names.contains_key(&name)
        )
      }
      _ => false,
    }
  }

  fn lower_function_type(
    &mut self,
    func: &hir_js::TypeFunction,
    names: &hir_js::NameInterner,
  ) -> Signature {
    let prev_params = self.type_params.clone();
    let prev_names = self.type_param_names.clone();
    let type_params = self.lower_type_param_decls(&func.type_params, names);
    let (this_param, params) = self.lower_fn_params(&func.params, names);
    let ret_kind = self
      .arenas()
      .type_exprs
      .get(func.ret.0 as usize)
      .map(|expr| expr.kind.clone());
    let ret = match ret_kind {
      Some(TypeExprKind::TypePredicate(pred)) => {
        self.lower_type_predicate_in_signature(&pred, &params, names)
      }
      _ => self.lower_type_expr(func.ret, names),
    };
    let sig = Signature {
      params,
      ret,
      type_params,
      this_param,
    };
    self.type_params = prev_params;
    self.type_param_names = prev_names;
    sig
  }

  fn lower_type_predicate_in_signature(
    &mut self,
    pred: &hir_js::TypePredicate,
    params: &[Param],
    names: &hir_js::NameInterner,
  ) -> TypeId {
    let asserted = pred
      .type_annotation
      .map(|ty| self.lower_type_expr(ty, names));
    let parameter = names.resolve(pred.parameter).and_then(|name| {
      if name == "this" {
        return Some(PredicateParam::This);
      }
      let name_id = self.store.intern_name(name.to_string());
      params
        .iter()
        .position(|param| param.name == Some(name_id))
        .map(|idx| PredicateParam::Param(idx as u32))
    });
    self.store.intern_type(TypeKind::Predicate {
      parameter,
      asserted,
      asserts: pred.asserts,
    })
  }

  fn map_modifier(&self, modifier: Option<hir_js::TypeMappedModifier>) -> MappedModifier {
    match modifier {
      None => MappedModifier::Preserve,
      Some(hir_js::TypeMappedModifier::Plus) => MappedModifier::Add,
      Some(hir_js::TypeMappedModifier::Minus) => MappedModifier::Remove,
      Some(hir_js::TypeMappedModifier::None) => MappedModifier::Add,
    }
  }

  fn alloc_type_param(&mut self, id: HirTypeParamId) -> TypeParamId {
    if let Some(existing) = self.type_params.get(&id) {
      return *existing;
    }
    let new_id = TypeParamId(self.next_type_param);
    self.next_type_param = self.next_type_param.wrapping_add(1);
    self.type_params.insert(id, new_id);
    if let Some(param) = self.arenas().type_params.get(id.0 as usize) {
      self.type_param_names.insert(param.name, new_id);
    }
    new_id
  }

  fn lower_type_param_decls(
    &mut self,
    params: &[HirTypeParamId],
    names: &hir_js::NameInterner,
  ) -> Vec<TypeParamDecl> {
    for tp in params.iter() {
      self.alloc_type_param(*tp);
    }
    params
      .iter()
      .filter_map(|id| {
        let (constraint, default, variance, const_) = {
          let data = self.arenas().type_params.get(id.0 as usize)?;
          (data.constraint, data.default, data.variance, data.const_)
        };
        let mapped = *self.type_params.get(id)?;
        let constraint = constraint.map(|c| self.lower_type_expr(c, names));
        let default = default.map(|d| self.lower_type_expr(d, names));
        let variance = variance.map(|variance| match variance {
          hir_js::TypeVariance::In => TypeParamVariance::In,
          hir_js::TypeVariance::Out => TypeParamVariance::Out,
          hir_js::TypeVariance::InOut => TypeParamVariance::InOut,
        });
        Some(TypeParamDecl {
          id: mapped,
          constraint,
          default,
          variance,
          const_,
        })
      })
      .collect()
  }

  fn validate_variance_annotations(
    &mut self,
    params: &[HirTypeParamId],
    ty: TypeId,
    names: &hir_js::NameInterner,
  ) {
    const OUT: u8 = 1;
    const IN: u8 = 2;

    let mut declared: Vec<(TypeParamId, TypeParamVariance, TextRange, String)> = Vec::new();
    for hir_id in params.iter() {
      let Some(data) = self.arenas().type_params.get(hir_id.0 as usize) else {
        continue;
      };
      let Some(variance) = data.variance else {
        continue;
      };
      let Some(mapped) = self.type_params.get(hir_id).copied() else {
        continue;
      };
      let name = names
        .resolve(data.name)
        .map(|n| n.to_string())
        .unwrap_or_default();
      let mut span = data.span;
      if let (Some(host), Some(file_key)) = (self.host, self.file_key.as_ref()) {
        if let Ok(text) = host.file_text(file_key) {
          let end = span.end as usize;
          if end > 0 && end <= text.len() {
            match text.as_bytes()[end - 1] {
              b'>' | b',' => span.end = span.end.saturating_sub(1),
              _ => {}
            }
          }
        }
      }
      let variance = match variance {
        hir_js::TypeVariance::In => TypeParamVariance::In,
        hir_js::TypeVariance::Out => TypeParamVariance::Out,
        hir_js::TypeVariance::InOut => TypeParamVariance::InOut,
      };
      declared.push((mapped, variance, span, name));
    }
    if declared.is_empty() {
      return;
    }

    let mut usage: HashMap<TypeParamId, u8> = HashMap::new();
    let mut visited: std::collections::HashSet<(TypeId, u8)> = std::collections::HashSet::new();
    self.collect_variance_usage(ty, OUT, &mut usage, &mut visited);

    for (param_id, expected, span, name) in declared {
      let actual = usage.get(&param_id).copied().unwrap_or(0);
      let ok = match expected {
        TypeParamVariance::Out => (actual & IN) == 0,
        TypeParamVariance::In => (actual & OUT) == 0,
        TypeParamVariance::InOut => true,
      };
      if ok {
        continue;
      }
      let expected_str = match expected {
        TypeParamVariance::Out => "out",
        TypeParamVariance::In => "in",
        TypeParamVariance::InOut => "in out",
      };
      let actual_str = match actual {
        0 => "it is never used",
        OUT => "it is only used covariantly",
        IN => "it is only used contravariantly",
        _ => "it is used in both covariant and contravariant positions",
      };
      self
        .diagnostics
        .push(codes::INVALID_VARIANCE_ANNOTATION.error(
          format!("Type parameter '{name}' is declared as '{expected_str}', but {actual_str}."),
          Span::new(self.file, span),
        ));
    }
  }

  fn collect_variance_usage(
    &self,
    ty: TypeId,
    position: u8,
    usage: &mut HashMap<TypeParamId, u8>,
    visited: &mut std::collections::HashSet<(TypeId, u8)>,
  ) {
    const OUT: u8 = 1;
    const IN: u8 = 2;

    if !visited.insert((ty, position)) {
      return;
    }
    match self.store.type_kind(ty) {
      TypeKind::TypeParam(id) => {
        usage
          .entry(id)
          .and_modify(|bits| *bits |= position)
          .or_insert(position);
      }
      TypeKind::Union(members) | TypeKind::Intersection(members) => {
        for member in members {
          self.collect_variance_usage(member, position, usage, visited);
        }
      }
      TypeKind::Array { ty, .. } => self.collect_variance_usage(ty, position, usage, visited),
      TypeKind::Tuple(elems) => {
        for elem in elems {
          self.collect_variance_usage(elem.ty, position, usage, visited);
        }
      }
      TypeKind::Callable { overloads } => {
        for sig_id in overloads {
          let sig = self.store.signature(sig_id);
          self.collect_signature_variance(&sig, position, usage, visited);
        }
      }
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        for prop in shape.properties {
          self.collect_variance_usage(prop.data.ty, position, usage, visited);
        }
        for sig_id in shape.call_signatures {
          let sig = self.store.signature(sig_id);
          self.collect_signature_variance(&sig, position, usage, visited);
        }
        for sig_id in shape.construct_signatures {
          let sig = self.store.signature(sig_id);
          self.collect_signature_variance(&sig, position, usage, visited);
        }
        for idx in shape.indexers {
          let flipped = ((position & OUT) << 1) | ((position & IN) >> 1);
          self.collect_variance_usage(idx.key_type, flipped, usage, visited);
          self.collect_variance_usage(idx.value_type, position, usage, visited);
        }
      }
      TypeKind::Ref { args, .. } => {
        for arg in args {
          self.collect_variance_usage(arg, position, usage, visited);
        }
      }
      TypeKind::Intrinsic { ty, .. } => self.collect_variance_usage(ty, position, usage, visited),
      TypeKind::Infer { constraint, .. } => {
        if let Some(constraint) = constraint {
          self.collect_variance_usage(constraint, position, usage, visited);
        }
      }
      TypeKind::Predicate { asserted, .. } => {
        if let Some(asserted) = asserted {
          self.collect_variance_usage(asserted, position, usage, visited);
        }
      }
      TypeKind::Conditional {
        check,
        extends,
        true_ty,
        false_ty,
        ..
      } => {
        self.collect_variance_usage(check, OUT | IN, usage, visited);
        self.collect_variance_usage(extends, OUT | IN, usage, visited);
        self.collect_variance_usage(true_ty, position, usage, visited);
        self.collect_variance_usage(false_ty, position, usage, visited);
      }
      TypeKind::Mapped(mapped) => {
        self.collect_variance_usage(mapped.source, OUT | IN, usage, visited);
        self.collect_variance_usage(mapped.value, position, usage, visited);
        if let Some(name_type) = mapped.name_type {
          self.collect_variance_usage(name_type, OUT | IN, usage, visited);
        }
        if let Some(as_type) = mapped.as_type {
          self.collect_variance_usage(as_type, OUT | IN, usage, visited);
        }
      }
      TypeKind::IndexedAccess { obj, index } => {
        self.collect_variance_usage(obj, OUT | IN, usage, visited);
        self.collect_variance_usage(index, OUT | IN, usage, visited);
      }
      TypeKind::KeyOf(inner) => self.collect_variance_usage(inner, OUT | IN, usage, visited),
      TypeKind::EmptyObject
      | TypeKind::Any
      | TypeKind::Unknown
      | TypeKind::Never
      | TypeKind::Void
      | TypeKind::Null
      | TypeKind::Undefined
      | TypeKind::Boolean
      | TypeKind::Number
      | TypeKind::String
      | TypeKind::BigInt
      | TypeKind::Symbol
      | TypeKind::UniqueSymbol
      | TypeKind::BooleanLiteral(_)
      | TypeKind::NumberLiteral(_)
      | TypeKind::StringLiteral(_)
      | TypeKind::BigIntLiteral(_)
      | TypeKind::This
      | TypeKind::TemplateLiteral(_) => {}
    }
  }

  fn collect_signature_variance(
    &self,
    sig: &Signature,
    position: u8,
    usage: &mut HashMap<TypeParamId, u8>,
    visited: &mut std::collections::HashSet<(TypeId, u8)>,
  ) {
    const OUT: u8 = 1;
    const IN: u8 = 2;

    let flipped = ((position & OUT) << 1) | ((position & IN) >> 1);
    if let Some(this) = sig.this_param {
      self.collect_variance_usage(this, flipped, usage, visited);
    }
    for param in sig.params.iter() {
      self.collect_variance_usage(param.ty, flipped, usage, visited);
    }
    self.collect_variance_usage(sig.ret, position, usage, visited);
  }

  fn type_name_to_string(&self, name: &hir_js::TypeName, names: &hir_js::NameInterner) -> String {
    match name {
      TypeName::Ident(id) => names.resolve(*id).unwrap_or_default().to_string(),
      TypeName::Qualified(path) => path
        .last()
        .and_then(|id| names.resolve(*id))
        .unwrap_or_default()
        .to_string(),
      TypeName::Import(import) => import
        .qualifier
        .as_ref()
        .and_then(|q| q.last())
        .and_then(|id| names.resolve(*id))
        .unwrap_or_default()
        .to_string(),
      TypeName::ImportExpr => String::new(),
    }
  }

  fn type_name_to_path(
    &self,
    name: &hir_js::TypeName,
    names: &hir_js::NameInterner,
  ) -> Option<Vec<String>> {
    match name {
      TypeName::Ident(id) => Some(vec![names.resolve(*id)?.to_string()]),
      TypeName::Qualified(path) => {
        let mut segments = Vec::with_capacity(path.len());
        for id in path.iter() {
          segments.push(names.resolve(*id)?.to_string());
        }
        (!segments.is_empty()).then_some(segments)
      }
      TypeName::Import(_) | TypeName::ImportExpr => None,
    }
  }

  fn lower_signature(&mut self, sig: &TypeSignature, names: &hir_js::NameInterner) -> Signature {
    let prev_params = self.type_params.clone();
    let prev_names = self.type_param_names.clone();
    let type_params = self.lower_type_param_decls(&sig.type_params, names);
    let (this_param, sig_params) = self.lower_fn_params(&sig.params, names);
    let ret = match sig.return_type {
      Some(ret_id) => {
        let kind = self
          .arenas()
          .type_exprs
          .get(ret_id.0 as usize)
          .map(|expr| expr.kind.clone());
        match kind {
          Some(TypeExprKind::TypePredicate(pred)) => {
            self.lower_type_predicate_in_signature(&pred, &sig_params, names)
          }
          _ => self.lower_type_expr(ret_id, names),
        }
      }
      None => self.store.primitive_ids().any,
    };
    let sig = Signature {
      params: sig_params,
      ret,
      type_params,
      this_param,
    };
    self.type_params = prev_params;
    self.type_param_names = prev_names;
    sig
  }

  fn lower_fn_params(
    &mut self,
    params: &[TypeFnParam],
    names: &hir_js::NameInterner,
  ) -> (Option<TypeId>, Vec<Param>) {
    let mut lowered = Vec::new();
    let mut this_param = None;
    for param in params.iter() {
      let name = param.name.and_then(|n| names.resolve(n));
      if matches!(name.as_deref(), Some("this")) && this_param.is_none() {
        this_param = Some(self.lower_type_expr(param.ty, names));
        continue;
      }
      lowered.push(self.lower_fn_param(param, names));
    }
    (this_param, lowered)
  }

  fn lower_fn_param(&mut self, param: &TypeFnParam, names: &hir_js::NameInterner) -> Param {
    let mut ty = self.lower_type_expr(param.ty, names);
    if param.rest {
      ty = self.normalize_rest_param_type(ty);
    }
    Param {
      name: param
        .name
        .and_then(|n| names.resolve(n))
        .map(|n| self.store.intern_name(n.to_string())),
      ty,
      optional: param.optional,
      rest: param.rest,
    }
  }

  /// A rest parameter annotated with the lib `Array<X>` interface form must
  /// carry the intrinsic array type so rest-element expansion finds the
  /// element (`taggedTemplatesWithTypeArguments1.ts`:
  /// `...callbacks: Array<(x: T) => any>` checked each substitution against
  /// the whole `Array` instead of the element).
  fn normalize_rest_param_type(&mut self, ty: TypeId) -> TypeId {
    let TypeKind::Ref { def, args } = self.store.type_kind(ty) else {
      return ty;
    };
    if args.len() != 1 {
      return ty;
    }
    let is_lib_array = self
      .resolve_named_in_namespace("Array", self.file, Namespace::TYPE)
      .is_some_and(|array_def| array_def == def || self.map_value_def(array_def) == def);
    if !is_lib_array {
      return ty;
    }
    self.store.intern_type(TypeKind::Array {
      ty: args[0],
      readonly: false,
    })
  }

  /// String literal index like `"#bar"` — not a legal indexed-access key for
  /// ES private fields (tsc TS2339 on `C["#bar"]`).
  fn private_ident_string_index_prop(&self, index: TypeExprId) -> Option<String> {
    let arenas = self.current_arenas?;
    let ty = arenas.type_exprs.get(index.0 as usize)?;
    match &ty.kind {
      TypeExprKind::Literal(hir_js::TypeLiteral::String(s)) if s.starts_with('#') => {
        Some(s.clone())
      }
      TypeExprKind::Parenthesized(inner) => self.private_ident_string_index_prop(*inner),
      _ => None,
    }
  }

  /// Resolve a private identifier (`#foo`) from a HIR property name, if any.
  fn private_property_name(
    &self,
    name: &hir_js::PropertyName,
    names: &hir_js::NameInterner,
  ) -> Option<String> {
    match name {
      hir_js::PropertyName::Ident(id) => {
        let resolved = names.resolve(*id)?;
        resolved.starts_with('#').then(|| resolved.to_string())
      }
      hir_js::PropertyName::String(s) if s.starts_with('#') => Some(s.clone()),
      _ => None,
    }
  }

  /// Accessibility + nominal origin for a class member property.
  ///
  /// `#`-prefixed private identifiers are always `Private` and branded with the
  /// declaring class `DefId` so assignability treats them as unique per class
  /// (tsc private-name uniqueness / `privateNamesUnique-*`).
  fn class_member_prop_access(
    &self,
    name: &hir_js::PropertyName,
    names: &hir_js::NameInterner,
    member_accessibility: Option<hir_js::ClassMemberAccessibility>,
    owner: HirDefId,
  ) -> (Option<types_ts_interned::Accessibility>, Option<DefId>) {
    if self.private_property_name(name, names).is_some() {
      return (Some(types_ts_interned::Accessibility::Private), Some(owner));
    }
    let accessibility = member_accessibility.map(|a| match a {
      hir_js::ClassMemberAccessibility::Public => types_ts_interned::Accessibility::Public,
      hir_js::ClassMemberAccessibility::Protected => types_ts_interned::Accessibility::Protected,
      hir_js::ClassMemberAccessibility::Private => types_ts_interned::Accessibility::Private,
    });
    (accessibility, None)
  }

  /// TS18016 for private names in type/interface/object-type member positions.
  ///
  /// Property signatures use a name-only primary span; method signatures use the
  /// full member span (tsc baseline parity).
  fn check_private_name_type_member(
    &mut self,
    member_span: TextRange,
    name: &hir_js::PropertyName,
    names: &hir_js::NameInterner,
    full_member_span: bool,
  ) {
    let Some(priv_name) = self.private_property_name(name, names) else {
      return;
    };
    let range = if full_member_span {
      member_span
    } else {
      let name_len = priv_name.len() as u32;
      TextRange {
        start: member_span.start,
        end: member_span
          .start
          .saturating_add(name_len)
          .min(member_span.end),
      }
    };
    self
      .diagnostics
      .push(codes::PRIVATE_IDENTIFIERS_OUTSIDE_CLASS.error(
        "Private identifiers are not allowed outside class bodies.",
        Span {
          file: self.file,
          range,
        },
      ));
  }

  fn lower_member(
    &mut self,
    shape: &mut Shape,
    member: TypeMemberId,
    names: &hir_js::NameInterner,
  ) {
    let Some(member) = self.arenas().type_members.get(member.0 as usize).cloned() else {
      return;
    };
    match member.kind {
      TypeMemberKind::Property(prop) => {
        self.check_private_name_type_member(member.span, &prop.name, names, false);
        if let Some((key, data)) = self.lower_property(&prop, names) {
          shape.properties.push(Property { key, data });
        }
      }
      TypeMemberKind::Method(method) => {
        self.check_private_name_type_member(member.span, &method.name, names, true);
        if let Some((key, ty)) = self.lower_method(&method, names) {
          shape.properties.push(Property {
            key,
            data: PropData {
              ty,
              optional: method.optional,
              readonly: false,
              accessibility: None,
              is_method: true,
              origin: None,
              declared_on: None,
            },
          });
        }
      }
      TypeMemberKind::Constructor(cons) => {
        let sig = self.lower_signature(&cons, names);
        let sig_id = self.store.intern_signature(sig);
        shape.construct_signatures.push(sig_id);
      }
      TypeMemberKind::CallSignature(call) => {
        let sig = self.lower_signature(&call, names);
        let sig_id = self.store.intern_signature(sig);
        shape.call_signatures.push(sig_id);
      }
      TypeMemberKind::IndexSignature(idx) => {
        let key_type = self.lower_type_expr(idx.parameter_type, names);
        let value_type = self.lower_type_expr(idx.type_annotation, names);
        shape.indexers.push(Indexer {
          key_type,
          value_type,
          readonly: idx.readonly,
        });
      }
      TypeMemberKind::Getter(getter) => {
        self.check_private_name_type_member(member.span, &getter.name, names, false);
        if let Some((key, mut data)) = self.lower_property(
          &hir_js::TypePropertySignature {
            readonly: true,
            optional: false,
            name: getter.name,
            type_annotation: getter.return_type,
          },
          names,
        ) {
          data.readonly = true;
          shape.properties.push(Property { key, data });
        }
      }
      TypeMemberKind::Setter(setter) => {
        self.check_private_name_type_member(member.span, &setter.name, names, false);
        if let Some((key, mut data)) = self.lower_property(
          &hir_js::TypePropertySignature {
            readonly: false,
            optional: setter.parameter.optional,
            name: setter.name,
            type_annotation: Some(setter.parameter.ty),
          },
          names,
        ) {
          data.readonly = false;
          shape.properties.push(Property { key, data });
        }
      }
      TypeMemberKind::Mapped(mapped) => {
        let key_type = self.lower_type_expr(mapped.constraint, names);
        let value_type = self.lower_type_expr(mapped.value_type, names);
        shape.indexers.push(Indexer {
          key_type,
          value_type,
          readonly: matches!(
            mapped.readonly,
            Some(hir_js::TypeMappedModifier::Plus) | Some(hir_js::TypeMappedModifier::None)
          ),
        });
      }
    }
  }

  fn lower_property(
    &mut self,
    prop: &hir_js::TypePropertySignature,
    names: &hir_js::NameInterner,
  ) -> Option<(PropKey, PropData)> {
    let trace = std::env::var("TRACE_TYPEOF").is_ok();
    let key = self.prop_key_from_name(&prop.name, names)?;
    let ty = prop
      .type_annotation
      .map(|t| self.lower_type_expr(t, names))
      .unwrap_or(self.store.primitive_ids().unknown);
    if trace {
      if let PropKey::String(name_id) = &key {
        let name = self.store.name(*name_id);
        if name == "document" {
          eprintln!(
            "[lower_property] file {:?} prop {} has_annotation={}",
            self.file,
            name,
            prop.type_annotation.is_some()
          );
        }
      }
    }
    Some((
      key,
      PropData {
        ty,
        optional: prop.optional,
        readonly: prop.readonly,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    ))
  }

  fn lower_method(
    &mut self,
    method: &hir_js::TypeMethodSignature,
    names: &hir_js::NameInterner,
  ) -> Option<(PropKey, TypeId)> {
    let key = self.prop_key_from_name(&method.name, names)?;
    let prev_params = self.type_params.clone();
    let prev_names = self.type_param_names.clone();
    let type_params = self.lower_type_param_decls(&method.type_params, names);
    let (this_param, params) = self.lower_fn_params(&method.params, names);
    let sig = Signature {
      params,
      ret: method
        .return_type
        .map(|t| self.lower_type_expr(t, names))
        .unwrap_or(self.store.primitive_ids().unknown),
      type_params,
      this_param,
    };
    let sig_id = self.store.intern_signature(sig);
    self.type_params = prev_params;
    self.type_param_names = prev_names;
    Some((
      key,
      self.store.intern_type(TypeKind::Callable {
        overloads: vec![sig_id],
      }),
    ))
  }

  fn lower_type_query(&mut self, name: &TypeName, names: &hir_js::NameInterner) -> TypeId {
    if let TypeName::Import(import) = name {
      let empty_qualifier = import
        .qualifier
        .as_ref()
        .map(|segments| segments.is_empty())
        .unwrap_or(true);
      if empty_qualifier {
        if let Some(namespace_def) = self.resolve_import_module_namespace(import) {
          return self.store.intern_type(TypeKind::Ref {
            def: self.map_value_def(namespace_def),
            args: Vec::new(),
          });
        }
        if let Some(resolver) = &self.type_resolver {
          if let Some(module) = import.module.as_deref() {
            if let Some(def) = resolver.resolve_import_typeof(module, None) {
              return self.store.intern_type(TypeKind::Ref {
                def: self.map_value_def(def),
                args: Vec::new(),
              });
            }
          }
        }
      } else if let Some(def) = self.resolve_import_typeof_qualifier(import, names) {
        return self.store.intern_type(TypeKind::Ref {
          def: self.map_value_def(def),
          args: Vec::new(),
        });
      } else if let Some(resolver) = &self.type_resolver {
        if let Some(module) = import.module.as_deref() {
          if let Some(path) = import.qualifier.as_ref().map(|ids| {
            ids
              .iter()
              .filter_map(|id| names.resolve(*id).map(|s| s.to_string()))
              .collect::<Vec<_>>()
          }) {
            if !path.is_empty() {
              if let Some(def) = resolver.resolve_import_typeof(module, Some(&path)) {
                return self.store.intern_type(TypeKind::Ref {
                  def: self.map_value_def(def),
                  args: Vec::new(),
                });
              }
            }
          }
        }
      }
    }

    // Body-local values (`typeof x`) — TypeId from checker scopes.
    if let Some(path) = self.type_name_to_path(name, names) {
      if let [binding_name] = path.as_slice() {
        if let Some(ty) = self.typeof_bindings.get(binding_name).copied() {
          return ty;
        }
        // Ambient globals always present in tsc, even before body scopes are
        // seeded (`typeof undefined` in a var annotation).
        let prim = self.store.primitive_ids();
        match binding_name.as_str() {
          "undefined" => return prim.undefined,
          "NaN" | "Infinity" => return prim.number,
          _ => {}
        }
      }
      if let Some(resolver) = &self.type_resolver {
        if let Some(def) = resolver.resolve_typeof(&path) {
          return self.store.intern_type(TypeKind::Ref {
            def: self.map_value_def(def),
            args: Vec::new(),
          });
        }
      }
      // Qualified `typeof` on a *value member chain* that is not a namespace
      // path (`typeof window.document.title`): read the remaining members as
      // indexed accesses on the head value's type — the evaluator computes
      // the chain type (`{ document: { title: string } }["document"]["title"]`
      // → `string`). Never resolve the last segment as a top-level name:
      // that manufactures self-references
      // (`declare const title: typeof window.document.title;`).
      if path.len() > 1 {
        if let Some(head_def) =
          self.resolve_named_in_namespace(&path[0], self.file, Namespace::VALUE)
        {
          let mut ty = self.store.intern_type(TypeKind::Ref {
            def: self.map_value_def(head_def),
            args: Vec::new(),
          });
          for segment in &path[1..] {
            let key = self.store.intern_name(segment.clone());
            let index = self.store.intern_type(TypeKind::StringLiteral(key));
            ty = self
              .store
              .intern_type(TypeKind::IndexedAccess { obj: ty, index });
          }
          return ty;
        }
      }
    }

    if let Some(def) = self.resolve_value_name(name, names, None) {
      return self.store.intern_type(TypeKind::Ref {
        def: self.map_value_def(def),
        args: Vec::new(),
      });
    }

    let fallback_name = self.type_name_to_string(name, names);
    if let Some(def) = self.defs.get(&(self.file, fallback_name.clone())) {
      return self.store.intern_type(TypeKind::Ref {
        def: self.map_value_def(*def),
        args: Vec::new(),
      });
    }

    self.diagnostics.push(codes::CANNOT_FIND_NAME.error(
      codes::cannot_find_name_message(&fallback_name),
      Span::new(self.file, TextRange::new(0, 0)),
    ));

    self.store.primitive_ids().unknown
  }

  fn lower_type_ref(
    &mut self,
    reference: &hir_js::TypeRef,
    names: &hir_js::NameInterner,
    span: TextRange,
  ) -> TypeId {
    let args: Vec<_> = reference
      .type_args
      .iter()
      .map(|a| self.lower_type_expr(*a, names))
      .collect();

    // Type parameter reference.
    if let TypeName::Ident(name_id) = &reference.name {
      if let Some(tp) = self.type_param_names.get(name_id) {
        return self.store.intern_type(TypeKind::TypeParam(*tp));
      }
    }

    // TypeScript `intrinsic` marker used by lib declarations (e.g. `type Uppercase<S extends string> = intrinsic;`).
    // Treat it as an opaque type during lowering so that we can detect and
    // replace intrinsic aliases later without emitting an "unknown identifier"
    // diagnostic for the marker itself.
    if reference.type_args.is_empty() {
      if let TypeName::Ident(name_id) = &reference.name {
        if names.resolve(*name_id) == Some("intrinsic") {
          return self.store.primitive_ids().unknown;
        }
        // Global `Object` ≈ `{}` for assignability (primitives/enums are non-nullish).
        if names.resolve(*name_id) == Some("Object") {
          return self.store.intern_type(TypeKind::EmptyObject);
        }
        // Boxed primitives ≈ their primitive types for assignability
        // (`enumAssignability.ts`: `var p: Number = e`).
        let prim = self.store.primitive_ids();
        match names.resolve(*name_id) {
          Some("Number") => return prim.number,
          Some("String") => return prim.string,
          Some("Boolean") => return prim.boolean,
          Some("BigInt") => return prim.bigint,
          Some("Symbol") => return prim.symbol,
          _ => {}
        }
      }
    }

    if let Some(resolved) = self.resolve_type_name(&reference.name, names, None) {
      return self.store.intern_type(TypeKind::Ref {
        def: resolved,
        args,
      });
    }

    // Program-grade resolver (import-equals, ambient export=, namespace members).
    if let Some(resolver) = self.type_name_resolver {
      if let Some(path) = self.type_name_to_path(&reference.name, names) {
        if let Some(resolved) = resolver(&path) {
          return self.store.intern_type(TypeKind::Ref {
            def: resolved,
            args,
          });
        }
      }
    }

    // Body-check / owned TypeResolver (avoids borrowing a short-lived Fn).
    if let Some(resolver) = &self.type_resolver {
      if let Some(path) = self.type_name_to_path(&reference.name, names) {
        if let Some(resolved) = resolver.resolve_type_name(&path) {
          return self.store.intern_type(TypeKind::Ref {
            def: resolved,
            args,
          });
        }
      }
    }

    let name = self.type_name_to_string(&reference.name, names);

    if let Some(def) = self
      .defs
      .iter()
      .find(|((_, def_name), _)| def_name == &name)
      .map(|(_, def)| *def)
      .or_else(|| {
        self.def_by_name.and_then(|map| {
          map
            .iter()
            .find(|((_, def_name), _)| def_name == &name)
            .map(|(_, def)| *def)
        })
      })
    {
      return self.store.intern_type(TypeKind::Ref { def, args });
    }

    // Match AST `TypeLowerer` / skipLibCheck filtering: type-position refs use
    // TC2008, not value-position TS2304.
    self
      .diagnostics
      .push(codes::UNRESOLVED_TYPE_REFERENCE.error(
        format!("unresolved type '{name}'"),
        Span::new(self.file, span),
      ));

    self.store.primitive_ids().unknown
  }

  fn lower_import_type(
    &mut self,
    import: &hir_js::TypeImport,
    names: &hir_js::NameInterner,
  ) -> TypeId {
    let args: Vec<_> = import
      .type_args
      .iter()
      .map(|a| self.lower_type_expr(*a, names))
      .collect();

    let qualifier_segments: Option<Vec<String>> = import.qualifier.as_ref().and_then(|q| match q {
      TypeName::Ident(id) => names.resolve(*id).map(|n| vec![n.to_string()]),
      TypeName::Qualified(path) => {
        let segs: Vec<String> = path
          .iter()
          .filter_map(|id| names.resolve(*id).map(|s| s.to_string()))
          .collect();
        (!segs.is_empty()).then_some(segs)
      }
      TypeName::Import(inner) => inner.qualifier.as_ref().map(|segments| {
        segments
          .iter()
          .filter_map(|id| names.resolve(*id).map(|s| s.to_string()))
          .collect()
      }),
      TypeName::ImportExpr => None,
    });

    // Program-grade resolver (works without DeclHost / key_to_id wiring used by
    // body and value-signature lowering).
    if let Some(resolver) = &self.type_resolver {
      if let Some(def) = resolver.resolve_import_type(&import.module, qualifier_segments.as_deref())
      {
        return self.store.intern_type(TypeKind::Ref {
          def,
          args: args.clone(),
        });
      }
    }

    let Some(host) = self.host else {
      return self.store.primitive_ids().unknown;
    };

    let Some(from_key) = self.file_key.as_ref() else {
      return self.store.primitive_ids().unknown;
    };
    let Some(target_key) = host.resolve(from_key, &import.module) else {
      return self.store.primitive_ids().unknown;
    };
    let Some(target_file) = self.key_to_id.and_then(|resolver| resolver(&target_key)) else {
      return self.store.primitive_ids().unknown;
    };

    if let Some(name) = qualifier_segments
      .as_ref()
      .and_then(|segs| segs.last())
      .cloned()
    {
      if let Some(def) = self
        .def_by_name
        .and_then(|map| map.get(&(target_file, name.clone())).copied())
        .or_else(|| self.defs.get(&(target_file, name.clone())).copied())
      {
        return self.store.intern_type(TypeKind::Ref {
          def,
          args: args.clone(),
        });
      }
    }

    self.store.primitive_ids().unknown
  }

  fn resolve_type_name(
    &self,
    name: &hir_js::TypeName,
    names: &hir_js::NameInterner,
    file_override: Option<FileId>,
  ) -> Option<DefId> {
    self.resolve_in_namespace(name, names, file_override, Namespace::TYPE)
  }

  fn resolve_value_name(
    &self,
    name: &hir_js::TypeName,
    names: &hir_js::NameInterner,
    file_override: Option<FileId>,
  ) -> Option<DefId> {
    self.resolve_in_namespace(name, names, file_override, Namespace::VALUE)
  }

  fn resolve_in_namespace(
    &self,
    name: &hir_js::TypeName,
    names: &hir_js::NameInterner,
    file_override: Option<FileId>,
    ns: Namespace,
  ) -> Option<DefId> {
    match name {
      TypeName::Ident(id) => {
        let resolved = names.resolve(*id)?.to_string();
        self.resolve_named_in_namespace(&resolved, file_override.unwrap_or(self.file), ns)
      }
      TypeName::Qualified(path) => self
        .resolve_qualified_in_namespace(path, names, file_override.unwrap_or(self.file), ns)
        .or_else(|| {
          path
            .last()
            .and_then(|id| names.resolve(*id))
            .and_then(|resolved| {
              self.resolve_named_in_namespace(
                &resolved.to_string(),
                file_override.unwrap_or(self.file),
                ns,
              )
            })
        }),
      TypeName::Import(import) => import.module.as_ref().and_then(|module| {
        let name = import
          .qualifier
          .as_ref()
          .and_then(|segments| segments.last())
          .and_then(|id| names.resolve(*id))
          .map(|s| s.to_string())?;
        let from_key = self.file_key.as_ref()?;
        let target_key = self.host.and_then(|h| h.resolve(from_key, module))?;
        let target_file = self.key_to_id.and_then(|resolver| resolver(&target_key))?;
        self.resolve_named_in_namespace(&name, target_file, ns)
      }),
      TypeName::ImportExpr => None,
    }
  }

  fn resolve_import_module_namespace(&self, import: &hir_js::hir::TypeImportName) -> Option<DefId> {
    let module = import.module.as_ref()?;
    let from_key = self.file_key.as_ref()?;
    let host = self.host?;
    let target_key = host.resolve(from_key, module)?;
    let target_file = self.key_to_id.and_then(|resolver| resolver(&target_key))?;
    self
      .module_namespace_defs
      .and_then(|defs| defs.get(&target_file).copied())
  }

  fn resolve_import_typeof_qualifier(
    &self,
    import: &hir_js::hir::TypeImportName,
    names: &hir_js::NameInterner,
  ) -> Option<DefId> {
    let sem = self.semantics?;
    let module = import.module.as_ref()?;
    let qualifier_ids = import.qualifier.as_ref()?;
    if qualifier_ids.is_empty() {
      return None;
    }
    let from_key = self.file_key.as_ref()?;
    let host = self.host?;
    let target_key = host.resolve(from_key, module)?;
    let mut current_file = self.key_to_id.and_then(|resolver| resolver(&target_key))?;

    let mut segments = Vec::with_capacity(qualifier_ids.len());
    for id in qualifier_ids.iter() {
      segments.push(names.resolve(*id)?.to_string());
    }

    for (idx, segment) in segments.iter().enumerate() {
      let is_last = idx + 1 == segments.len();
      let ns = if is_last {
        Namespace::VALUE
      } else {
        Namespace::NAMESPACE
      };
      let symbol = sem.resolve_export(current_file, segment, ns)?;
      if is_last {
        if let Some(def) = self.def_for_symbol_in_namespace(sem, symbol, Namespace::VALUE) {
          return Some(def);
        }
        if let SymbolOrigin::Import { from, imported } = &sem.symbols().symbol(symbol).origin {
          if imported == "*" {
            if let ModuleRef::File(from_file) = from {
              return self
                .module_namespace_defs
                .and_then(|defs| defs.get(from_file).copied());
            }
          }
        }
        return None;
      }
      current_file = self.symbol_target_file(sem, symbol)?;
    }
    None
  }

  fn resolve_named_in_namespace(&self, name: &str, file: FileId, ns: Namespace) -> Option<DefId> {
    let trace = std::env::var("TRACE_TYPEOF").is_ok() && (name == "document" || name == "window");
    if trace {
      eprintln!(
        "[resolve_named_in_namespace] file {:?} name {} ns {:?}",
        file, name, ns
      );
    }

    // When semantic information is available, resolve type names using the TYPE
    // namespace only. This avoids incorrectly binding `Promise`/`Symbol`-style
    // references (used in many lib declaration signatures) to value-space
    // `declare var` bindings in the same file.
    if ns == Namespace::TYPE {
      if let Some(sem) = self.semantics {
        if let Some(symbol) = sem.resolve_in_module(file, name, Namespace::TYPE) {
          if let Some(def) = self.def_for_symbol_in_namespace(sem, symbol, Namespace::TYPE) {
            return Some(def);
          }
        }
        if let Some(group) = sem.global_symbols().get(name) {
          if let Some(symbol) = group.symbol_for(Namespace::TYPE, sem.symbols()) {
            if let Some(def) = self.def_for_symbol_in_namespace(sem, symbol, Namespace::TYPE) {
              return Some(def);
            }
          }
        }
      }
    }

    if file == self.file {
      if let Some(local) = self.local_defs.get(name, ns) {
        if trace {
          eprintln!("[resolve_named_in_namespace] local def {:?}", local);
        }
        return self
          .def_map
          .and_then(|map| map.get(&local).copied())
          .or_else(|| {
            self
              .def_by_name
              .and_then(|map| map.get(&(self.file, name.to_string())).copied())
          })
          .or(Some(local));
      }
    }

    if let Some(def) = self.defs.get(&(file, name.to_string())) {
      if trace {
        eprintln!(
          "[resolve_named_in_namespace] defs map hit {:?} -> {:?}",
          (file, name),
          def
        );
      }
      return Some(*def);
    }

    if let Some(def) = self
      .def_by_name
      .and_then(|map| map.get(&(file, name.to_string())).copied())
    {
      if trace {
        eprintln!(
          "[resolve_named_in_namespace] def_by_name hit {:?} -> {:?}",
          (file, name),
          def
        );
      }
      return Some(def);
    }

    // When semantic information is unavailable (e.g. unit tests without module
    // graphs), fall back to any known definition with the same name across
    // files. When semantics are available we rely on namespace-aware resolution
    // below so that names like `Promise` resolve to the type-space interface
    // instead of the value-space constructor.
    if self.semantics.is_none() {
      let mut candidates: Vec<_> = self
        .defs
        .iter()
        .filter_map(|((_, def_name), def)| (def_name == name).then_some(*def))
        .collect();
      candidates.sort_by_key(|d| d.0);
      if let Some(def) = candidates.first() {
        return Some(*def);
      }
    }

    if let Some(sem) = self.semantics {
      let order = if ns == Namespace::VALUE {
        [Namespace::VALUE, Namespace::NAMESPACE, Namespace::TYPE]
      } else {
        [Namespace::TYPE, Namespace::NAMESPACE, Namespace::VALUE]
      };
      if let Some(symbol) = self.resolve_symbol_in_module_ns(sem, file, name, &order) {
        if let Some(decl) = sem.symbol_decls(symbol, ns).first().or_else(|| {
          order
            .iter()
            .filter_map(|candidate| sem.symbol_decls(symbol, *candidate).first())
            .next()
        }) {
          let decl_data = sem.symbols().decl(*decl);
          let target = DefId(decl_data.def_id.0);
          if trace {
            eprintln!(
              "[resolve_named_in_namespace] symbol decl hit {:?} -> {:?}",
              (file, name),
              target
            );
          }
          return self
            .def_map
            .and_then(|map| map.get(&target).copied())
            .or_else(|| {
              self.def_by_name.and_then(|map| {
                map
                  .get(&(FileId(decl_data.file.0), decl_data.name.clone()))
                  .copied()
              })
            })
            .or(Some(target));
        }
      }
      if let Some((_, group)) = sem
        .global_symbols()
        .iter()
        .find(|(global_name, _)| *global_name == name)
      {
        if let Some(symbol) = group.symbol_for(ns, sem.symbols()) {
          if let Some(def) = self.def_for_symbol(sem, symbol) {
            if trace {
              eprintln!(
                "[resolve_named_in_namespace] global symbol {:?} -> {:?}",
                name, def
              );
            }
            return Some(def);
          }
        }
      }
    }

    None
  }

  fn resolve_qualified_in_namespace(
    &self,
    path: &[hir_js::NameId],
    names: &hir_js::NameInterner,
    file: FileId,
    ns: Namespace,
  ) -> Option<DefId> {
    let sem = self.semantics?;
    let mut segments = Vec::new();
    for id in path.iter() {
      let Some(name) = names.resolve(*id) else {
        return None;
      };
      segments.push(name.to_string());
    }
    if segments.is_empty() {
      return None;
    }

    let order = if ns == Namespace::VALUE {
      [Namespace::VALUE, Namespace::NAMESPACE, Namespace::TYPE]
    } else {
      [Namespace::TYPE, Namespace::NAMESPACE, Namespace::VALUE]
    };
    let mut symbol = self.resolve_symbol_in_module_ns(sem, file, &segments[0], &order)?;
    let mut current_file = self.symbol_target_file(sem, symbol).unwrap_or(file);
    for segment in segments.iter().skip(1) {
      symbol = self.resolve_symbol_export(sem, current_file, segment, &order)?;
      current_file = self.symbol_target_file(sem, symbol).unwrap_or(current_file);
    }

    let def = self.def_for_symbol(sem, symbol);
    def
  }

  fn resolve_symbol_in_module_ns(
    &self,
    sem: &TsProgramSemantics,
    file: FileId,
    name: &str,
    order: &[Namespace],
  ) -> Option<semantic_js::ts::SymbolId> {
    for ns in order {
      if let Some(sym) = sem.resolve_in_module(file, name, *ns) {
        return Some(sym);
      }
    }
    None
  }

  fn resolve_symbol_export(
    &self,
    sem: &TsProgramSemantics,
    file: FileId,
    name: &str,
    order: &[Namespace],
  ) -> Option<semantic_js::ts::SymbolId> {
    for ns in order {
      if let Some(sym) = sem.resolve_export(file, name, *ns) {
        return Some(sym);
      }
    }
    None
  }

  fn symbol_target_file(
    &self,
    sem: &TsProgramSemantics,
    symbol: semantic_js::ts::SymbolId,
  ) -> Option<FileId> {
    let sym = sem.symbols().symbol(symbol);
    match &sym.origin {
      SymbolOrigin::Import { from, .. } => match from {
        ModuleRef::File(from) => Some(*from),
        _ => None,
      },
      _ => match &sym.owner {
        SymbolOwner::Module(file) => Some(*file),
        _ => None,
      },
    }
  }

  fn def_for_symbol(
    &self,
    sem: &TsProgramSemantics,
    symbol: semantic_js::ts::SymbolId,
  ) -> Option<DefId> {
    for ns in [Namespace::TYPE, Namespace::NAMESPACE, Namespace::VALUE] {
      if let Some(def) = self.def_for_symbol_in_namespace(sem, symbol, ns) {
        return Some(def);
      }
    }
    None
  }

  fn def_for_symbol_in_namespace(
    &self,
    sem: &TsProgramSemantics,
    symbol: semantic_js::ts::SymbolId,
    ns: Namespace,
  ) -> Option<DefId> {
    let decl = sem.symbol_decls(symbol, ns).first()?;
    let decl_data = sem.symbols().decl(*decl);
    let def = DefId(decl_data.def_id.0);
    self
      .def_map
      .and_then(|map| map.get(&def).copied())
      .or_else(|| {
        self
          .def_by_name
          .and_then(|map| map.get(&(decl_data.file, decl_data.name.clone())).copied())
      })
      .or(Some(def))
  }
}

impl<'a, 'diag> std::fmt::Debug for HirDeclLowerer<'a, 'diag> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("HirDeclLowerer")
      .field("file", &self.file)
      .finish_non_exhaustive()
  }
}
