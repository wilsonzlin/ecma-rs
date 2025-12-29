use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::{Diagnostic, FileId, TextRange};
use hir_js::{DefId, DefKind as HirDefKind, LowerResult};
use parse_js::ast::class_or_object::{ClassMember, ClassOrObjKey, ClassOrObjVal};
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::func::Func;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{Accessibility as ClassAccessibility, ClassDecl, ParamDecl};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::{AmbientClassDecl, NamespaceBody, NamespaceDecl};
use parse_js::loc::Loc;
use types_ts_interned::{
  Accessibility, Indexer, ObjectType, Param as SigParam, PropData, PropKey, Property, Shape,
  Signature, TypeId, TypeKind, TypeParamId, TypeStore,
};

use crate::check::type_expr::{TypeLowerer, TypeResolver};

#[derive(Clone)]
struct Resolver {
  map: HashMap<String, DefId>,
}

impl Resolver {
  fn new(defs: &HashMap<(FileId, String), DefId>) -> Self {
    let mut map = HashMap::new();
    for ((_file, name), def) in defs.iter() {
      map.entry(name.clone()).or_insert(*def);
    }
    Self { map }
  }
}

impl TypeResolver for Resolver {
  fn resolve_type_name(&self, path: &[String]) -> Option<DefId> {
    match path {
      [name] => self.map.get(name).copied(),
      _ => None,
    }
  }
}

pub(crate) struct ClassTypeInfo {
  pub def: DefId,
  pub name: Option<String>,
  pub instance: TypeId,
  pub value: TypeId,
  pub type_params: Vec<TypeParamId>,
}

pub(crate) fn type_classes_in_file(
  store: Arc<TypeStore>,
  ast: &Arc<Node<TopLevel>>,
  lowered: &LowerResult,
  file: FileId,
  def_by_name: &HashMap<(FileId, String), DefId>,
  diagnostics: &mut Vec<Diagnostic>,
) -> Vec<ClassTypeInfo> {
  let mut class_defs: HashMap<TextRange, DefId> = HashMap::new();
  for def in lowered
    .defs
    .iter()
    .filter(|d| matches!(d.path.kind, HirDefKind::Class))
  {
    class_defs.insert(def.span, def.id);
  }
  let resolver: Option<Arc<dyn TypeResolver>> = Some(Arc::new(Resolver::new(def_by_name)));

  let mut results = Vec::new();
  walk_stmts(
    &ast.stx.body,
    file,
    &store,
    resolver.clone(),
    &class_defs,
    def_by_name,
    diagnostics,
    &mut results,
  );
  results
}

fn walk_stmts(
  stmts: &[Node<Stmt>],
  file: FileId,
  store: &Arc<TypeStore>,
  resolver: Option<Arc<dyn TypeResolver>>,
  class_defs: &HashMap<TextRange, DefId>,
  def_by_name: &HashMap<(FileId, String), DefId>,
  diagnostics: &mut Vec<Diagnostic>,
  out: &mut Vec<ClassTypeInfo>,
) {
  for stmt in stmts.iter() {
    match stmt.stx.as_ref() {
      Stmt::ClassDecl(class) => {
        let span = loc_range(stmt.loc);
        let name = class.stx.name.as_ref().map(|n| n.stx.name.clone());
        if let Some(def) = def_for_class(span, name.as_deref(), file, class_defs, def_by_name) {
          if let Some(info) =
            lower_runtime_class(store, resolver.clone(), &class.stx, def, file, diagnostics)
          {
            out.push(info);
          }
        }
      }
      Stmt::AmbientClassDecl(class) => {
        let span = loc_range(stmt.loc);
        if let Some(def) = def_for_class(span, Some(&class.stx.name), file, class_defs, def_by_name)
        {
          let info =
            lower_ambient_class(store, resolver.clone(), &class.stx, def, file, diagnostics);
          out.push(info);
        }
      }
      Stmt::NamespaceDecl(ns) => walk_namespace(
        ns,
        file,
        store,
        resolver.clone(),
        class_defs,
        def_by_name,
        diagnostics,
        out,
      ),
      Stmt::ModuleDecl(module) => {
        if let Some(body) = &module.stx.body {
          walk_stmts(
            body,
            file,
            store,
            resolver.clone(),
            class_defs,
            def_by_name,
            diagnostics,
            out,
          );
        }
      }
      Stmt::GlobalDecl(global) => walk_stmts(
        &global.stx.body,
        file,
        store,
        resolver.clone(),
        class_defs,
        def_by_name,
        diagnostics,
        out,
      ),
      Stmt::Block(block) => walk_stmts(
        &block.stx.body,
        file,
        store,
        resolver.clone(),
        class_defs,
        def_by_name,
        diagnostics,
        out,
      ),
      _ => {}
    }
  }
}

fn walk_namespace(
  ns: &Node<NamespaceDecl>,
  file: FileId,
  store: &Arc<TypeStore>,
  resolver: Option<Arc<dyn TypeResolver>>,
  class_defs: &HashMap<TextRange, DefId>,
  def_by_name: &HashMap<(FileId, String), DefId>,
  diagnostics: &mut Vec<Diagnostic>,
  out: &mut Vec<ClassTypeInfo>,
) {
  match &ns.stx.body {
    NamespaceBody::Block(stmts) => walk_stmts(
      stmts,
      file,
      store,
      resolver,
      class_defs,
      def_by_name,
      diagnostics,
      out,
    ),
    NamespaceBody::Namespace(inner) => walk_namespace(
      inner,
      file,
      store,
      resolver,
      class_defs,
      def_by_name,
      diagnostics,
      out,
    ),
  }
}

fn def_for_class(
  span: TextRange,
  name: Option<&str>,
  file: FileId,
  class_defs: &HashMap<TextRange, DefId>,
  def_by_name: &HashMap<(FileId, String), DefId>,
) -> Option<DefId> {
  class_defs
    .get(&span)
    .copied()
    .or_else(|| name.and_then(|n| def_by_name.get(&(file, n.to_string())).copied()))
}

fn lower_ambient_class(
  store: &Arc<TypeStore>,
  resolver: Option<Arc<dyn TypeResolver>>,
  class: &AmbientClassDecl,
  def: DefId,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> ClassTypeInfo {
  let mut lowerer = match resolver {
    Some(resolver) => TypeLowerer::with_resolver(Arc::clone(store), resolver),
    None => TypeLowerer::new(Arc::clone(store)),
  };
  lowerer.set_file(file);

  let mut type_params = Vec::new();
  if let Some(params) = class.type_parameters.as_ref() {
    let decls = lowerer.register_type_params(params);
    type_params = decls.iter().map(|decl| decl.id).collect();
  }

  let shape = lowerer.lower_type_members(&class.members);

  let mut types = Vec::new();
  let shape_id = store.intern_shape(shape);
  let obj = store.intern_object(ObjectType { shape: shape_id });
  types.push(store.intern_type(TypeKind::Object(obj)));

  if let Some(ext) = &class.extends {
    types.push(lowerer.lower_type_expr(ext));
  }
  for implemented in class.implements.iter() {
    types.push(lowerer.lower_type_expr(implemented));
  }

  let instance = if types.len() == 1 {
    types[0]
  } else {
    store.intersection(types)
  };
  let mut ctor_sigs = Vec::new();
  {
    let shape = store.shape(shape_id);
    for sig_id in shape.construct_signatures.iter().copied() {
      let mut sig = store.signature(sig_id).clone();
      sig.ret = instance;
      ctor_sigs.push(store.intern_signature(sig));
    }
  }
  if ctor_sigs.is_empty() {
    let sig = Signature {
      params: Vec::new(),
      ret: instance,
      type_params: Vec::new(),
      this_param: None,
    };
    ctor_sigs.push(store.intern_signature(sig));
  }
  let mut value_shape = Shape::new();
  value_shape.construct_signatures = ctor_sigs.clone();
  value_shape.call_signatures = ctor_sigs;
  let value_shape_id = store.intern_shape(value_shape);
  let value = store.intern_type(TypeKind::Object(store.intern_object(ObjectType {
    shape: value_shape_id,
  })));

  diagnostics.extend(lowerer.take_diagnostics());

  ClassTypeInfo {
    def,
    name: Some(class.name.clone()),
    instance,
    value,
    type_params,
  }
}

fn lower_runtime_class(
  store: &Arc<TypeStore>,
  resolver: Option<Arc<dyn TypeResolver>>,
  class: &ClassDecl,
  def: DefId,
  file: FileId,
  diagnostics: &mut Vec<Diagnostic>,
) -> Option<ClassTypeInfo> {
  let mut lowerer = match resolver.clone() {
    Some(resolver) => TypeLowerer::with_resolver(Arc::clone(store), resolver),
    None => TypeLowerer::new(Arc::clone(store)),
  };
  lowerer.set_file(file);

  let mut type_params = Vec::new();
  if let Some(params) = class.type_parameters.as_ref() {
    let decls = lowerer.register_type_params(params);
    type_params = decls.iter().map(|decl| decl.id).collect();
  }

  let mut instance_shape = Shape::new();
  let mut static_shape = Shape::new();
  lower_runtime_members(
    store,
    &mut lowerer,
    &mut instance_shape,
    &mut static_shape,
    &class.members,
  );

  let mut types = Vec::new();
  let shape_id = store.intern_shape(instance_shape);
  let obj = store.intern_object(ObjectType { shape: shape_id });
  types.push(store.intern_type(TypeKind::Object(obj)));

  if let Some(ext) = &class.extends {
    if let Some(base) = lower_runtime_type_expr(&mut lowerer, ext, resolver.as_ref()) {
      types.push(base);
    }
  }
  for implemented in class.implements.iter() {
    if let Some(base) = lower_runtime_type_expr(&mut lowerer, implemented, resolver.as_ref()) {
      types.push(base);
    }
  }

  let instance = if types.len() == 1 {
    types[0]
  } else {
    store.intersection(types)
  };
  let mut ctor_sigs = Vec::new();
  {
    let shape = store.shape(shape_id);
    for sig_id in shape.construct_signatures.iter().copied() {
      let mut sig = store.signature(sig_id).clone();
      sig.ret = instance;
      ctor_sigs.push(store.intern_signature(sig));
    }
  }
  if ctor_sigs.is_empty() {
    let sig = Signature {
      params: Vec::new(),
      ret: instance,
      type_params: Vec::new(),
      this_param: None,
    };
    ctor_sigs.push(store.intern_signature(sig));
  }
  let mut value_shape = static_shape;
  value_shape.construct_signatures = ctor_sigs.clone();
  value_shape.call_signatures = ctor_sigs;
  let value_shape_id = store.intern_shape(value_shape);
  let value = store.intern_type(TypeKind::Object(store.intern_object(ObjectType {
    shape: value_shape_id,
  })));

  diagnostics.extend(lowerer.take_diagnostics());

  Some(ClassTypeInfo {
    def,
    name: class.name.as_ref().map(|n| n.stx.name.clone()),
    instance,
    value,
    type_params,
  })
}

fn lower_runtime_type_expr(
  lowerer: &mut TypeLowerer,
  expr: &Node<AstExpr>,
  resolver: Option<&Arc<dyn TypeResolver>>,
) -> Option<TypeId> {
  match expr.stx.as_ref() {
    AstExpr::Id(id) => {
      if let Some(resolver) = resolver {
        if let Some(def) = resolver.resolve_type_name(&[id.stx.name.clone()]) {
          return Some(lowerer.store().intern_type(TypeKind::Ref {
            def,
            args: Vec::new(),
          }));
        }
      }
      None
    }
    _ => None,
  }
}

fn lower_runtime_members(
  store: &Arc<TypeStore>,
  lowerer: &mut TypeLowerer,
  instance_shape: &mut Shape,
  static_shape: &mut Shape,
  members: &[Node<ClassMember>],
) {
  for member in members.iter() {
    let shape = if member.stx.static_ {
      &mut *static_shape
    } else {
      &mut *instance_shape
    };
    let key = match class_member_key(store, &member.stx.key) {
      Some(key) => key,
      None => continue,
    };
    match &member.stx.val {
      ClassOrObjVal::Prop(_val) => {
        let ty = member
          .stx
          .type_annotation
          .as_ref()
          .map(|ann| lowerer.lower_type_expr(ann))
          .unwrap_or_else(|| store.primitive_ids().unknown);
        if std::env::var("DEBUG_CLASS_TYPING").is_ok() {
          eprintln!(
            "class member {:?} ty kind {:?}",
            member.stx.key,
            store.type_kind(ty)
          );
        }
        shape.properties.push(Property {
          key,
          data: PropData {
            ty,
            optional: member.stx.optional,
            readonly: member.stx.readonly,
            accessibility: map_accessibility(member.stx.accessibility),
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
      }
      ClassOrObjVal::Method(method) => {
        let sig = lower_func_signature(store, lowerer, &method.stx.func);
        let is_constructor = matches!(
          &member.stx.key,
          ClassOrObjKey::Direct(direct) if direct.stx.key == "constructor"
        );
        if is_constructor {
          static_shape.construct_signatures.push(sig);
          for param in method.stx.func.stx.parameters.iter() {
            if param.stx.accessibility.is_some() {
              if let parse_js::ast::expr::pat::Pat::Id(id) = param.stx.pattern.stx.pat.stx.as_ref() {
                let key = PropKey::String(store.intern_name(id.stx.name.clone()));
                let ty = param
                  .stx
                  .type_annotation
                  .as_ref()
                  .map(|ann| lowerer.lower_type_expr(ann))
                  .unwrap_or_else(|| store.primitive_ids().unknown);
                instance_shape.properties.push(Property {
                  key,
                  data: PropData {
                    ty,
                    optional: param.stx.optional,
                    readonly: param.stx.readonly,
                    accessibility: map_accessibility(param.stx.accessibility),
                    is_method: false,
                    origin: None,
                    declared_on: None,
                  },
                });
              }
            }
          }
        } else {
          let ty = store.intern_type(TypeKind::Callable {
            overloads: vec![sig],
          });
          shape.properties.push(Property {
            key,
            data: PropData {
              ty,
              optional: member.stx.optional,
              readonly: true,
              accessibility: map_accessibility(member.stx.accessibility),
              is_method: true,
              origin: None,
              declared_on: None,
            },
          });
        }
      }
      ClassOrObjVal::Getter(get) => {
        let ty = get
          .stx
          .func
          .stx
          .return_type
          .as_ref()
          .map(|ann| lowerer.lower_type_expr(ann))
          .unwrap_or_else(|| store.primitive_ids().unknown);
        shape.properties.push(Property {
          key,
          data: PropData {
            ty,
            optional: member.stx.optional,
            readonly: true,
            accessibility: map_accessibility(member.stx.accessibility),
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
      }
      ClassOrObjVal::Setter(set) => {
        let param_type = set
          .stx
          .func
          .stx
          .parameters
          .first()
          .and_then(|p| p.stx.type_annotation.as_ref())
          .map(|ann| lowerer.lower_type_expr(ann))
          .unwrap_or_else(|| store.primitive_ids().unknown);
        shape.properties.push(Property {
          key,
          data: PropData {
            ty: param_type,
            optional: member.stx.optional,
            readonly: false,
            accessibility: map_accessibility(member.stx.accessibility),
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
      }
      ClassOrObjVal::IndexSignature(idx) => {
        shape.indexers.push(Indexer {
          key_type: lowerer.lower_type_expr(&idx.stx.parameter_type),
          value_type: lowerer.lower_type_expr(&idx.stx.type_annotation),
          readonly: false,
        });
      }
      ClassOrObjVal::StaticBlock(_) => {}
    }
  }
}

fn lower_func_signature(
  store: &Arc<TypeStore>,
  lowerer: &mut TypeLowerer,
  func: &Node<Func>,
) -> types_ts_interned::SignatureId {
  lowerer.push_type_param_scope();
  let mut type_params = Vec::new();
  if let Some(params) = func.stx.type_parameters.as_ref() {
    type_params = lowerer.register_type_params(params);
  }
  let (this_param, params) = lower_params_from_decl(store, lowerer, &func.stx.parameters);
  let ret = func
    .stx
    .return_type
    .as_ref()
    .map(|ann| lowerer.lower_type_expr(ann))
    .unwrap_or_else(|| store.primitive_ids().unknown);
  let sig = Signature {
    params,
    ret,
    type_params,
    this_param,
  };
  lowerer.pop_type_param_scope();
  store.intern_signature(sig)
}

fn lower_params_from_decl(
  store: &Arc<TypeStore>,
  lowerer: &mut TypeLowerer,
  params: &[Node<ParamDecl>],
) -> (Option<TypeId>, Vec<SigParam>) {
  let mut lowered = Vec::new();
  let mut this_param = None;
  for param in params.iter() {
    let ty = param
      .stx
      .type_annotation
      .as_ref()
      .map(|ann| lowerer.lower_type_expr(ann))
      .unwrap_or_else(|| store.primitive_ids().unknown);
    let name = match param.stx.pattern.stx.pat.stx.as_ref() {
      parse_js::ast::expr::pat::Pat::Id(id) => Some(id.stx.name.clone()),
      _ => None,
    };
    if matches!(name.as_deref(), Some("this")) && this_param.is_none() {
      this_param = Some(ty);
      continue;
    }
    lowered.push(SigParam {
      name: name.map(|n| store.intern_name(n)),
      ty,
      optional: param.stx.optional,
      rest: param.stx.rest,
    });
  }
  (this_param, lowered)
}

fn class_member_key(store: &Arc<TypeStore>, key: &ClassOrObjKey) -> Option<PropKey> {
  match key {
    ClassOrObjKey::Direct(direct) => {
      if let Ok(num) = direct.stx.key.parse::<i64>() {
        Some(PropKey::Number(num))
      } else {
        Some(PropKey::String(store.intern_name(direct.stx.key.clone())))
      }
    }
    ClassOrObjKey::Computed(_) => None,
  }
}

fn loc_range(loc: Loc) -> TextRange {
  let (range, _) = loc.to_diagnostics_range_with_note();
  TextRange::new(range.start, range.end)
}

fn map_accessibility(acc: Option<ClassAccessibility>) -> Option<Accessibility> {
  match acc {
    Some(ClassAccessibility::Public) => Some(Accessibility::Public),
    Some(ClassAccessibility::Private) => Some(Accessibility::Private),
    Some(ClassAccessibility::Protected) => Some(Accessibility::Protected),
    None => None,
  }
}
