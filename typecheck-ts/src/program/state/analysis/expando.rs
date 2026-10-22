//! JS "expando" property-assignment namespace members (tsc
//! `bindSpecialPropertyAssignment`).
//!
//! In `.js`/`.jsx` files under `checkJs`, assignments of the form
//! `Outer.X = <class | function>` and `Outer.X.prototype = <object literal>`
//! where `Outer` is a top-level `var Outer = {}` (empty object literal, no
//! annotation) register `X` as a member of `Outer`'s expando namespace. tsc
//! binds these in both the value and type namespaces, so `new Outer.X()`,
//! `Outer.X` property access, and JSDoc `@type {Outer.X}` all resolve
//! (`typeFromPropertyAssignment24`, `jsdocTypeReferenceToMergedClass`).
//!
//! This module scans JS sources for the pattern ([`scan_js_expando_file`])
//! and registers the members ([`ProgramState::register_js_expando_members`]):
//!
//! - class RHS: the class expression's own defs are reused —
//!   `qualified_def_members[(outer, X, TYPE)] = class def` (so `Ref` gives the
//!   instance) and `[(outer, X, VALUE)] = synthetic value def` (constructor);
//! - function RHS: a synthetic def pair is created — a type-side def whose
//!   type is the prototype instance type and a value-side def whose type is a
//!   JS-constructor object (`new (params): instance`, plus `prototype`);
//! - the outer var's type is augmented with an object carrying each member so
//!   the value side (`Outer.X`, `new Outer.X()`) checks through ordinary
//!   member/construct paths.
//!
//! Registration never invokes body checking: member types are built directly
//! from AST shapes (prototype object literal members, function params).

use super::*;

use parse_js::ast::class_or_object::{ClassOrObjKey, ObjMemberType};
use parse_js::ast::func::FuncBody;
use parse_js::operator::OperatorName;

/// Return type of a prototype-object method, inferred from top-level `return`
/// statements only (no control-flow analysis): all value returns sharing one
/// primitive literal kind give that (widened) primitive, no value returns give
/// `void`, anything else gives `any`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum SimpleRet {
  Void,
  Str,
  Num,
  Bool,
  Any,
}

impl SimpleRet {
  fn ty(self, store: &tti::TypeStore) -> TypeId {
    let prim = store.primitive_ids();
    match self {
      SimpleRet::Void => prim.void,
      SimpleRet::Str => prim.string,
      SimpleRet::Num => prim.number,
      SimpleRet::Bool => prim.boolean,
      SimpleRet::Any => prim.any,
    }
  }

  fn join(self, other: SimpleRet) -> SimpleRet {
    if self == other {
      self
    } else {
      SimpleRet::Any
    }
  }
}

/// A function/method parameter used to synthesize JS-constructor signatures.
/// Types are `any` (JS params are unannotated); tsc treats them as optional
/// (`new F()` arity is `0-n`).
struct ExpandoParam {
  name: String,
  rest: bool,
}

/// Classified RHS of an expando member assignment.
enum ExpandoRhs {
  /// `Outer.X = class { … }` — the class expression has its own defs.
  Class,
  /// `Outer.X = function …(params) { … }`.
  Function {
    params: Vec<ExpandoParam>,
    ret: SimpleRet,
  },
  /// `Outer.X.prototype = { … }` — object literal with method/prop members.
  Object { members: Vec<ExpandoObjMember> },
  /// Anything else (arrows, literals, calls): not registered.
  Other,
}

struct ExpandoObjMember {
  name: String,
  kind: ExpandoObjMemberKind,
}

enum ExpandoObjMemberKind {
  Method {
    params: Vec<ExpandoParam>,
    ret: SimpleRet,
  },
  Prop {
    ret: SimpleRet,
  },
}

/// One `Outer.path = rhs` top-level assignment recorded from a JS file.
struct ExpandoAssignment {
  file: FileId,
  outer: String,
  /// Member path after the head: `[X]` or `[X, "prototype"]`. Deeper paths
  /// (nested statics like `Outer.X.Y = …`) are recorded but skipped.
  path: Vec<String>,
  rhs: ExpandoRhs,
  /// Span of the assignment RHS expression (matches the class-expression def
  /// span for class RHS).
  rhs_span: TextRange,
  /// Span of the assignment LHS (`Outer.X`), used for synthetic member defs.
  lhs_span: TextRange,
}

#[derive(Default)]
struct ExpandoFileScan {
  /// Names of top-level expando bases: `var X = {}` (empty object literal, no
  /// type annotation, no leading JSDoc `@type`), `var X = function … {}`, and
  /// `function X() {}` declarations (tsc `bindSpecialPropertyAssignment`).
  empty_object_vars: Vec<String>,
  assignments: Vec<ExpandoAssignment>,
}

/// Registered expando member kind before type synthesis.
enum ExpandoMemberKind {
  Class(DefId),
  Function {
    params: Vec<ExpandoParam>,
    ret: SimpleRet,
  },
}

struct ExpandoMemberReg {
  kind: ExpandoMemberKind,
  file: FileId,
  span: TextRange,
}

/// Scan one JS/JSX file's top-level statements for expando declarations and
/// property assignments. Pure AST analysis: no defs, no types.
fn scan_js_expando_file(file: FileId, ast: &Node<TopLevel>, source: &str) -> ExpandoFileScan {
  let mut scan = ExpandoFileScan::default();
  for stmt in ast.stx.body.iter() {
    match stmt.stx.as_ref() {
      Stmt::VarDecl(decl) => {
        for declarator in decl.stx.declarators.iter() {
          if declarator.type_annotation.is_some() {
            continue;
          }
          let Pat::Id(id) = declarator.pattern.stx.pat.stx.as_ref() else {
            continue;
          };
          let Some(init) = declarator.initializer.as_ref() else {
            continue;
          };
          let is_expando_base = match init.stx.as_ref() {
            // `var X = {}` (empty object literal): members merge onto the
            // object type.
            Expr::LitObj(obj) => obj.stx.members.is_empty(),
            // `var X = function … {}` / `function X() {}` / `var X = class …` /
            // `var X = (…) => …`: tsc `bindSpecialPropertyAssignment` treats
            // all of these as expando containers in JS (`Outer.Inner = class …`
            // resolves in value *and* type positions —
            // `salsa/typeFromPropertyAssignment.ts`).
            Expr::Func(_) | Expr::Class(_) | Expr::ArrowFunc(_) => true,
            _ => false,
          };
          if !is_expando_base {
            continue;
          }
          // A leading JSDoc `@type` counts as a type annotation (tsc
          // `getEffectiveTypeAnnotationNode`): the var is not expando.
          if crate::jsdoc::leading_type_tag(source, stmt.loc.0 as u32).is_some() {
            continue;
          }
          scan.empty_object_vars.push(id.stx.name.clone());
        }
      }
      Stmt::FunctionDecl(func) => {
        // `function X() {}` is an expando container too (same tsc mechanism):
        // `X.Member = …` augments the function (value *and* JSDoc-type
        // positions, `salsa/typeFromPropertyAssignment2.ts`).
        if let Some(name) = func.stx.name.as_ref() {
          scan.empty_object_vars.push(name.stx.name.clone());
        }
      }
      Stmt::Expr(expr_stmt) => {
        let Expr::Binary(bin) = expr_stmt.stx.expr.stx.as_ref() else {
          continue;
        };
        if !matches!(bin.stx.operator, OperatorName::Assignment) {
          continue;
        }
        let Some((outer, path)) = member_assign_path(&bin.stx.left) else {
          continue;
        };
        if path.is_empty() {
          continue;
        }
        scan.assignments.push(ExpandoAssignment {
          file,
          outer,
          path,
          rhs: classify_rhs(&bin.stx.right),
          rhs_span: loc_to_text_range(bin.stx.right.loc),
          lhs_span: loc_to_text_range(bin.stx.left.loc),
        });
      }
      _ => {}
    }
  }
  scan
}

fn loc_to_text_range(loc: Loc) -> TextRange {
  TextRange::new(
    loc.0.min(u32::MAX as usize) as u32,
    loc.1.min(u32::MAX as usize) as u32,
  )
}

/// Decompose `Outer.A.B` into `("Outer", ["A", "B"])`. Only plain (non-
/// optional, non-computed) member segments; returns `None` otherwise.
fn member_assign_path(expr: &Node<Expr>) -> Option<(String, Vec<String>)> {
  match expr.stx.as_ref() {
    Expr::Member(member) if !member.stx.optional_chaining => {
      let (head, mut path) = member_assign_path(&member.stx.left)?;
      path.push(member.stx.right.clone());
      Some((head, path))
    }
    Expr::Id(id) => Some((id.stx.name.clone(), Vec::new())),
    _ => None,
  }
}

fn classify_rhs(rhs: &Node<Expr>) -> ExpandoRhs {
  match rhs.stx.as_ref() {
    Expr::Class(_) => ExpandoRhs::Class,
    Expr::Func(func) => ExpandoRhs::Function {
      params: expando_params(&func.stx.func),
      ret: infer_simple_ret(&func.stx.func),
    },
    Expr::LitObj(obj) => ExpandoRhs::Object {
      members: object_members(obj),
    },
    _ => ExpandoRhs::Other,
  }
}

fn expando_params(func: &Node<Func>) -> Vec<ExpandoParam> {
  func
    .stx
    .parameters
    .iter()
    .map(|param| {
      let name = match param.stx.pattern.stx.pat.stx.as_ref() {
        Pat::Id(id) => id.stx.name.clone(),
        _ => String::new(),
      };
      ExpandoParam {
        name,
        rest: param.stx.rest,
      }
    })
    .collect()
}

fn object_members(obj: &Node<parse_js::ast::expr::lit::LitObjExpr>) -> Vec<ExpandoObjMember> {
  let mut out = Vec::new();
  for member in obj.stx.members.iter() {
    let ObjMemberType::Valued { key, val } = &member.stx.typ else {
      continue;
    };
    let ClassOrObjKey::Direct(key) = key else {
      continue;
    };
    let name = key.stx.key.clone();
    match val {
      ClassOrObjVal::Method(method) => out.push(ExpandoObjMember {
        name,
        kind: ExpandoObjMemberKind::Method {
          params: expando_params(&method.stx.func),
          ret: infer_simple_ret(&method.stx.func),
        },
      }),
      ClassOrObjVal::Prop(Some(init)) => out.push(ExpandoObjMember {
        name,
        kind: ExpandoObjMemberKind::Prop {
          ret: simple_expr_ret(init),
        },
      }),
      _ => {}
    }
  }
  out
}

fn simple_expr_ret(expr: &Node<Expr>) -> SimpleRet {
  match expr.stx.as_ref() {
    Expr::LitStr(_) => SimpleRet::Str,
    Expr::LitNum(_) => SimpleRet::Num,
    Expr::LitBool(_) => SimpleRet::Bool,
    _ => SimpleRet::Any,
  }
}

/// Very small return-type inference for prototype-object methods: scan
/// top-level (non-nested-function) `return` statements. `void` when no return
/// produces a value, the shared widened primitive when all value returns are
/// the same literal kind, otherwise `any`.
fn infer_simple_ret(func: &Node<Func>) -> SimpleRet {
  let Some(FuncBody::Block(stmts)) = func.stx.body.as_ref() else {
    return SimpleRet::Void;
  };
  let mut acc: Option<SimpleRet> = None;
  collect_return_kinds(stmts, &mut acc);
  acc.unwrap_or(SimpleRet::Void)
}

fn collect_return_kinds(stmts: &[Node<Stmt>], acc: &mut Option<SimpleRet>) {
  for stmt in stmts {
    match stmt.stx.as_ref() {
      Stmt::Return(ret) => {
        let kind = ret
          .stx
          .value
          .as_ref()
          .map(simple_expr_ret)
          .unwrap_or(SimpleRet::Any);
        *acc = Some(match *acc {
          None => kind,
          Some(existing) => existing.join(kind),
        });
      }
      Stmt::Block(block) => collect_return_kinds(&block.stx.body, acc),
      Stmt::If(if_stmt) => {
        collect_return_kinds(std::slice::from_ref(&if_stmt.stx.consequent), acc);
        if let Some(alternate) = if_stmt.stx.alternate.as_ref() {
          collect_return_kinds(std::slice::from_ref(alternate), acc);
        }
      }
      _ => {}
    }
  }
}

/// Signature params for a synthesized JS-constructor / method: all `any` and
/// optional (tsc treats JS params as optional, arity `0-n`).
fn expando_sig_params(store: &tti::TypeStore, params: &[ExpandoParam]) -> Vec<tti::Param> {
  let any = store.primitive_ids().any;
  params
    .iter()
    .map(|param| tti::Param {
      name: Some(store.intern_name(param.name.clone())),
      ty: any,
      optional: !param.rest,
      rest: param.rest,
    })
    .collect()
}

fn object_type_from_shape(store: &tti::TypeStore, shape: tti::Shape) -> TypeId {
  let shape_id = store.intern_shape(shape);
  let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
  store.intern_type(tti::TypeKind::Object(obj_id))
}

/// Instance type for a function-RHS expando member: the shape of its
/// `Outer.X.prototype = { … }` object literal, or `{}` when absent/not an
/// object literal.
fn prototype_instance_type(
  store: &tti::TypeStore,
  members: Option<&Vec<ExpandoObjMember>>,
) -> TypeId {
  let mut shape = tti::Shape::new();
  if let Some(members) = members {
    let mut sorted: Vec<&ExpandoObjMember> = members.iter().collect();
    sorted.sort_by(|a, b| a.name.cmp(&b.name));
    for member in sorted {
      let (ty, is_method) = match &member.kind {
        ExpandoObjMemberKind::Method { params, ret } => {
          let sig = tti::Signature {
            params: expando_sig_params(store, params),
            ret: ret.ty(store),
            type_params: Vec::new(),
            this_param: None,
          };
          let sig_id = store.intern_signature(sig);
          (
            store.intern_type(tti::TypeKind::Callable {
              overloads: vec![sig_id],
            }),
            true,
          )
        }
        ExpandoObjMemberKind::Prop { ret } => (ret.ty(store), false),
      };
      shape.properties.push(Property {
        key: PropKey::String(store.intern_name(member.name.clone())),
        data: PropData {
          ty,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method,
          origin: None,
          declared_on: None,
        },
      });
    }
  }
  object_type_from_shape(store, shape)
}

/// Value-side type of a function-RHS expando member that has a
/// `Outer.X.prototype = { … }` assignment: a JS-constructor object
/// (`new (params): instance`) with a `prototype` property (tsc exposes the
/// instance type as `Fn.prototype`). It also keeps a call signature returning
/// `any` — tsc permits calling JS constructor functions directly.
fn js_constructor_type(
  store: &tti::TypeStore,
  params: &[ExpandoParam],
  instance: TypeId,
) -> TypeId {
  let prim = store.primitive_ids();
  let call_sig = tti::Signature {
    params: expando_sig_params(store, params),
    ret: prim.any,
    type_params: Vec::new(),
    this_param: None,
  };
  let new_sig = tti::Signature {
    params: expando_sig_params(store, params),
    ret: instance,
    type_params: Vec::new(),
    this_param: None,
  };
  let mut shape = tti::Shape::new();
  shape.call_signatures.push(store.intern_signature(call_sig));
  shape
    .construct_signatures
    .push(store.intern_signature(new_sig));
  shape.properties.push(Property {
    key: PropKey::String(store.intern_name("prototype")),
    data: PropData {
      ty: instance,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  });
  object_type_from_shape(store, shape)
}

/// Value-side type of a function-RHS expando member *without* a prototype
/// assignment: a plain function — call signature `(params): ret` (tsc infers
/// the return from the body; we use the top-level-return approximation from
/// [`SimpleRet`]). tsc still allows `new` on it (the instance type is
/// effectively `any`), so a construct signature returning `any` is included,
/// plus a `prototype: any` property (lib `Function.prototype`).
fn js_plain_function_type(
  store: &tti::TypeStore,
  params: &[ExpandoParam],
  ret: SimpleRet,
) -> TypeId {
  let prim = store.primitive_ids();
  let call_sig = tti::Signature {
    params: expando_sig_params(store, params),
    ret: ret.ty(store),
    type_params: Vec::new(),
    this_param: None,
  };
  let new_sig = tti::Signature {
    params: expando_sig_params(store, params),
    ret: prim.any,
    type_params: Vec::new(),
    this_param: None,
  };
  let mut shape = tti::Shape::new();
  shape.call_signatures.push(store.intern_signature(call_sig));
  shape
    .construct_signatures
    .push(store.intern_signature(new_sig));
  shape.properties.push(Property {
    key: PropKey::String(store.intern_name("prototype")),
    data: PropData {
      ty: prim.any,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  });
  object_type_from_shape(store, shape)
}

impl ProgramState {
  /// Resolve the expando candidate `Outer` (referenced from `file`) to the var
  /// defs confirmed as `var Outer = {}` declarations. Returns every matching
  /// decl def (a global var can be redeclared across script files); empty when
  /// the head is not an expando var.
  fn resolve_js_expando_outer_defs(
    &self,
    file: FileId,
    name: &str,
    expando_var_decls: &HashSet<(FileId, String)>,
  ) -> Vec<DefId> {
    let Some(semantics) = self.semantics.as_deref() else {
      return Vec::new();
    };
    let symbol = semantics
      .resolve_in_module(sem_ts::FileId(file.0), name, sem_ts::Namespace::VALUE)
      .or_else(|| {
        semantics
          .global_symbols()
          .get(name)
          .and_then(|group| group.symbol_for(sem_ts::Namespace::VALUE, semantics.symbols()))
      });
    let Some(symbol) = symbol else {
      return Vec::new();
    };
    let mut defs: Vec<DefId> = semantics
      .symbol_decls(symbol, sem_ts::Namespace::VALUE)
      .iter()
      .filter_map(|decl_id| {
        let decl = semantics.symbols().decl(*decl_id);
        self.map_decl_to_program_def(decl, sem_ts::Namespace::VALUE)
      })
      .filter(|def| {
        self
          .def_data
          .get(def)
          .is_some_and(|data| expando_var_decls.contains(&(data.file, data.name.clone())))
      })
      .collect();
    defs.sort_by_key(|def| def.0);
    defs.dedup();
    defs
  }

  /// Find the class-expression def for an expando class RHS by span.
  fn find_class_expr_def(&self, file: FileId, span: TextRange) -> Option<DefId> {
    let lowered = self.hir_lowered.get(&file)?;
    lowered
      .defs
      .iter()
      .filter(|def| matches!(def.path.kind, HirDefKind::Class) && def.span == span)
      .map(|def| def.id)
      .min_by_key(|id| id.0)
  }

  /// Register JS expando property-assignment members (tsc
  /// `bindSpecialPropertyAssignment`).
  ///
  /// Runs inside [`ProgramState::ensure_interned_types`] after
  /// `canonical_defs`: extends `qualified_def_members` so the resolver finds
  /// `Outer.X` in TYPE/VALUE namespaces, synthesizes defs + types for
  /// function-RHS members, and augments the outer var's type — directly in
  /// `def_types[outer]` (the namespace-merge machinery's `(file, None, name)`
  /// lookup misses vars, whose HIR parent is the `VarDeclarator` container)
  /// and via `namespace_types` so `type_of_def(outer)` recomputations keep the
  /// members. Never calls `check_body` — member types are built from AST
  /// shapes and already-lowered declaration types.
  pub(in super::super) fn register_js_expando_members(
    &mut self,
    store: &Arc<tti::TypeStore>,
    qualified_def_members: &mut HashMap<(DefId, String, sem_ts::Namespace), DefId>,
    def_types: &mut HashMap<DefId, tti::TypeId>,
    namespace_types: &mut HashMap<(FileId, String), TypeId>,
  ) -> Result<(), FatalError> {
    self.expando_members.clear();
    if self.compiler_options.check_js != Some(true) {
      return Ok(());
    }
    self.check_cancelled()?;

    // Phase 1: scan JS/JSX sources.
    let mut js_files: Vec<FileId> = Vec::new();
    for (file, kind) in self.file_kinds.iter() {
      if matches!(kind, FileKind::Js | FileKind::Jsx) && self.asts.contains_key(file) {
        js_files.push(*file);
      }
    }
    js_files.sort_by_key(|file| file.0);

    let mut expando_var_decls: HashSet<(FileId, String)> = HashSet::new();
    let mut assignments: Vec<ExpandoAssignment> = Vec::new();
    for file in js_files {
      let Some(ast) = self.asts.get(&file).cloned() else {
        continue;
      };
      let text = db::file_text(&self.typecheck_db, file);
      let scan = scan_js_expando_file(file, ast.as_ref(), text.as_ref());
      for name in scan.empty_object_vars {
        expando_var_decls.insert((file, name));
      }
      assignments.extend(scan.assignments);
    }
    if assignments.is_empty() {
      return Ok(());
    }
    assignments.sort_by(|a, b| {
      (a.file.0, a.rhs_span.start, a.rhs_span.end).cmp(&(
        b.file.0,
        b.rhs_span.start,
        b.rhs_span.end,
      ))
    });

    // Phase 2: group member and prototype assignments by canonical outer def.
    // The outer head resolves through semantic-js, so members from every file
    // merge onto the same canonical (global) var def.
    let mut members: BTreeMap<(DefId, String), ExpandoMemberReg> = BTreeMap::new();
    let mut prototypes: BTreeMap<(DefId, String), Vec<ExpandoObjMember>> = BTreeMap::new();
    for record in assignments.iter() {
      self.check_cancelled()?;
      let outer_defs =
        self.resolve_js_expando_outer_defs(record.file, &record.outer, &expando_var_decls);
      if outer_defs.is_empty() {
        continue;
      }
      match record.path.as_slice() {
        [member] => {
          for outer_def in outer_defs.iter().copied() {
            let key = (outer_def, member.clone());
            if members.contains_key(&key) {
              continue;
            }
            let kind = match &record.rhs {
              ExpandoRhs::Class => self
                .find_class_expr_def(record.file, record.rhs_span)
                .map(ExpandoMemberKind::Class),
              ExpandoRhs::Function { params, ret } => Some(ExpandoMemberKind::Function {
                params: clone_params(params),
                ret: *ret,
              }),
              // Arrows, literals, calls, and other expressions are not
              // registered (the assignment itself stays silent because the
              // member is not on the outer var's type either).
              _ => None,
            };
            if let Some(kind) = kind {
              members.insert(
                key,
                ExpandoMemberReg {
                  kind,
                  file: record.file,
                  span: record.lhs_span,
                },
              );
            }
          }
        }
        [member, tail] if tail == "prototype" => {
          let ExpandoRhs::Object {
            members: proto_members,
          } = &record.rhs
          else {
            continue;
          };
          for outer_def in outer_defs.iter().copied() {
            prototypes
              .entry((outer_def, member.clone()))
              .or_insert_with(|| clone_obj_members(proto_members));
          }
        }
        _ => {}
      }
    }

    // Phase 3: register members and collect the outer var's member object.
    // Member property types are `Ref{value_def}` (not the ctor type itself)
    // so later refinement passes (e.g. unannotated method-return inference in
    // `refine_class_method_property_types`) stay visible — `Ref` expansion
    // reads the final `interned_def_types`.
    let mut outer_props: BTreeMap<DefId, BTreeMap<String, TypeId>> = BTreeMap::new();
    let mut taken_ids: HashSet<DefId> = self.def_data.keys().copied().collect();
    for ((outer_def, member), reg) in members.iter() {
      self.check_cancelled()?;
      match &reg.kind {
        ExpandoMemberKind::Class(class_def) => {
          let class_def = *class_def;
          // The class def holds the *instance* type (`Ref{class}` for
          // `@type {Outer.X}`); the synthetic value def holds the constructor
          // (`new Outer.X()`).
          let value_def = self
            .value_defs
            .get(&class_def)
            .copied()
            .unwrap_or(class_def);
          qualified_def_members.insert(
            (*outer_def, member.clone(), sem_ts::Namespace::TYPE),
            class_def,
          );
          qualified_def_members.insert(
            (*outer_def, member.clone(), sem_ts::Namespace::VALUE),
            value_def,
          );
          outer_props.entry(*outer_def).or_default().insert(
            member.clone(),
            store.intern_type(tti::TypeKind::Ref {
              def: value_def,
              args: Vec::new(),
            }),
          );
        }
        ExpandoMemberKind::Function { params, ret } => {
          // With a `Outer.X.prototype = {…}` assignment the member is a JS
          // constructor function (tsc: `new Outer.X()` = prototype instance,
          // `@type {Outer.X}` = instance). Without one it is a plain function
          // (callable; `@type {Outer.X}` = the function type).
          let prototype = prototypes.get(&(*outer_def, member.clone()));
          let (type_side_ty, value_side_ty) = match prototype {
            Some(_) => {
              let instance_ty = prototype_instance_type(store, prototype);
              (instance_ty, js_constructor_type(store, params, instance_ty))
            }
            None => {
              let fn_ty = js_plain_function_type(store, params, *ret);
              (fn_ty, fn_ty)
            }
          };
          let type_def = alloc_synthetic_def_id(
            reg.file,
            &mut taken_ids,
            &("ts_expando_type", outer_def.0, member.as_str()),
          );
          let value_def = alloc_synthetic_def_id(
            reg.file,
            &mut taken_ids,
            &("ts_expando_value", outer_def.0, member.as_str()),
          );
          let symbol = self.alloc_symbol();
          self.def_data.insert(
            type_def,
            DefData {
              name: member.clone(),
              file: reg.file,
              span: reg.span,
              symbol,
              export: false,
              kind: DefKind::TypeAlias(TypeAliasData { typ: type_side_ty }),
            },
          );
          self.def_data.insert(
            value_def,
            DefData {
              name: member.clone(),
              file: reg.file,
              span: reg.span,
              symbol,
              export: false,
              kind: DefKind::Var(VarData {
                typ: None,
                init: None,
                body: MISSING_BODY,
                mode: VarDeclMode::Let,
              }),
            },
          );
          self.value_defs.insert(type_def, value_def);
          def_types.insert(type_def, type_side_ty);
          def_types.insert(value_def, value_side_ty);
          qualified_def_members.insert(
            (*outer_def, member.clone(), sem_ts::Namespace::TYPE),
            type_def,
          );
          qualified_def_members.insert(
            (*outer_def, member.clone(), sem_ts::Namespace::VALUE),
            value_def,
          );
          outer_props.entry(*outer_def).or_default().insert(
            member.clone(),
            store.intern_type(tti::TypeKind::Ref {
              def: value_def,
              args: Vec::new(),
            }),
          );
        }
      }
      self
        .expando_members
        .entry(*outer_def)
        .or_default()
        .insert(member.clone());
    }

    // Phase 4: augment each outer var's type with its member object. Merge
    // into `def_types[outer]` directly: the namespace-merge machinery in
    // `ensure_interned_types` looks up `(file, None, name)`, which misses vars
    // (their HIR parent is the `VarDeclarator` container, not `None`). The
    // `namespace_types` entry keeps `type_of_def(outer)` recomputations
    // lossless (the member object is intersected back onto the `{}`
    // initializer type).
    for (outer_def, props) in outer_props.iter() {
      let Some(data) = self.def_data.get(outer_def) else {
        continue;
      };
      let mut shape = tti::Shape::new();
      for (name, ty) in props.iter() {
        shape.properties.push(Property {
          key: PropKey::String(store.intern_name(name.clone())),
          data: PropData {
            ty: *ty,
            optional: false,
            readonly: false,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
      }
      let ty = object_type_from_shape(store, shape);
      def_types
        .entry(*outer_def)
        .and_modify(|existing| {
          *existing = ProgramState::merge_interned_decl_types(store, *existing, ty);
        })
        .or_insert(ty);
      namespace_types
        .entry((data.file, data.name.clone()))
        .and_modify(|existing| {
          *existing = ProgramState::merge_interned_object_types(store, *existing, ty);
        })
        .or_insert(ty);
    }
    Ok(())
  }
}

fn clone_params(params: &[ExpandoParam]) -> Vec<ExpandoParam> {
  params
    .iter()
    .map(|param| ExpandoParam {
      name: param.name.clone(),
      rest: param.rest,
    })
    .collect()
}

fn clone_obj_members(members: &[ExpandoObjMember]) -> Vec<ExpandoObjMember> {
  members
    .iter()
    .map(|member| ExpandoObjMember {
      name: member.name.clone(),
      kind: match &member.kind {
        ExpandoObjMemberKind::Method { params, ret } => ExpandoObjMemberKind::Method {
          params: clone_params(params),
          ret: *ret,
        },
        ExpandoObjMemberKind::Prop { ret } => ExpandoObjMemberKind::Prop { ret: *ret },
      },
    })
    .collect()
}
