//! `#x in obj` — RHS checks, lexical private resolution, CFA narrowing.

use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{lower_from_source, Body, BodyId, DefKind, LowerResult, NameId, NameInterner};
use typecheck_ts::check::hir_body::check_body_with_env_with_bindings;
use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};
use types_ts_interned::{
  ObjectType, PropData, PropKey, Property, RelateCtx, Shape, TypeDisplay, TypeId, TypeKind,
  TypeStore,
};

fn diags(opts: CompilerOptions, src: &str) -> Vec<(String, String)> {
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| {
      let end = (d.primary.range.end as usize).min(src.len());
      let start = (d.primary.range.start as usize).min(end);
      (d.code.as_str().to_string(), src[start..end].to_string())
    })
    .collect();
  out.sort();
  out
}

fn codes(opts: CompilerOptions, src: &str) -> Vec<String> {
  diags(opts, src).into_iter().map(|(c, _)| c).collect()
}

fn opts() -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  opts
}

#[test]
fn private_in_on_any_is_ok() {
  let src = r#"
class Foo {
  #field = 1;
  good(v: any) {
    const a = #field in v;
  }
}
"#;
  let c = codes(opts(), src);
  assert!(
    !c.iter()
      .any(|x| x == "TS2304" || x == "TS2339" || x == "TS2571"),
    "legal #field in v must be quiet: {c:?}"
  );
}

#[test]
fn private_in_unknown_rhs_is_ts2571() {
  let src = r#"
class Foo {
  #field = 1;
  bad(v: any) {
    const a = #field in (v as unknown);
  }
}
"#;
  let d = diags(opts(), src);
  let hits: Vec<_> = d.iter().filter(|(c, _)| c == "TS2571").collect();
  assert_eq!(hits.len(), 1, "expected TS2571: {d:?}");
}

#[test]
fn undeclared_private_in_is_ts2339() {
  let src = r#"
class Foo {
  #field = 1;
  bad(v: any) {
    const b = #fiel in v;
  }
}
"#;
  let d = diags(opts(), src);
  let hits: Vec<_> = d.iter().filter(|(c, _)| c == "TS2339").collect();
  assert_eq!(hits.len(), 1, "expected TS2339: {d:?}");
  assert_eq!(hits[0].1, "#fiel");
  assert!(
    !d.iter().any(|(c, _)| c == "TS2304"),
    "must not be Cannot find name: {d:?}"
  );
}

#[test]
fn parenthesized_private_in_is_ts1451() {
  let src = r#"
class Foo {
  #field = 1;
  bad(v: any) {
    const c = (#field) in v;
  }
}
"#;
  let d = diags(opts(), src);
  let hits: Vec<_> = d.iter().filter(|(c, _)| c == "TS1451").collect();
  assert_eq!(hits.len(), 1, "expected TS1451: {d:?}");
}

#[test]
fn private_in_outside_class_is_ts18016() {
  let src = r#"
class Foo { #field = 1; }
function bad(v: Foo) {
  return #field in v;
}
"#;
  let c = codes(opts(), src);
  assert_eq!(c.iter().filter(|x| *x == "TS18016").count(), 1, "{c:?}");
}

#[test]
fn private_in_counts_as_brand_use() {
  // Mirrors conformance `privateNameInInExpressionUnused.ts` (without
  // noUnusedLocals — that option is not modeled yet). Recognizing `#brand in`
  // must not emit TS2304.
  let src = r#"
class Foo {
  #unused: undefined;
  #brand: undefined;
  isFoo(v: any): v is Foo {
    return #brand in v;
  }
}
"#;
  let c = codes(opts(), src);
  assert!(
    !c.iter().any(|x| x == "TS2304"),
    "#brand in v must resolve as private-in: {c:?}"
  );
}

#[test]
fn for_in_private_lhs_is_ts2406() {
  let src = r#"
class Foo {
  #field = 1;
  bad(v: any) {
    for (#field in v) { }
  }
}
"#;
  let c = codes(opts(), src);
  assert!(c.iter().any(|x| x == "TS2406"), "expected TS2406: {c:?}");
}

#[test]
fn for_in_boolean_rhs_is_ts2407() {
  let src = r#"
class Foo {
  #field = 1;
  bad(v: any) {
    for (let d in #field in v) { }
  }
}
"#;
  let c = codes(opts(), src);
  assert!(c.iter().any(|x| x == "TS2407"), "expected TS2407: {c:?}");
}

#[test]
fn private_in_flow_does_not_error_on_union_rhs() {
  // Full assignability CFA for `const ok: Foo = fb` still goes through the AST
  // checker (pre-flow). Here we only assert `#field in fb` is recognized so the
  // RHS is not a false TS2304 / the `in` expression itself is quiet.
  let src = r#"
class Foo {
  #field = 1;
  flow(fb: Foo | Bar) {
    if (#field in fb) {
      return fb;
    }
    return fb;
  }
}
class Bar { notFoo = true; }
"#;
  let c = codes(opts(), src);
  assert!(
    !c.iter().any(|x| x == "TS2304" || x == "TS2339"),
    "#field in fb on a union must resolve: {c:?}"
  );
}

fn name_id(names: &NameInterner, target: &str) -> NameId {
  let mut clone = names.clone();
  clone.intern(target)
}

fn body_of<'a>(lowered: &'a LowerResult, names: &NameInterner, func: &str) -> (BodyId, &'a Body) {
  let def = lowered
    .defs
    .iter()
    .find(|d| names.resolve(d.name) == Some(func) && d.path.kind == DefKind::Function)
    .unwrap_or_else(|| panic!("missing function {func}"));
  let body_id = def.body.expect("function body");
  (body_id, lowered.body(body_id).unwrap())
}

fn obj_type(store: &Arc<TypeStore>, props: &[(&str, TypeId)]) -> TypeId {
  let mut shape = Shape::new();
  for (name, ty) in props {
    shape.properties.push(Property {
      key: PropKey::String(store.intern_name(*name)),
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
  let shape_id = store.intern_shape(shape);
  let obj_id = store.intern_object(ObjectType { shape: shape_id });
  store.intern_type(TypeKind::Object(obj_id))
}

#[test]
fn private_in_cfa_narrows_union_in_flow_pass() {
  // Direct flow-pass unit test (tsc getNarrowedType checkDerived).
  let src = r#"
function flow(fb: object) {
  if (#field in fb) {
    return fb;
  }
  return fb;
}
"#;
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "flow");
  let store = TypeStore::new();
  let foo = obj_type(&store, &[("foo", store.primitive_ids().number)]);
  let bar = obj_type(&store, &[("bar", store.primitive_ids().boolean)]);
  let union = store.union(vec![foo, bar]);
  let mut initial = HashMap::new();
  initial.insert(name_id(lowered.names.as_ref(), "fb"), union);
  let mut private_in_targets = HashMap::new();
  private_in_targets.insert("#field".to_string(), foo);
  let relate = RelateCtx::new(Arc::clone(&store), store.options());
  let res = check_body_with_env_with_bindings(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
    None,
    relate,
    None,
    None,
    None,
    private_in_targets,
    None,
    false,
  );
  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, TypeDisplay::new(&store, foo).to_string());
  assert_eq!(else_ty, TypeDisplay::new(&store, bar).to_string());
}

#[test]
fn assign_to_in_recovers_as_ts1005() {
  // tsc: non-LHS `in` stops before `=`; ';' expected on `=` (TS1005).
  let src = r#"
class Foo {
  #field = 1;
  invalidLHS(v: any) {
    'prop' in v = 10;
    #field in v = 10;
  }
}
"#;
  let d = diags(opts(), src);
  let semis: Vec<_> = d
    .iter()
    .filter(|(c, t)| c == "PS0013" && t == "=")
    .collect();
  assert_eq!(semis.len(), 2, "expected two ';' expected on '=': {d:?}");
  assert!(
    !d.iter().any(|(c, _)| c == "PS0003"),
    "must not hard-fail invalid assignment target: {d:?}"
  );
}

#[test]
fn in_prec_shift_rhs_number_is_ts2322() {
  // `(v << #field) in (v << v)` — RHS number ↛ object.
  let src = r#"
class Foo {
  #field = 1;
  precedence(v: any) {
    v << #field in v << v;
  }
}
"#;
  let d = diags(opts(), src);
  let hits: Vec<_> = d
    .iter()
    .filter(|(c, t)| c == "TS2322" && t.contains("<<"))
    .collect();
  assert!(
    hits.iter().any(|(_, t)| *t == "v << v"),
    "expected TS2322 on 'v << v': {d:?}"
  );
}

#[test]
fn in_prec_boolean_lhs_is_ts2322() {
  // `v == ((#field in v) in v)` — boolean ↛ string|number|symbol.
  let src = r#"
class Foo {
  #field = 1;
  precedence(v: any) {
    v == #field in v in v;
  }
}
"#;
  let d = diags(opts(), src);
  let hits: Vec<_> = d
    .iter()
    .filter(|(c, t)| c == "TS2322" && t.contains("#field in v"))
    .collect();
  assert_eq!(hits.len(), 1, "expected TS2322 on '#field in v': {d:?}");
}

#[test]
fn transform_fixture_exact_codes_with_parse_errors() {
  // Mirrors conformance `privateNameInInExpressionTransform.ts` (minus emit).
  // Parse errors suppress private-name grammar diagnostics (tsc grammarErrorOnNode).
  let src = r#"
class Foo {
  #field = 1;
  #method() {}
  static #staticField = 2;
  static #staticMethod() {}
  check(v: any) {
    #field in v;
    #method in v;
    #staticField in v;
    #staticMethod in v;
  }
  precedence(v: any) {
    v == #field in v || v;
    v << #field in v << v;
    v << #field in v == v;
    v == #field in v in v;
    #field in v && #field in v;
  }
  invalidLHS(v: any) {
    'prop' in v = 10;
    #field in v = 10;
  }
}
class Bar {
  #field = 1;
  check(v: any) {
    #field in v;
  }
}
function syntaxError(v: Foo) {
  return #field in v;
}
export {};
"#;
  let c = codes(opts(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2322").count(),
    2,
    "expected two TS2322: {c:?}"
  );
  assert_eq!(
    c.iter().filter(|x| *x == "PS0013").count(),
    2,
    "expected two PS0013: {c:?}"
  );
  assert!(
    !c.iter()
      .any(|x| *x == "TS18016" || *x == "TS1451" || *x == "PS0003" || *x == "TS2304"),
    "parse errors must suppress private grammar / not PS0003/TS2304: {c:?}"
  );
}
