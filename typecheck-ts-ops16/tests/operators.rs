use typecheck_ts_ops16::Env;
use typecheck_ts_ops16::MappedModifier;
use typecheck_ts_ops16::Normalizer;
use typecheck_ts_ops16::Property;
use typecheck_ts_ops16::TemplatePart;
use typecheck_ts_ops16::TypeDisplay;
use typecheck_ts_ops16::TypeId;
use typecheck_ts_ops16::TypeStore;

fn display(store: &TypeStore, ty: TypeId) -> String {
  TypeDisplay::new(store).fmt(ty)
}

#[test]
fn conditional_distributes_over_union() {
  let mut store = TypeStore::new();
  let t = store.type_param("T");
  let string_ty = store.string();
  let number_ty = store.number();
  let boolean_ty = store.boolean();
  let cond = store.conditional(t, string_ty, number_ty, boolean_ty, Some(t));
  let mut env = Env::new();
  let lit_a = store.literal_string("a");
  let arg_union = store.union(vec![lit_a, number_ty]);
  env.insert(t, arg_union);

  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(cond, &env);
  drop(norm);

  assert_eq!(display(&store, result), "boolean | number");
}

#[test]
fn conditional_non_distributive_union() {
  let mut store = TypeStore::new();
  let string_ty = store.string();
  let number_ty = store.number();
  let check = store.union(vec![string_ty, number_ty]);
  let cond = store.conditional(
    check,
    string_ty,
    store.true_type(),
    store.false_type(),
    None,
  );
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(cond, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "false");
}

#[test]
fn conditional_true_branch() {
  let mut store = TypeStore::new();
  let string_ty = store.string();
  let yes = store.literal_string("yes");
  let no = store.literal_string("no");
  let cond = store.conditional(string_ty, string_ty, yes, no, None);
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(cond, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "\"yes\"");
}

#[test]
fn template_literal_distribution() {
  let mut store = TypeStore::new();
  let lit_a = store.literal_string("a");
  let lit_b = store.literal_string("b");
  let lit_c = store.literal_string("c");
  let lit_d = store.literal_string("d");
  let left = store.union(vec![lit_a, lit_b]);
  let right = store.union(vec![lit_c, lit_d]);
  let tpl = store.template(vec![TemplatePart::Type(left), TemplatePart::Type(right)]);
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(tpl, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "\"ac\" | \"ad\" | \"bc\" | \"bd\"");
}

#[test]
fn template_literal_fallback_to_string() {
  let mut store = TypeStore::new();
  let string_ty = store.string();
  let tpl = store.template(vec![
    TemplatePart::Literal("foo".into()),
    TemplatePart::Type(string_ty),
  ]);
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(tpl, &Env::new());
  let diags = norm.diagnostics().to_vec();
  drop(norm);
  assert_eq!(display(&store, result), "string");
  assert!(!diags.is_empty());
}

#[test]
fn indexed_access_union_key() {
  let mut store = TypeStore::new();
  let string_ty = store.string();
  let number_ty = store.number();
  let obj = store.object(vec![
    ("a".into(), Property {
      ty: string_ty,
      optional: false,
      readonly: false,
    }),
    ("b".into(), Property {
      ty: number_ty,
      optional: false,
      readonly: false,
    }),
  ]);
  let lit_a = store.literal_string("a");
  let lit_b = store.literal_string("b");
  let idx = store.union(vec![lit_a, lit_b]);
  let access = store.indexed_access(obj, idx);
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(access, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "number | string");
}

#[test]
fn indexed_access_missing_property_yields_unknown() {
  let mut store = TypeStore::new();
  let string_ty = store.string();
  let obj = store.object(vec![("a".into(), Property {
    ty: string_ty,
    optional: false,
    readonly: false,
  })]);
  let lit_b = store.literal_string("b");
  let access = store.indexed_access(obj, lit_b);
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(access, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "unknown");
}

#[test]
fn indexed_access_distributes_over_object_union() {
  let mut store = TypeStore::new();
  let string_ty = store.string();
  let number_ty = store.number();
  let a = store.object(vec![("a".into(), Property {
    ty: string_ty,
    optional: false,
    readonly: false,
  })]);
  let b = store.object(vec![("a".into(), Property {
    ty: number_ty,
    optional: false,
    readonly: false,
  })]);
  let obj_union = store.union(vec![a, b]);
  let lit_a = store.literal_string("a");
  let access = store.indexed_access(obj_union, lit_a);
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(access, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "number | string");
}

#[test]
fn mapped_type_basic_keys() {
  let mut store = TypeStore::new();
  let k = store.type_param("K");
  let lit_a = store.literal_string("a");
  let lit_b = store.literal_string("b");
  let keys = store.union(vec![lit_a, lit_b]);
  let mapped = store.mapped(
    k,
    keys,
    store.number(),
    None,
    MappedModifier::Inherit,
    MappedModifier::Inherit,
  );
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(mapped, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "{ a: number; b: number }");
}

#[test]
fn mapped_optional_and_readonly() {
  let mut store = TypeStore::new();
  let k = store.type_param("K");
  let lit_a = store.literal_string("a");
  let string_ty = store.string();
  let mapped = store.mapped(
    k,
    lit_a,
    string_ty,
    None,
    MappedModifier::Add,
    MappedModifier::Add,
  );
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(mapped, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "{ readonly a?: string }");
}

#[test]
fn mapped_key_remap_template() {
  let mut store = TypeStore::new();
  let k = store.type_param("K");
  let lit_a = store.literal_string("a");
  let lit_b = store.literal_string("b");
  let keys = store.union(vec![lit_a, lit_b]);
  let as_type = store.template(vec![
    TemplatePart::Type(k),
    TemplatePart::Literal("_x".into()),
  ]);
  let mapped = store.mapped(
    k,
    keys,
    k,
    Some(as_type),
    MappedModifier::Inherit,
    MappedModifier::Inherit,
  );
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(mapped, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "{ a_x: \"a\"; b_x: \"b\" }");
}

#[test]
fn mapped_remap_to_never_drops_properties() {
  let mut store = TypeStore::new();
  let k = store.type_param("K");
  let lit_a = store.literal_string("a");
  let lit_b = store.literal_string("b");
  let keys = store.union(vec![lit_a, lit_b]);
  let mapped = store.mapped(
    k,
    keys,
    store.number(),
    Some(store.never()),
    MappedModifier::Inherit,
    MappedModifier::Inherit,
  );
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(mapped, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "{  }");
}

#[test]
fn mapped_remove_modifiers() {
  let mut store = TypeStore::new();
  let k = store.type_param("K");
  let key = store.literal_string("p");
  let mapped = store.mapped(
    k,
    key,
    store.number(),
    None,
    MappedModifier::Remove,
    MappedModifier::Remove,
  );
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(mapped, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "{ p: number }");
}

#[test]
fn mapped_duplicate_keys_union_value() {
  let mut store = TypeStore::new();
  let k = store.type_param("K");
  let lit_x = store.literal_string("x");
  let lit_y = store.literal_string("y");
  let keys = store.union(vec![lit_x, lit_y]);
  let as_key = store.literal_string("z");
  let mapped = store.mapped(
    k,
    keys,
    k,
    Some(as_key),
    MappedModifier::Inherit,
    MappedModifier::Inherit,
  );
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(mapped, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "{ z: \"x\" | \"y\" }");
}

#[test]
fn keyof_union_intersection_behavior() {
  let mut store = TypeStore::new();
  let string_ty = store.string();
  let number_ty = store.number();
  let boolean_ty = store.boolean();
  let a = store.object(vec![
    ("a".into(), Property {
      ty: string_ty,
      optional: false,
      readonly: false,
    }),
    ("b".into(), Property {
      ty: number_ty,
      optional: false,
      readonly: false,
    }),
  ]);
  let b = store.object(vec![
    ("b".into(), Property {
      ty: string_ty,
      optional: false,
      readonly: false,
    }),
    ("c".into(), Property {
      ty: boolean_ty,
      optional: false,
      readonly: false,
    }),
  ]);
  let union = store.union(vec![a, b]);
  let keys = store.keyof(union);
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(keys, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "\"b\"");
}

#[test]
fn keyof_any_is_string_with_diag() {
  let mut store = TypeStore::new();
  let keys = store.keyof(store.any());
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(keys, &Env::new());
  let diags = norm.diagnostics().to_vec();
  drop(norm);
  assert_eq!(display(&store, result), "string");
  assert!(!diags.is_empty());
}

#[test]
fn keyof_never_is_never() {
  let mut store = TypeStore::new();
  let keys = store.keyof(store.never());
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(keys, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "never");
}

#[test]
fn keyof_intersection_merges_keys() {
  let mut store = TypeStore::new();
  let string_ty = store.string();
  let number_ty = store.number();
  let a = store.object(vec![("a".into(), Property {
    ty: string_ty,
    optional: false,
    readonly: false,
  })]);
  let b = store.object(vec![("b".into(), Property {
    ty: number_ty,
    optional: false,
    readonly: false,
  })]);
  let intersection = store.intersection(vec![a, b]);
  let keys = store.keyof(intersection);
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(keys, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "\"a\" | \"b\"");
}

#[test]
fn keyof_object_basic() {
  let mut store = TypeStore::new();
  let string_ty = store.string();
  let number_ty = store.number();
  let obj = store.object(vec![
    ("foo".into(), Property {
      ty: string_ty,
      optional: false,
      readonly: false,
    }),
    ("bar".into(), Property {
      ty: number_ty,
      optional: false,
      readonly: false,
    }),
  ]);
  let keys = store.keyof(obj);
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(keys, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "\"bar\" | \"foo\"");
}

#[test]
fn template_literal_nested_template_part() {
  let mut store = TypeStore::new();
  let inner = store.template(vec![TemplatePart::Literal("X".into())]);
  let outer = store.template(vec![
    TemplatePart::Literal("a".into()),
    TemplatePart::Type(inner),
  ]);
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(outer, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "\"aX\"");
}

#[test]
fn recursive_conditional_terminates() {
  let mut store = TypeStore::new();
  let t = store.type_param("T");
  let string_ty = store.string();
  let number_ty = store.number();
  let cond = store.conditional(t, string_ty, t, number_ty, Some(t));
  let mut env = Env::new();
  env.insert(t, cond);
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(t, &env);
  let diags = norm.diagnostics().to_vec();
  drop(norm);
  assert_eq!(display(&store, result), "number");
  assert!(!diags.is_empty());
}

#[test]
fn indexed_access_with_keyof_result() {
  let mut store = TypeStore::new();
  let string_ty = store.string();
  let number_ty = store.number();
  let obj = store.object(vec![
    ("a".into(), Property {
      ty: string_ty,
      optional: false,
      readonly: false,
    }),
    ("b".into(), Property {
      ty: number_ty,
      optional: false,
      readonly: false,
    }),
  ]);
  let keys = store.keyof(obj);
  let access = store.indexed_access(obj, keys);
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(access, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "number | string");
}

#[test]
fn indexed_access_non_object_diags() {
  let mut store = TypeStore::new();
  let number_ty = store.number();
  let key_a = store.literal_string("a");
  let access = store.indexed_access(number_ty, key_a);
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(access, &Env::new());
  let diags = norm.diagnostics().to_vec();
  drop(norm);
  assert_eq!(display(&store, result), "unknown");
  assert!(!diags.is_empty());
}

#[test]
fn mapped_value_uses_key_parameter() {
  let mut store = TypeStore::new();
  let k = store.type_param("K");
  let lit_foo = store.literal_string("foo");
  let lit_bar = store.literal_string("bar");
  let keys = store.union(vec![lit_foo, lit_bar]);
  let value_tpl = store.template(vec![
    TemplatePart::Type(k),
    TemplatePart::Literal("_value".into()),
  ]);
  let mapped = store.mapped(
    k,
    keys,
    value_tpl,
    None,
    MappedModifier::Inherit,
    MappedModifier::Inherit,
  );
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(mapped, &Env::new());
  drop(norm);
  assert_eq!(
    display(&store, result),
    "{ bar: \"bar_value\"; foo: \"foo_value\" }"
  );
}

#[test]
fn conditional_with_keyof_operand() {
  let mut store = TypeStore::new();
  let string_ty = store.string();
  let obj = store.object(vec![("a".into(), Property {
    ty: string_ty,
    optional: false,
    readonly: false,
  })]);
  let keys = store.keyof(obj);
  let lit_a = store.literal_string("a");
  let cond = store.conditional(keys, lit_a, store.true_type(), store.false_type(), None);
  let mut norm = Normalizer::new(&mut store);
  let result = norm.normalize(cond, &Env::new());
  drop(norm);
  assert_eq!(display(&store, result), "true");
}
