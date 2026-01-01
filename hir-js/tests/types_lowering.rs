use diagnostics::FileId;
use hir_js::hir::TypeImportName;
use hir_js::lower_file_with_diagnostics;
use hir_js::lower_from_source;
use hir_js::ClassMemberSigKind;
use hir_js::DefTypeInfo;
use hir_js::EnumMemberValue;
use hir_js::FileKind;
use hir_js::PropertyName;
use hir_js::TypeExprKind;
use hir_js::TypeMappedModifier;
use hir_js::TypeMemberKind;
use hir_js::TypeName;
use parse_js::ast::stmt::Stmt as AstStmt;
use parse_js::loc::Loc;
use parse_js::parse;

fn type_alias<'a>(
  result: &'a hir_js::LowerResult,
  name: &str,
) -> (
  hir_js::DefId,
  &'a hir_js::TypeArenas,
  hir_js::TypeExprId,
  &'a [hir_js::TypeParamId],
) {
  let def = result
    .defs
    .iter()
    .find(|def| result.names.resolve(def.name).unwrap() == name)
    .expect("type alias definition");
  let arenas = result
    .type_arenas(def.id)
    .expect("type arenas present for alias");
  match def.type_info.as_ref().expect("type info present") {
    DefTypeInfo::TypeAlias {
      type_expr,
      type_params,
    } => (def.id, arenas, *type_expr, type_params.as_slice()),
    other => panic!("expected type alias, found {other:?}"),
  }
}

fn type_query_import_name<'a>(result: &'a hir_js::LowerResult, name: &str) -> &'a TypeImportName {
  let (_, arenas, type_expr, _) = type_alias(result, name);
  let expr = &arenas.type_exprs[type_expr.0 as usize];
  match &expr.kind {
    TypeExprKind::TypeQuery(type_name) => match type_name {
      hir_js::TypeName::Import(import) => import,
      other => panic!("expected import type query, got {other:?}"),
    },
    other => panic!("expected type query, got {other:?}"),
  }
}

#[test]
fn lowers_function_type_alias() {
  let result = lower_from_source("type Fn = (x: string, y?: number, ...rest: boolean[]) => void;")
    .expect("lower");
  let (_, arenas, type_expr, type_params) = type_alias(&result, "Fn");
  assert!(type_params.is_empty());

  let expr = &arenas.type_exprs[type_expr.0 as usize];
  match &expr.kind {
    TypeExprKind::Function(func) => {
      assert_eq!(func.params.len(), 3);
      let first = &func.params[0];
      assert_eq!(result.names.resolve(first.name.unwrap()).unwrap(), "x");
      assert_eq!(first.optional, false);
      assert!(matches!(
        arenas.type_exprs[first.ty.0 as usize].kind,
        TypeExprKind::String
      ));

      let second = &func.params[1];
      assert!(second.optional);
      assert!(matches!(
        arenas.type_exprs[second.ty.0 as usize].kind,
        TypeExprKind::Number
      ));

      let third = &func.params[2];
      assert!(third.rest);
      let third_ty = &arenas.type_exprs[third.ty.0 as usize];
      match &third_ty.kind {
        TypeExprKind::Array(arr) => {
          assert!(matches!(
            arenas.type_exprs[arr.element.0 as usize].kind,
            TypeExprKind::Boolean
          ));
        }
        other => panic!("expected array type, got {other:?}"),
      }

      assert!(matches!(
        arenas.type_exprs[func.ret.0 as usize].kind,
        TypeExprKind::Void
      ));
    }
    other => panic!("expected function type, got {other:?}"),
  }
}

#[test]
fn lowers_conditional_and_infer_types() {
  let result = lower_from_source("type Cond<T> = T extends infer R ? R[] : never;").expect("lower");
  let (_, arenas, type_expr, type_params) = type_alias(&result, "Cond");
  assert_eq!(type_params.len(), 1);

  let expr = &arenas.type_exprs[type_expr.0 as usize];
  match &expr.kind {
    TypeExprKind::Conditional(cond) => {
      let extends = &arenas.type_exprs[cond.extends_type.0 as usize];
      assert!(matches!(extends.kind, TypeExprKind::Infer(_)));

      let true_type = &arenas.type_exprs[cond.true_type.0 as usize];
      match &true_type.kind {
        TypeExprKind::Array(arr) => {
          let element = &arenas.type_exprs[arr.element.0 as usize];
          match &element.kind {
            TypeExprKind::TypeRef(reference) => match &reference.name {
              hir_js::TypeName::Ident(id) => {
                assert_eq!(result.names.resolve(*id).unwrap(), "R");
              }
              other => panic!("unexpected type reference {other:?}"),
            },
            other => panic!("expected ref to infer type, got {other:?}"),
          }
        }
        other => panic!("expected array of infer, got {other:?}"),
      }

      let false_type = &arenas.type_exprs[cond.false_type.0 as usize];
      assert!(matches!(false_type.kind, TypeExprKind::Never));
    }
    other => panic!("expected conditional type, got {other:?}"),
  }
}

#[test]
fn lowers_mapped_types_with_remapping() {
  let result = lower_from_source(
    "type Mapped<T> = { readonly [K in keyof T as `${K & string}Changed`]?: T[K] };",
  )
  .expect("lower");
  let (_, arenas, type_expr, type_params) = type_alias(&result, "Mapped");
  assert_eq!(type_params.len(), 1);

  let expr = &arenas.type_exprs[type_expr.0 as usize];
  match &expr.kind {
    TypeExprKind::Mapped(mapped) => {
      assert_eq!(mapped.readonly, Some(TypeMappedModifier::None));
      assert_eq!(mapped.optional, Some(TypeMappedModifier::None));
      assert!(mapped.name_type.is_some());
      let value_type = &arenas.type_exprs[mapped.value_type.0 as usize];
      assert!(matches!(
        value_type.kind,
        TypeExprKind::IndexedAccess { .. }
      ));
    }
    other => panic!("expected mapped type, got {other:?}"),
  }
}

#[test]
fn lowers_template_literal_and_indexed_access_types() {
  let source = r#"
    type Index = { foo: { bar: number } }["foo"]["bar"];
    type Tmpl<T> = `start${T & string}end`;
  "#;
  let result = lower_from_source(source).expect("lower");

  let (_index_def, index_arenas, index_expr, _) = type_alias(&result, "Index");
  let index = &index_arenas.type_exprs[index_expr.0 as usize];
  match &index.kind {
    TypeExprKind::IndexedAccess {
      object_type,
      index_type,
    } => {
      let last_index = &index_arenas.type_exprs[index_type.0 as usize];
      assert!(matches!(
        last_index.kind,
        TypeExprKind::Literal(hir_js::TypeLiteral::String(_))
      ));
      let first_index = &index_arenas.type_exprs[object_type.0 as usize];
      match &first_index.kind {
        TypeExprKind::IndexedAccess {
          object_type: first_object,
          index_type: first_key,
        } => {
          let first_key_expr = &index_arenas.type_exprs[first_key.0 as usize];
          assert!(matches!(
            first_key_expr.kind,
            TypeExprKind::Literal(hir_js::TypeLiteral::String(_))
          ));
          let object_expr = &index_arenas.type_exprs[first_object.0 as usize];
          assert!(matches!(object_expr.kind, TypeExprKind::TypeLiteral(_)));
        }
        other => panic!("expected nested indexed access, got {other:?}"),
      }
    }
    other => panic!("expected indexed access, got {other:?}"),
  }

  let (tmpl_def, tmpl_arenas, tmpl_expr, _) = type_alias(&result, "Tmpl");
  let tmpl = &tmpl_arenas.type_exprs[tmpl_expr.0 as usize];
  match &tmpl.kind {
    TypeExprKind::TemplateLiteral(tmpl) => {
      assert!(tmpl.head.contains("start"));
      assert_eq!(tmpl.spans.len(), 1);
      assert!(tmpl.spans[0].literal.contains("end"));
    }
    other => panic!("expected template literal, got {other:?}"),
  }

  let span = tmpl.span;
  let mapped = result
    .hir
    .span_map
    .type_expr_at_offset(span.start)
    .expect("span lookup");
  assert_eq!(mapped, (tmpl_def, tmpl_expr));
}

#[test]
fn type_ids_do_not_shift_across_unrelated_type_decl_insertions() {
  let base = lower_from_source("type A = { a: string }; type B = { b: number };").expect("base");
  let variant =
    lower_from_source("type A = { a: string }; type Inserted = boolean; type B = { b: number };")
      .expect("variant");

  let (base_def, base_arenas, base_expr, _) = type_alias(&base, "B");
  let (variant_def, variant_arenas, variant_expr, _) = type_alias(&variant, "B");

  let base_info = base
    .defs
    .iter()
    .find(|def| def.id == base_def)
    .and_then(|def| def.type_info.clone())
    .expect("base type info");
  let variant_info = variant
    .defs
    .iter()
    .find(|def| def.id == variant_def)
    .and_then(|def| def.type_info.clone())
    .expect("variant type info");

  assert_eq!(base_info, variant_info);

  let base_literal = match &base_arenas.type_exprs[base_expr.0 as usize].kind {
    TypeExprKind::TypeLiteral(lit) => lit,
    other => panic!("expected type literal, got {other:?}"),
  };
  let variant_literal = match &variant_arenas.type_exprs[variant_expr.0 as usize].kind {
    TypeExprKind::TypeLiteral(lit) => lit,
    other => panic!("expected type literal, got {other:?}"),
  };

  assert_eq!(base_literal.members, variant_literal.members);

  let base_member = &base_arenas.type_members[base_literal.members[0].0 as usize];
  let variant_member = &variant_arenas.type_members[variant_literal.members[0].0 as usize];
  match (&base_member.kind, &variant_member.kind) {
    (TypeMemberKind::Property(base_prop), TypeMemberKind::Property(variant_prop)) => {
      assert_eq!(base_prop.type_annotation, variant_prop.type_annotation);
      if let (Some(base_ty), Some(variant_ty)) =
        (base_prop.type_annotation, variant_prop.type_annotation)
      {
        assert_eq!(
          base_arenas.type_exprs[base_ty.0 as usize].kind,
          variant_arenas.type_exprs[variant_ty.0 as usize].kind
        );
      }
    }
    other => panic!("expected property members, got {other:?}"),
  }
}

#[test]
fn span_map_can_locate_type_member() {
  let result = lower_from_source("interface Foo { a: string; b(): number; }").expect("lower");
  let def = result
    .defs
    .iter()
    .find(|def| result.names.resolve(def.name).unwrap() == "Foo")
    .expect("interface definition");
  let arenas = result.type_arenas(def.id).expect("type arenas present");
  let members = match def.type_info.as_ref().expect("type info present") {
    DefTypeInfo::Interface { members, .. } => members,
    other => panic!("expected interface, found {other:?}"),
  };
  let member_id = members
    .iter()
    .copied()
    .find(|id| match &arenas.type_members[id.0 as usize].kind {
      TypeMemberKind::Property(prop) => match prop.name {
        PropertyName::Ident(id) => result.names.resolve(id).unwrap() == "a",
        _ => false,
      },
      _ => false,
    })
    .expect("property member");

  let span = arenas.type_members[member_id.0 as usize].span;
  let found = result
    .hir
    .span_map
    .type_member_at_offset(span.start)
    .expect("member at offset");
  assert_eq!(found, (def.id, member_id));
}

#[test]
fn span_map_can_locate_type_param() {
  let result = lower_from_source("type T<A extends string> = A;").expect("lower");
  let (def_id, arenas, _, type_params) = type_alias(&result, "T");
  assert_eq!(type_params.len(), 1);
  let type_param_id = type_params[0];

  let span = arenas.type_params[type_param_id.0 as usize].span;
  let found = result
    .hir
    .span_map
    .type_param_at_offset(span.start)
    .expect("type param at offset");
  assert_eq!(found, (def_id, type_param_id));
}

#[test]
fn span_map_type_ids_are_scoped_to_def() {
  let result =
    lower_from_source("interface A<T> { a: T }\ninterface B<U> { b: U }").expect("lower");

  let def_a = result
    .defs
    .iter()
    .find(|def| result.names.resolve(def.name).unwrap() == "A")
    .expect("interface A");
  let def_b = result
    .defs
    .iter()
    .find(|def| result.names.resolve(def.name).unwrap() == "B")
    .expect("interface B");

  let arenas_a = result.type_arenas(def_a.id).expect("type arenas for A");
  let arenas_b = result.type_arenas(def_b.id).expect("type arenas for B");

  let (members_a, type_params_a) = match def_a.type_info.as_ref().expect("type info for A") {
    DefTypeInfo::Interface {
      members,
      type_params,
      ..
    } => (members.as_slice(), type_params.as_slice()),
    other => panic!("expected interface for A, found {other:?}"),
  };
  let (members_b, type_params_b) = match def_b.type_info.as_ref().expect("type info for B") {
    DefTypeInfo::Interface {
      members,
      type_params,
      ..
    } => (members.as_slice(), type_params.as_slice()),
    other => panic!("expected interface for B, found {other:?}"),
  };

  assert_eq!(members_a.len(), 1);
  assert_eq!(members_b.len(), 1);
  assert_eq!(type_params_a.len(), 1);
  assert_eq!(type_params_b.len(), 1);

  let member0 = hir_js::TypeMemberId(0);
  assert_eq!(members_a[0], member0);
  assert_eq!(members_b[0], member0);

  let type_param0 = hir_js::TypeParamId(0);
  assert_eq!(type_params_a[0], type_param0);
  assert_eq!(type_params_b[0], type_param0);

  let member_a_span = arenas_a.type_members[member0.0 as usize].span;
  let member_b_span = arenas_b.type_members[member0.0 as usize].span;
  assert_ne!(member_a_span, member_b_span);

  assert_eq!(
    result.hir.span_map.type_member_span(def_a.id, member0),
    Some(member_a_span),
  );
  assert_eq!(
    result.hir.span_map.type_member_span(def_b.id, member0),
    Some(member_b_span),
  );

  assert_eq!(
    result
      .hir
      .span_map
      .type_member_at_offset(member_a_span.start),
    Some((def_a.id, member0)),
  );
  assert_eq!(
    result
      .hir
      .span_map
      .type_member_at_offset(member_b_span.start),
    Some((def_b.id, member0)),
  );

  let type_param_a_span = arenas_a.type_params[type_param0.0 as usize].span;
  let type_param_b_span = arenas_b.type_params[type_param0.0 as usize].span;
  assert_ne!(type_param_a_span, type_param_b_span);

  assert_eq!(
    result.hir.span_map.type_param_span(def_a.id, type_param0),
    Some(type_param_a_span),
  );
  assert_eq!(
    result.hir.span_map.type_param_span(def_b.id, type_param0),
    Some(type_param_b_span),
  );

  assert_eq!(
    result
      .hir
      .span_map
      .type_param_at_offset(type_param_a_span.start),
    Some((def_a.id, type_param0)),
  );
  assert_eq!(
    result
      .hir
      .span_map
      .type_param_at_offset(type_param_b_span.start),
    Some((def_b.id, type_param0)),
  );
}

#[test]
fn lowers_mapped_types_without_modifiers() {
  let result = lower_from_source("type M<T> = { [K in keyof T]: T[K] };").expect("lower");
  let (_, arenas, type_expr, type_params) = type_alias(&result, "M");
  assert_eq!(type_params.len(), 1);

  let expr = &arenas.type_exprs[type_expr.0 as usize];
  match &expr.kind {
    TypeExprKind::Mapped(mapped) => {
      assert_eq!(mapped.readonly, None);
      assert_eq!(mapped.optional, None);
      assert!(mapped.name_type.is_none());
    }
    other => panic!("expected mapped type, got {other:?}"),
  }
}

#[test]
fn lowers_type_query_import_name() {
  let result = lower_from_source(r#"type T = typeof import("mod").Foo;"#).expect("lower");
  let import = type_query_import_name(&result, "T");
  assert_eq!(import.module.as_deref(), Some("mod"));
  let qualifier = import.qualifier.as_ref().expect("qualifier");
  assert_eq!(qualifier.len(), 1);
  assert_eq!(result.names.resolve(qualifier[0]).unwrap(), "Foo");
}

#[test]
fn lowers_type_query_import_name_no_qualifier() {
  let result = lower_from_source(r#"type T = typeof import("mod");"#).expect("lower");
  let import = type_query_import_name(&result, "T");
  assert_eq!(import.module.as_deref(), Some("mod"));
  assert!(import.qualifier.is_none());
}

#[test]
fn lowers_type_query_import_name_multi_segment() {
  let result = lower_from_source(r#"type T = typeof import("mod").Foo.Bar;"#).expect("lower");
  let import = type_query_import_name(&result, "T");
  assert_eq!(import.module.as_deref(), Some("mod"));
  let qualifier = import.qualifier.as_ref().expect("qualifier");
  assert_eq!(qualifier.len(), 2);
  assert_eq!(result.names.resolve(qualifier[0]).unwrap(), "Foo");
  assert_eq!(result.names.resolve(qualifier[1]).unwrap(), "Bar");
}

#[test]
fn reports_overflowing_type_spans() {
  let mut ast = parse("type Overflow = string;").expect("parse");
  let huge_start = u32::MAX as usize + 10;
  let huge_end = huge_start + 5;

  let stmt = ast.stx.body.first_mut().expect("type alias stmt");
  match &mut *stmt.stx {
    AstStmt::TypeAliasDecl(alias) => {
      alias.stx.type_expr.loc = Loc(huge_start, huge_end);
    }
    other => panic!("expected type alias, got {other:?}"),
  }

  let (result, diagnostics) = lower_file_with_diagnostics(FileId(0), FileKind::Ts, &ast);
  assert!(
    diagnostics.iter().any(|d| d.code == "LOWER0001"),
    "expected overflow diagnostic for type span",
  );

  let (_, arenas, type_expr, _) = type_alias(&result, "Overflow");
  let span = arenas.type_exprs[type_expr.0 as usize].span;
  assert_eq!(span.start, u32::MAX);
  assert_eq!(span.end, u32::MAX);
}

#[test]
fn union_canonicalization_is_span_stable() {
  let base = lower_from_source("type A = (Foo | Bar);").expect("lower");
  let with_padding =
    lower_from_source("type Z = string;\ntype A = (Foo | Bar);").expect("lower with padding");

  let base_members = union_member_names(&base, "A");
  let with_padding_members = union_member_names(&with_padding, "A");

  assert_eq!(base_members, vec!["Bar", "Foo"]);
  assert_eq!(base_members, with_padding_members);
}

#[test]
fn union_canonicalization_is_span_stable_for_function_types() {
  let base =
    lower_from_source("type A = ((x: string) => void) | ((y: number) => void);").expect("lower");
  let with_padding =
    lower_from_source("type Z = string;\ntype A = ((x: string) => void) | ((y: number) => void);")
      .expect("lower with padding");

  let base_members = union_member_first_param_type_names(&base, "A");
  let with_padding_members = union_member_first_param_type_names(&with_padding, "A");

  assert_eq!(base_members, vec!["number", "string"]);
  assert_eq!(base_members, with_padding_members);
}

#[test]
fn union_dedups_simple_duplicates() {
  let result = lower_from_source("type A = string | string | Foo | Foo;").expect("lower");
  let members = union_member_names(&result, "A");
  assert_eq!(members, vec!["string", "Foo"]);
}

#[test]
fn union_strips_parenthesized_members() {
  let result = lower_from_source("type A = (Foo) | Bar;").expect("lower");
  let members = union_member_names(&result, "A");
  assert_eq!(members, vec!["Bar", "Foo"]);
}

#[test]
fn union_flattens_parenthesized_nested_unions() {
  let result = lower_from_source("type A = Foo | (Bar | Baz);").expect("lower");
  let members = union_member_names(&result, "A");
  assert_eq!(members, vec!["Bar", "Baz", "Foo"]);
}

#[test]
fn union_dedups_duplicate_function_types() {
  let result =
    lower_from_source("type A = ((x: string) => void) | ((x: string) => void);").expect("lower");
  let (_, arenas, expr_id, _) = type_alias(&result, "A");
  let mut ty = &arenas.type_exprs[expr_id.0 as usize].kind;
  while let TypeExprKind::Parenthesized(inner) = ty {
    ty = &arenas.type_exprs[inner.0 as usize].kind;
  }

  let members = match ty {
    TypeExprKind::Union(members) => members.as_slice(),
    other => panic!("expected union, got {other:?}"),
  };

  assert_eq!(members.len(), 1);
}

#[test]
fn union_dedups_duplicate_function_types_ignoring_param_names() {
  let result =
    lower_from_source("type A = ((x: string) => void) | ((y: string) => void);").expect("lower");
  let (_, arenas, expr_id, _) = type_alias(&result, "A");
  let mut ty = &arenas.type_exprs[expr_id.0 as usize].kind;
  while let TypeExprKind::Parenthesized(inner) = ty {
    ty = &arenas.type_exprs[inner.0 as usize].kind;
  }

  let members = match ty {
    TypeExprKind::Union(members) => members.as_slice(),
    other => panic!("expected union, got {other:?}"),
  };

  assert_eq!(members.len(), 1);
}

#[test]
fn union_dedups_type_predicate_function_types_ignoring_param_names() {
  let result =
    lower_from_source("type A = ((x: unknown) => x is string) | ((y: unknown) => y is string);")
      .expect("lower");
  let (_, arenas, expr_id, _) = type_alias(&result, "A");
  let mut ty = &arenas.type_exprs[expr_id.0 as usize].kind;
  while let TypeExprKind::Parenthesized(inner) = ty {
    ty = &arenas.type_exprs[inner.0 as usize].kind;
  }

  let members = match ty {
    TypeExprKind::Union(members) => members.as_slice(),
    other => panic!("expected union, got {other:?}"),
  };

  assert_eq!(members.len(), 1);
}

#[test]
fn union_does_not_dedup_generic_function_types_with_different_bindings() {
  let result =
    lower_from_source("type T = string;\ntype A = (<T>(x: T) => void) | (<U>(x: T) => void);")
      .expect("lower");
  let (_, arenas, expr_id, _) = type_alias(&result, "A");
  let mut ty = &arenas.type_exprs[expr_id.0 as usize].kind;
  while let TypeExprKind::Parenthesized(inner) = ty {
    ty = &arenas.type_exprs[inner.0 as usize].kind;
  }

  let members = match ty {
    TypeExprKind::Union(members) => members.as_slice(),
    other => panic!("expected union, got {other:?}"),
  };

  assert_eq!(members.len(), 2);
}

#[test]
fn union_dedups_tuple_types_ignoring_labels() {
  let result = lower_from_source("type A = ([x: string] | [y: string]);").expect("lower");
  let (_, arenas, expr_id, _) = type_alias(&result, "A");
  let mut ty = &arenas.type_exprs[expr_id.0 as usize].kind;
  while let TypeExprKind::Parenthesized(inner) = ty {
    ty = &arenas.type_exprs[inner.0 as usize].kind;
  }

  let members = match ty {
    TypeExprKind::Union(members) => members.as_slice(),
    other => panic!("expected union, got {other:?}"),
  };

  assert_eq!(members.len(), 1);

  let tuple = match &arenas.type_exprs[members[0].0 as usize].kind {
    TypeExprKind::Tuple(tuple) => tuple,
    other => panic!("expected tuple member, got {other:?}"),
  };
  assert_eq!(tuple.elements.len(), 1);
  assert!(matches!(
    arenas.type_exprs[tuple.elements[0].ty.0 as usize].kind,
    TypeExprKind::String
  ));
}

#[test]
fn union_does_not_dedup_distinct_computed_string_property_names() {
  let result =
    lower_from_source(r#"type A = { ["foo"]: string } | { ["bar"]: string };"#).expect("lower");
  let members = union_member_first_property_names(&result, "A");
  assert_eq!(members, vec!["bar", "foo"]);
}

#[test]
fn union_does_not_dedup_distinct_computed_template_property_names() {
  let result =
    lower_from_source(r#"type A = { [`foo`]: string } | { [`bar`]: string };"#).expect("lower");
  let members = union_member_first_property_names(&result, "A");
  assert_eq!(members, vec!["bar", "foo"]);
}

#[test]
fn union_canonicalization_is_span_stable_for_type_literals() {
  let base = lower_from_source("type A = ({ a: string } | { b: number });").expect("lower");
  let with_padding =
    lower_from_source("type Z = boolean;\ntype A = ({ a: string } | { b: number });")
      .expect("lower with padding");

  let base_members = union_member_first_property_names(&base, "A");
  let with_padding_members = union_member_first_property_names(&with_padding, "A");

  assert_eq!(base_members, vec!["a", "b"]);
  assert_eq!(base_members, with_padding_members);
}

#[test]
fn union_dedups_duplicate_type_literals() {
  let result = lower_from_source("type A = { a: string } | { a: string };").expect("lower");
  let members = union_member_first_property_names(&result, "A");
  assert_eq!(members, vec!["a"]);
}

#[test]
fn intersection_canonicalization_is_span_stable_for_function_types() {
  let base =
    lower_from_source("type A = ((x: string) => void) & ((y: number) => void);").expect("lower");
  let with_padding =
    lower_from_source("type Z = string;\ntype A = ((x: string) => void) & ((y: number) => void);")
      .expect("lower with padding");

  let base_members = intersection_member_first_param_type_names(&base, "A");
  let with_padding_members = intersection_member_first_param_type_names(&with_padding, "A");

  assert_eq!(base_members, vec!["number", "string"]);
  assert_eq!(base_members, with_padding_members);
}

#[test]
fn intersection_dedups_duplicate_function_types() {
  let result =
    lower_from_source("type A = ((x: string) => void) & ((y: string) => void);").expect("lower");
  let (_, arenas, expr_id, _) = type_alias(&result, "A");
  let mut ty = &arenas.type_exprs[expr_id.0 as usize].kind;
  while let TypeExprKind::Parenthesized(inner) = ty {
    ty = &arenas.type_exprs[inner.0 as usize].kind;
  }

  let members = match ty {
    TypeExprKind::Intersection(members) => members.as_slice(),
    other => panic!("expected intersection, got {other:?}"),
  };

  assert_eq!(members.len(), 1);
}

#[test]
fn intersection_strips_parenthesized_members() {
  let result = lower_from_source("type A = (Foo) & Bar;").expect("lower");
  let members = intersection_member_names(&result, "A");
  assert_eq!(members, vec!["Bar", "Foo"]);
}

#[test]
fn intersection_flattens_parenthesized_nested_intersections() {
  let result = lower_from_source("type A = Foo & (Bar & Baz);").expect("lower");
  let members = intersection_member_names(&result, "A");
  assert_eq!(members, vec!["Bar", "Baz", "Foo"]);
}

#[test]
fn intersection_canonicalization_is_span_stable_for_type_literals() {
  let base = lower_from_source("type A = ({ a: string } & { b: number });").expect("lower");
  let with_padding =
    lower_from_source("type Z = boolean;\ntype A = ({ a: string } & { b: number });")
      .expect("lower with padding");

  let base_members = intersection_member_first_property_names(&base, "A");
  let with_padding_members = intersection_member_first_property_names(&with_padding, "A");

  assert_eq!(base_members, vec!["a", "b"]);
  assert_eq!(base_members, with_padding_members);
}

#[test]
fn intersection_dedups_duplicate_type_literals() {
  let result = lower_from_source("type A = { a: string } & { a: string };").expect("lower");
  let members = intersection_member_first_property_names(&result, "A");
  assert_eq!(members, vec!["a"]);
}

fn union_member_names(result: &hir_js::LowerResult, alias: &str) -> Vec<String> {
  let (_, arenas, expr_id, _) = type_alias(result, alias);
  let mut ty = &arenas.type_exprs[expr_id.0 as usize].kind;
  while let TypeExprKind::Parenthesized(inner) = ty {
    ty = &arenas.type_exprs[inner.0 as usize].kind;
  }

  let members = match ty {
    TypeExprKind::Union(members) => members.as_slice(),
    other => panic!("expected union, got {other:?}"),
  };

  members
    .iter()
    .map(|id| type_name(&result.names, &arenas.type_exprs[id.0 as usize].kind))
    .collect()
}

fn intersection_member_names(result: &hir_js::LowerResult, alias: &str) -> Vec<String> {
  let (_, arenas, expr_id, _) = type_alias(result, alias);
  let mut ty = &arenas.type_exprs[expr_id.0 as usize].kind;
  while let TypeExprKind::Parenthesized(inner) = ty {
    ty = &arenas.type_exprs[inner.0 as usize].kind;
  }

  let members = match ty {
    TypeExprKind::Intersection(members) => members.as_slice(),
    other => panic!("expected intersection, got {other:?}"),
  };

  members
    .iter()
    .map(|id| type_name(&result.names, &arenas.type_exprs[id.0 as usize].kind))
    .collect()
}

fn intersection_member_first_property_names(
  result: &hir_js::LowerResult,
  alias: &str,
) -> Vec<String> {
  let (_, arenas, expr_id, _) = type_alias(result, alias);
  let mut ty = &arenas.type_exprs[expr_id.0 as usize].kind;
  while let TypeExprKind::Parenthesized(inner) = ty {
    ty = &arenas.type_exprs[inner.0 as usize].kind;
  }

  let members = match ty {
    TypeExprKind::Intersection(members) => members.as_slice(),
    other => panic!("expected intersection, got {other:?}"),
  };

  members
    .iter()
    .map(|member_id| {
      let mut member_kind = &arenas.type_exprs[member_id.0 as usize].kind;
      while let TypeExprKind::Parenthesized(inner) = member_kind {
        member_kind = &arenas.type_exprs[inner.0 as usize].kind;
      }

      let lit = match member_kind {
        TypeExprKind::TypeLiteral(lit) => lit,
        other => panic!("expected type literal member, got {other:?}"),
      };

      let first_member_id = lit.members.first().expect("type literal member");
      match &arenas.type_members[first_member_id.0 as usize].kind {
        TypeMemberKind::Property(prop) => match &prop.name {
          PropertyName::Ident(id) => result.names.resolve(*id).unwrap().to_string(),
          PropertyName::String(s) => s.clone(),
          PropertyName::Number(n) => n.clone(),
          PropertyName::Computed => "[computed]".to_string(),
        },
        other => panic!("expected property member, got {other:?}"),
      }
    })
    .collect()
}

fn union_member_first_property_names(result: &hir_js::LowerResult, alias: &str) -> Vec<String> {
  let (_, arenas, expr_id, _) = type_alias(result, alias);
  let mut ty = &arenas.type_exprs[expr_id.0 as usize].kind;
  while let TypeExprKind::Parenthesized(inner) = ty {
    ty = &arenas.type_exprs[inner.0 as usize].kind;
  }

  let members = match ty {
    TypeExprKind::Union(members) => members.as_slice(),
    other => panic!("expected union, got {other:?}"),
  };

  members
    .iter()
    .map(|member_id| {
      let mut member_kind = &arenas.type_exprs[member_id.0 as usize].kind;
      while let TypeExprKind::Parenthesized(inner) = member_kind {
        member_kind = &arenas.type_exprs[inner.0 as usize].kind;
      }

      let lit = match member_kind {
        TypeExprKind::TypeLiteral(lit) => lit,
        other => panic!("expected type literal member, got {other:?}"),
      };

      let first_member_id = lit.members.first().expect("type literal member");
      match &arenas.type_members[first_member_id.0 as usize].kind {
        TypeMemberKind::Property(prop) => match &prop.name {
          PropertyName::Ident(id) => result.names.resolve(*id).unwrap().to_string(),
          PropertyName::String(s) => s.clone(),
          PropertyName::Number(n) => n.clone(),
          PropertyName::Computed => "[computed]".to_string(),
        },
        other => panic!("expected property member, got {other:?}"),
      }
    })
    .collect()
}

fn intersection_member_first_param_type_names(
  result: &hir_js::LowerResult,
  alias: &str,
) -> Vec<&'static str> {
  let (_, arenas, expr_id, _) = type_alias(result, alias);
  let mut ty = &arenas.type_exprs[expr_id.0 as usize].kind;
  while let TypeExprKind::Parenthesized(inner) = ty {
    ty = &arenas.type_exprs[inner.0 as usize].kind;
  }

  let members = match ty {
    TypeExprKind::Intersection(members) => members.as_slice(),
    other => panic!("expected intersection, got {other:?}"),
  };

  members
    .iter()
    .map(|member_id| {
      let mut member_kind = &arenas.type_exprs[member_id.0 as usize].kind;
      while let TypeExprKind::Parenthesized(inner) = member_kind {
        member_kind = &arenas.type_exprs[inner.0 as usize].kind;
      }

      let func = match member_kind {
        TypeExprKind::Function(func) => func,
        other => panic!("expected function member, got {other:?}"),
      };

      let first = func.params.first().expect("function param");
      let param_ty = &arenas.type_exprs[first.ty.0 as usize].kind;
      match param_ty {
        TypeExprKind::String => "string",
        TypeExprKind::Number => "number",
        other => panic!("expected primitive param type, got {other:?}"),
      }
    })
    .collect()
}

fn union_member_first_param_type_names(
  result: &hir_js::LowerResult,
  alias: &str,
) -> Vec<&'static str> {
  let (_, arenas, expr_id, _) = type_alias(result, alias);
  let mut ty = &arenas.type_exprs[expr_id.0 as usize].kind;
  while let TypeExprKind::Parenthesized(inner) = ty {
    ty = &arenas.type_exprs[inner.0 as usize].kind;
  }

  let members = match ty {
    TypeExprKind::Union(members) => members.as_slice(),
    other => panic!("expected union, got {other:?}"),
  };

  members
    .iter()
    .map(|member_id| {
      let mut member_kind = &arenas.type_exprs[member_id.0 as usize].kind;
      while let TypeExprKind::Parenthesized(inner) = member_kind {
        member_kind = &arenas.type_exprs[inner.0 as usize].kind;
      }

      let func = match member_kind {
        TypeExprKind::Function(func) => func,
        other => panic!("expected function member, got {other:?}"),
      };

      let first = func.params.first().expect("function param");
      let param_ty = &arenas.type_exprs[first.ty.0 as usize].kind;
      match param_ty {
        TypeExprKind::String => "string",
        TypeExprKind::Number => "number",
        other => panic!("expected primitive param type, got {other:?}"),
      }
    })
    .collect()
}

fn type_name(names: &hir_js::NameInterner, ty: &TypeExprKind) -> String {
  match ty {
    TypeExprKind::String => "string".to_string(),
    TypeExprKind::TypeRef(r) => match &r.name {
      hir_js::TypeName::Ident(id) => names.resolve(*id).unwrap().to_string(),
      hir_js::TypeName::Qualified(path) => path
        .iter()
        .map(|id| names.resolve(*id).unwrap())
        .collect::<Vec<_>>()
        .join("."),
      hir_js::TypeName::Import(_) => "[import]".to_string(),
      hir_js::TypeName::ImportExpr => "[import expr]".to_string(),
    },
    other => format!("{other:?}"),
  }
}
#[test]
fn lowers_class_type_info_basic() {
  let result = lower_from_source(
    "class C<T> extends Base implements IFace { x: string; m(a: number): boolean { return true } }",
  )
  .expect("lower");
  let def = result
    .defs
    .iter()
    .find(|def| result.names.resolve(def.name).unwrap() == "C")
    .expect("class definition");
  let info = def.type_info.as_ref().expect("type info present");
  let arenas = result
    .type_arenas(def.id)
    .expect("type arenas present for class");
  let (type_params, extends, implements, members) = match info {
    DefTypeInfo::Class {
      type_params,
      extends,
      implements,
      members,
    } => (type_params, extends, implements, members),
    other => panic!("expected class type info, got {other:?}"),
  };
  assert_eq!(type_params.len(), 1);

  let base = extends.expect("extends clause");
  let base_expr = &arenas.type_exprs[base.0 as usize];
  match &base_expr.kind {
    TypeExprKind::TypeRef(reference) => match &reference.name {
      TypeName::Ident(id) => assert_eq!(result.names.resolve(*id).unwrap(), "Base"),
      other => panic!("unexpected base name {other:?}"),
    },
    other => panic!("unexpected extends kind {other:?}"),
  }

  assert_eq!(implements.len(), 1);
  let iface_expr = &arenas.type_exprs[implements[0].0 as usize];
  match &iface_expr.kind {
    TypeExprKind::TypeRef(reference) => match &reference.name {
      TypeName::Ident(id) => assert_eq!(result.names.resolve(*id).unwrap(), "IFace"),
      other => panic!("unexpected implements name {other:?}"),
    },
    other => panic!("unexpected implements kind {other:?}"),
  }

  let field = members
    .iter()
    .find(|member| match &member.kind {
      ClassMemberSigKind::Field { name, .. } => matches!(
        name,
        PropertyName::Ident(id) if result.names.resolve(*id).unwrap() == "x"
      ),
      _ => false,
    })
    .expect("field member");
  match &field.kind {
    ClassMemberSigKind::Field {
      type_annotation, ..
    } => {
      let ty = type_annotation.expect("field type");
      assert!(matches!(
        arenas.type_exprs[ty.0 as usize].kind,
        TypeExprKind::String
      ));
    }
    other => panic!("unexpected field kind {other:?}"),
  }

  let method = members
    .iter()
    .find(|member| match &member.kind {
      ClassMemberSigKind::Method { name, .. } => matches!(
        name,
        PropertyName::Ident(id) if result.names.resolve(*id).unwrap() == "m"
      ),
      _ => false,
    })
    .expect("method member");
  match &method.kind {
    ClassMemberSigKind::Method { signature, .. } => {
      assert_eq!(signature.params.len(), 1);
      let param = &signature.params[0];
      let param_name = param.name.expect("param name");
      assert_eq!(result.names.resolve(param_name).unwrap(), "a");
      assert!(matches!(
        arenas.type_exprs[param.ty.0 as usize].kind,
        TypeExprKind::Number
      ));
      let ret = signature.return_type.expect("return type");
      assert!(matches!(
        arenas.type_exprs[ret.0 as usize].kind,
        TypeExprKind::Boolean
      ));
    }
    other => panic!("unexpected method kind {other:?}"),
  }
}

#[test]
fn lowers_enum_type_info() {
  let result = lower_from_source(r#"enum E { A, B = 2, C = "c" }"#).expect("lower");
  let def = result
    .defs
    .iter()
    .find(|def| result.names.resolve(def.name).unwrap() == "E")
    .expect("enum definition");
  let info = def.type_info.as_ref().expect("type info present");
  let members = match info {
    DefTypeInfo::Enum { members } => members,
    other => panic!("expected enum type info, got {other:?}"),
  };
  assert_eq!(members.len(), 3);
  assert_eq!(result.names.resolve(members[0].name).unwrap(), "A");
  assert_eq!(members[0].value, EnumMemberValue::Number);
  assert_eq!(result.names.resolve(members[1].name).unwrap(), "B");
  assert_eq!(members[1].value, EnumMemberValue::Number);
  assert_eq!(result.names.resolve(members[2].name).unwrap(), "C");
  assert_eq!(members[2].value, EnumMemberValue::String);
}
