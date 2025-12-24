use hir_js::lower_from_source;
use hir_js::DefTypeInfo;
use hir_js::TypeExprKind;
use hir_js::TypeMappedModifier;

fn type_alias<'a>(
  result: &'a hir_js::LowerResult,
  name: &str,
) -> (hir_js::TypeExprId, &'a [hir_js::TypeParamId]) {
  let def = result
    .defs
    .iter()
    .find(|def| result.names.resolve(def.path.name).unwrap() == name)
    .expect("type alias definition");
  match def.type_info.as_ref().expect("type info present") {
    DefTypeInfo::TypeAlias {
      type_expr,
      type_params,
    } => (*type_expr, type_params.as_slice()),
    other => panic!("expected type alias, found {other:?}"),
  }
}

#[test]
fn lowers_function_type_alias() {
  let result = lower_from_source("type Fn = (x: string, y?: number, ...rest: boolean[]) => void;")
    .expect("lower");
  let (type_expr, type_params) = type_alias(&result, "Fn");
  assert!(type_params.is_empty());

  let expr = &result.types.type_exprs[type_expr.0 as usize];
  match &expr.kind {
    TypeExprKind::Function(func) => {
      assert_eq!(func.params.len(), 3);
      let first = &func.params[0];
      assert_eq!(result.names.resolve(first.name.unwrap()).unwrap(), "x");
      assert_eq!(first.optional, false);
      assert!(matches!(
        result.types.type_exprs[first.ty.0 as usize].kind,
        TypeExprKind::String
      ));

      let second = &func.params[1];
      assert!(second.optional);
      assert!(matches!(
        result.types.type_exprs[second.ty.0 as usize].kind,
        TypeExprKind::Number
      ));

      let third = &func.params[2];
      assert!(third.rest);
      let third_ty = &result.types.type_exprs[third.ty.0 as usize];
      match &third_ty.kind {
        TypeExprKind::Array(arr) => {
          assert!(matches!(
            result.types.type_exprs[arr.element.0 as usize].kind,
            TypeExprKind::Boolean
          ));
        }
        other => panic!("expected array type, got {other:?}"),
      }

      assert!(matches!(
        result.types.type_exprs[func.ret.0 as usize].kind,
        TypeExprKind::Void
      ));
    }
    other => panic!("expected function type, got {other:?}"),
  }
}

#[test]
fn lowers_conditional_and_infer_types() {
  let result = lower_from_source("type Cond<T> = T extends infer R ? R[] : never;").expect("lower");
  let (type_expr, type_params) = type_alias(&result, "Cond");
  assert_eq!(type_params.len(), 1);

  let expr = &result.types.type_exprs[type_expr.0 as usize];
  match &expr.kind {
    TypeExprKind::Conditional(cond) => {
      let extends = &result.types.type_exprs[cond.extends_type.0 as usize];
      assert!(matches!(extends.kind, TypeExprKind::Infer(_)));

      let true_type = &result.types.type_exprs[cond.true_type.0 as usize];
      match &true_type.kind {
        TypeExprKind::Array(arr) => {
          let element = &result.types.type_exprs[arr.element.0 as usize];
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

      let false_type = &result.types.type_exprs[cond.false_type.0 as usize];
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
  let (type_expr, type_params) = type_alias(&result, "Mapped");
  assert_eq!(type_params.len(), 1);

  let expr = &result.types.type_exprs[type_expr.0 as usize];
  match &expr.kind {
    TypeExprKind::Mapped(mapped) => {
      assert_eq!(mapped.readonly, TypeMappedModifier::None);
      assert_eq!(mapped.optional, TypeMappedModifier::None);
      assert!(mapped.name_type.is_some());
      let value_type = &result.types.type_exprs[mapped.value_type.0 as usize];
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

  let (index_expr, _) = type_alias(&result, "Index");
  let index = &result.types.type_exprs[index_expr.0 as usize];
  match &index.kind {
    TypeExprKind::IndexedAccess {
      object_type,
      index_type,
    } => {
      let last_index = &result.types.type_exprs[index_type.0 as usize];
      assert!(matches!(
        last_index.kind,
        TypeExprKind::Literal(hir_js::TypeLiteral::String(_))
      ));
      let first_index = &result.types.type_exprs[object_type.0 as usize];
      match &first_index.kind {
        TypeExprKind::IndexedAccess {
          object_type: first_object,
          index_type: first_key,
        } => {
          let first_key_expr = &result.types.type_exprs[first_key.0 as usize];
          assert!(matches!(
            first_key_expr.kind,
            TypeExprKind::Literal(hir_js::TypeLiteral::String(_))
          ));
          let object_expr = &result.types.type_exprs[first_object.0 as usize];
          assert!(matches!(object_expr.kind, TypeExprKind::TypeLiteral(_)));
        }
        other => panic!("expected nested indexed access, got {other:?}"),
      }
    }
    other => panic!("expected indexed access, got {other:?}"),
  }

  let (tmpl_expr, _) = type_alias(&result, "Tmpl");
  let tmpl = &result.types.type_exprs[tmpl_expr.0 as usize];
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
  assert_eq!(mapped, tmpl_expr);
}
