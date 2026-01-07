#[cfg(feature = "emit-minify")]
use crate::{
  clear_last_emit_backend_for_tests, force_hir_emit_failure_for_tests, last_emit_backend_for_tests,
  EmitBackend,
};
use crate::{
  minify, minify_with_options, Diagnostic, Dialect, FileId, MinifyOptions, Severity, TopLevelMode,
  TsEraseOptions,
};
use derive_visitor::{Drive, Visitor};
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMemberType};
use parse_js::ast::expr::jsx::{JsxAttr, JsxAttrVal, JsxElemChild, JsxElemName};
use parse_js::ast::expr::Expr;
use parse_js::ast::func::FuncBody;
use parse_js::ast::import_export::ImportNames;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{ClassDecl, FuncDecl, VarDeclMode};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::operator::OperatorName;
use parse_js::{parse, parse_with_options, ParseOptions, SourceType};
use semantic_js::assoc::js::resolved_symbol;
use semantic_js::js::bind_js;

fn minified(mode: TopLevelMode, src: &str) -> String {
  let mut out = Vec::new();
  minify(mode, src, &mut out).unwrap();
  String::from_utf8(out).unwrap()
}

fn minified_program(
  mode: TopLevelMode,
  input_dialect: Dialect,
  output_dialect: Dialect,
  src: &str,
) -> (String, Node<TopLevel>) {
  let mut out = Vec::new();
  minify_with_options(
    MinifyOptions::new(mode).with_dialect(input_dialect),
    src,
    &mut out,
  )
  .unwrap();
  let output = String::from_utf8(out).unwrap();
  let parsed = parse_with_options(
    &output,
    ParseOptions {
      dialect: output_dialect,
      source_type: match mode {
        TopLevelMode::Global => SourceType::Script,
        TopLevelMode::Module => SourceType::Module,
      },
    },
  )
  .expect("output should parse as JavaScript");
  (output, parsed)
}

#[cfg(feature = "emit-minify")]
fn minified_with_backend_options(options: MinifyOptions, src: &str) -> (String, EmitBackend) {
  clear_last_emit_backend_for_tests();
  let mut out = Vec::new();
  minify_with_options(options, src, &mut out).unwrap();
  let backend = last_emit_backend_for_tests().expect("emitter backend should be recorded");
  (String::from_utf8(out).unwrap(), backend)
}

#[cfg(feature = "emit-minify")]
fn try_minified_with_backend_options(
  options: MinifyOptions,
  src: &str,
) -> Result<(String, EmitBackend), Vec<Diagnostic>> {
  clear_last_emit_backend_for_tests();
  let mut out = Vec::new();
  minify_with_options(options, src, &mut out)?;
  let backend = last_emit_backend_for_tests().expect("emitter backend should be recorded");
  Ok((String::from_utf8(out).unwrap(), backend))
}

#[test]
fn test_shadow_safety() {
  let result = minified(
    TopLevelMode::Global,
    "let x=1;(()=>{let x=2;let y=x;return y})();",
  );
  assert_eq!(result, "let x=1;(()=>{let b=2;let a=b;return a;})();");
}

#[test]
fn test_unknown_globals_not_shadowed() {
  let result = minified(
    TopLevelMode::Global,
    "console.log(x);(()=>{let console=1;return console;})();",
  );
  assert_eq!(result, "console.log(x);(()=>{let a=1;return a;})();");
}

#[test]
fn test_module_export_bindings_preserved() {
  let result = minified(TopLevelMode::Module, "export const x=1; const y=2;");
  assert_eq!(result, "export const x=1;");
}

#[test]
fn preserves_string_import_aliases() {
  // Use direct `eval` to disable renaming so we can assert the raw output
  // contains the string literal import names.
  let result = minified(
    TopLevelMode::Module,
    r#"eval("x");import { "a-b" as c_d } from "x";"#,
  );
  assert_eq!(result, r#"eval("x");import{"a-b"as c_d}from"x";"#);
}

#[test]
fn preserves_namespace_imports() {
  // Use direct `eval` to disable renaming so we can assert the raw output
  // contains the namespace import.
  let result = minified(
    TopLevelMode::Module,
    r#"eval("x");import * as ns from "x";"#,
  );
  assert_eq!(result, r#"eval("x");import*as ns from"x";"#);
}

#[test]
fn reexport_keeps_renamed_string_import_aliases_in_sync() {
  // Exporting a binding imported from a string-named export should keep the
  // import binding name and the export specifier's `exportable` name consistent
  // after renaming.
  let result = minified(
    TopLevelMode::Module,
    r#"import { "a-b" as c_d } from "x";export { c_d as "e-f" };"#,
  );
  assert_eq!(result, r#"import{"a-b"as a}from"x";export{a as"e-f"};"#);
}

#[test]
fn reexport_keeps_renamed_default_import_in_sync() {
  // `default` is special-cased by the parser/emitters; ensure that importing it
  // via a named specifier still works with renaming + export specifier rewrites.
  let result = minified(
    TopLevelMode::Module,
    r#"import { default as c_d } from "x";export { c_d as "e-f" };"#,
  );
  assert_eq!(result, r#"import{default as a}from"x";export{a as"e-f"};"#);
}

#[test]
fn export_list_keeps_renamed_default_import_in_sync() {
  let result = minified(
    TopLevelMode::Module,
    r#"import { default as c_d } from "x";export { c_d as default };"#,
  );
  assert_eq!(
    result,
    r#"import{default as a}from"x";export{a as default};"#
  );
}

#[test]
fn reexport_keeps_renamed_namespace_import_aliases_in_sync() {
  // When we rename the internal binding, ensure export specifiers are updated
  // to reference the renamed name.
  let result = minified(
    TopLevelMode::Module,
    r#"import * as ns_name from "x";export { ns_name as ns };"#,
  );
  assert_eq!(result, r#"import*as a from"x";export{a as ns};"#);
}

#[test]
fn export_list_marks_local_binding_as_used() {
  let result = minified(TopLevelMode::Module, "const long=1;export { long as b };");
  assert_eq!(result, "const a=1;export{a as b};");
}

#[test]
fn export_list_string_alias_marks_local_binding_as_used() {
  let result = minified(
    TopLevelMode::Module,
    "const long=1;export { long as \"a-b\" };",
  );
  assert_eq!(result, "const a=1;export{a as\"a-b\"};");
}

#[test]
fn export_list_preserves_exported_name_when_local_is_renamed() {
  let result = minified(TopLevelMode::Module, "const foo=1;export { foo };");
  assert_eq!(result, "const a=1;export{a as foo};");
}

#[test]
fn export_star_alias_is_not_renamed() {
  let result = minified(
    TopLevelMode::Module,
    "const ns=1;export * as ns from \"mod\";",
  );
  assert_eq!(result, "export*as ns from\"mod\";");
}

#[test]
fn export_star_string_alias_is_preserved() {
  let result = minified(
    TopLevelMode::Module,
    "const ns=1;export * as \"ns-name\" from \"mod\";",
  );
  assert_eq!(result, "export*as\"ns-name\"from\"mod\";");
}

#[test]
fn export_star_default_alias_is_preserved() {
  let result = minified(
    TopLevelMode::Module,
    "const ns=1;export * as default from \"mod\";",
  );
  assert_eq!(result, "export*as default from\"mod\";");
}

#[test]
fn reexport_does_not_keep_or_rename_same_named_locals() {
  let result = minified(
    TopLevelMode::Module,
    "const foo=1;export { foo } from \"mod\";",
  );
  assert_eq!(result, "export{foo}from\"mod\";");
}

#[test]
fn preserves_default_export_in_reexports() {
  let result = minified(
    TopLevelMode::Module,
    "const foo=1;export { default } from \"mod\";",
  );
  assert_eq!(result, "export{default}from\"mod\";");
}

#[test]
fn preserves_default_as_string_literal_reexport() {
  let result = minified(
    TopLevelMode::Module,
    "const foo=1;export { default as \"a-b\" } from \"mod\";",
  );
  assert_eq!(result, "export{default as\"a-b\"}from\"mod\";");
}

#[test]
fn preserves_string_export_as_default_reexport() {
  let result = minified(
    TopLevelMode::Module,
    "const foo=1;export { \"a-b\" as default } from \"mod\";",
  );
  assert_eq!(result, "export{\"a-b\"as default}from\"mod\";");
}

#[test]
fn preserves_named_default_import_specifier() {
  // Use direct `eval` to disable renaming so we can assert on the raw output.
  let result = minified(
    TopLevelMode::Module,
    r#"eval("x");import { default as foo } from "x";export default foo;"#,
  );
  assert_eq!(
    result,
    r#"eval("x");import{default as foo}from"x";export default foo;"#
  );
}

#[test]
fn preserves_default_as_named_reexport() {
  let result = minified(
    TopLevelMode::Module,
    "const foo=1;export { default as foo } from \"mod\";",
  );
  assert_eq!(result, "export{default as foo}from\"mod\";");
}

#[test]
fn preserves_named_as_default_reexport() {
  let result = minified(
    TopLevelMode::Module,
    "const foo=1;export { foo as default } from \"mod\";",
  );
  assert_eq!(result, "export{foo as default}from\"mod\";");
}

#[test]
fn export_list_default_alias_is_preserved() {
  let result = minified(
    TopLevelMode::Module,
    "const foo=1;export { foo as default };",
  );
  assert_eq!(result, "const a=1;export{a as default};");
}

#[test]
fn preserves_string_export_names_in_reexports() {
  let result = minified(
    TopLevelMode::Module,
    "const foo=1;export { \"a-b\" as \"c-d\" } from \"mod\";",
  );
  assert_eq!(result, "export{\"a-b\"as\"c-d\"}from\"mod\";");
}

#[test]
fn preserves_side_effect_only_imports() {
  let result = minified(TopLevelMode::Module, "import \"side\";const x=1;");
  let normalized: String = result.chars().filter(|ch| !ch.is_whitespace()).collect();
  assert!(
    normalized.contains("import\"side\""),
    "side-effect-only import should be preserved: {result}"
  );
}

#[test]
fn removes_unused_named_import_specifiers() {
  let result = minified(
    TopLevelMode::Module,
    r#"import {foo,bar} from "x";console.log(foo);"#,
  );
  assert_eq!(result, r#"import{foo as a}from"x";console.log(a);"#);
}

#[test]
fn unused_default_import_becomes_side_effect_import() {
  let result = minified(
    TopLevelMode::Module,
    r#"import foo from "x";console.log(1);"#,
  );
  assert_eq!(result, r#"import"x";console.log(1);"#);
}

#[test]
fn unused_namespace_import_becomes_side_effect_import() {
  let result = minified(
    TopLevelMode::Module,
    r#"import * as ns from "x";console.log(1);"#,
  );
  assert_eq!(result, r#"import"x";console.log(1);"#);
}

#[test]
fn keeps_import_bindings_when_direct_eval_present() {
  let result = minified(
    TopLevelMode::Module,
    r#"import foo from "x";eval("foo");console.log(1);"#,
  );
  assert_eq!(result, r#"import foo from"x";eval("foo");console.log(1);"#);
}

#[test]
fn pruned_import_preserves_attributes() {
  let result = minified(
    TopLevelMode::Module,
    r#"import {foo} from "x" with { type: "json" };console.log(1);"#,
  );
  assert_eq!(result, r#"import"x"with{type:"json"};console.log(1);"#);
}

#[test]
fn empty_reexport_from_becomes_import() {
  let result = minified(
    TopLevelMode::Module,
    r#"export {} from "x";console.log(1);"#,
  );
  assert_eq!(result, r#"import"x";console.log(1);"#);
}

#[test]
fn empty_reexport_from_preserves_attributes() {
  let result = minified(
    TopLevelMode::Module,
    r#"export {} from "x" with { type: "json" };console.log(1);"#,
  );
  let normalized: String = result.chars().filter(|ch| !ch.is_whitespace()).collect();
  assert!(
    normalized.contains(r#"import"x"with{type:"json"}"#),
    "expected empty re-export to become attribute-preserving side-effect import: {result}"
  );
  assert!(
    !normalized.contains("export{}from"),
    "expected empty re-export to be rewritten to import: {result}"
  );
}

#[test]
fn type_only_import_does_not_become_side_effect_import() {
  let result = minified(
    TopLevelMode::Module,
    "import { type Foo } from \"mod\";const x=1;",
  );
  assert!(
    !result.contains("import"),
    "type-only imports should be erased without becoming side-effect imports: {result}"
  );
}

#[test]
fn type_only_default_named_import_is_removed() {
  let result = minified(
    TopLevelMode::Module,
    r#"import type { default as Foo } from "mod";export const x=1;"#,
  );
  assert_eq!(result, "export const x=1;");
}

#[test]
fn type_only_default_export_with_string_alias_is_removed() {
  let result = minified(
    TopLevelMode::Module,
    r#"export type { default as "a-b" } from "mod";export const x=1;"#,
  );
  assert_eq!(result, "export const x=1;");
}

#[test]
fn type_only_export_star_as_default_is_removed() {
  let result = minified(
    TopLevelMode::Module,
    r#"export type * as default from "mod";export const x=1;"#,
  );
  assert_eq!(result, "export const x=1;");
}

#[test]
fn type_only_string_export_as_default_is_removed() {
  let result = minified(
    TopLevelMode::Module,
    r#"export type { "a-b" as default } from "mod";export const x=1;"#,
  );
  assert_eq!(result, "export const x=1;");
}

#[test]
fn preserves_module_import_export_attributes() {
  let result = minified(
    TopLevelMode::Module,
    "import \"side\" with { type: \"json\" };export { a as b } from \"pkg\" with { type: \"json\" };",
  );
  let normalized: String = result.chars().filter(|ch| !ch.is_whitespace()).collect();
  assert!(
    normalized.contains("with{type:\"json\"}"),
    "module import/export attributes should be preserved: {result}"
  );
}

#[test]
fn returns_diagnostics_on_parse_error() {
  let mut output = Vec::new();
  let diagnostics = minify(TopLevelMode::Global, "let =", &mut output).unwrap_err();
  assert_eq!(diagnostics.len(), 1);
  let diagnostic = &diagnostics[0];
  assert!(diagnostic.code.as_str().starts_with("PS"));
  assert_eq!(diagnostic.primary.file, FileId(0));
  assert_eq!(diagnostic.severity, Severity::Error);
}

#[test]
fn returns_diagnostics_on_binding_error() {
  let mut output = Vec::new();
  let source = "x; let x = 1;";
  let diagnostics = minify(TopLevelMode::Module, source, &mut output).unwrap_err();
  assert!(!diagnostics.is_empty());
  assert!(
    diagnostics
      .iter()
      .any(|diag| diag.code.as_str().starts_with("BIND")),
    "expected binder diagnostics, got {diagnostics:?}"
  );
  assert!(output.is_empty());
}

#[test]
fn test_export_function_inner_locals_renamed() {
  let result = minified(
    TopLevelMode::Module,
    "export function foo(){let bar=1;return bar;}",
  );
  assert_eq!(result, "export function foo(){let a=1;return a;}");
}

#[test]
fn test_minify_determinism() {
  let src =
    "const foo=1; const qux=2; function bar(){ let baz=foo+qux; return baz; } export { bar };";
  let first = minified(TopLevelMode::Module, src);
  let second = minified(TopLevelMode::Module, src);
  assert_eq!(first, second);
}

#[test]
fn folds_numeric_expressions() {
  let result = minified(TopLevelMode::Global, "console.log(1+2*3);");
  assert_eq!(result, "console.log(7);");
}

#[test]
fn folds_constant_comparisons() {
  let result = minified(TopLevelMode::Global, "console.log(1<2);");
  assert_eq!(result, "console.log(true);");
}

#[test]
fn folds_constant_strict_equality() {
  let result = minified(TopLevelMode::Global, "console.log(1===2);");
  assert_eq!(result, "console.log(false);");
}

#[test]
fn folds_constant_loose_equality() {
  let result = minified(TopLevelMode::Global, "console.log(null==undefined);");
  assert_eq!(result, "console.log(true);");
}

#[test]
fn folds_string_concatenation() {
  let result = minified(TopLevelMode::Global, r#"console.log("a"+"b");"#);
  assert_eq!(result, r#"console.log("ab");"#);
}

#[test]
fn folds_string_concatenation_with_non_string_literals() {
  let result = minified(TopLevelMode::Global, r#"console.log("a"+1);"#);
  assert_eq!(result, r#"console.log("a1");"#);
}

#[test]
fn folds_boolean_negation() {
  let result = minified(TopLevelMode::Global, "console.log(!true);");
  assert_eq!(result, "console.log(false);");
}

#[test]
fn rewrites_computed_member_string_keys_to_dot_access() {
  let result = minified(TopLevelMode::Global, r#"let obj={foo:1};obj["foo"];"#);
  assert_eq!(result, "let obj={foo:1};obj.foo;");
}

#[test]
fn rewrites_computed_member_numeric_string_keys_to_number_access() {
  let result = minified(TopLevelMode::Global, r#"let obj=[1];obj["0"];"#);
  assert_eq!(result, "let obj=[1];obj[0];");
}

#[test]
fn rewrites_computed_member_large_numeric_string_keys_to_number_access() {
  let result = minified(TopLevelMode::Global, r#"let obj={};obj["4294967296"];"#);
  assert_eq!(result, "let obj={};obj[4294967296];");
}

#[test]
fn does_not_rewrite_non_identifier_computed_member_string_keys() {
  let result = minified(TopLevelMode::Global, r#"let obj={};obj["a-b"];"#);
  assert_eq!(result, r#"let obj={};obj["a-b"];"#);
}

#[test]
fn rewrites_object_literal_string_keys_to_identifier_keys() {
  let result = minified(TopLevelMode::Global, r#"let obj={"foo":1};obj.foo;"#);
  assert_eq!(result, "let obj={foo:1};obj.foo;");
}

#[test]
fn rewrites_object_literal_numeric_string_keys_to_number_keys() {
  let result = minified(TopLevelMode::Global, r#"let obj={"0":1};obj["0"];"#);
  assert_eq!(result, "let obj={0:1};obj[0];");
}

#[test]
fn rewrites_object_literal_large_numeric_string_keys_to_number_keys() {
  let result = minified(
    TopLevelMode::Global,
    r#"let obj={"4294967296":1};obj["4294967296"];"#,
  );
  assert_eq!(result, "let obj={4294967296:1};obj[4294967296];");
}

#[test]
fn rewrites_object_literal_computed_string_keys_to_direct_keys() {
  let result = minified(TopLevelMode::Global, r#"let obj={["a-b"]:1};"#);
  assert_eq!(result, r#"let obj={"a-b":1};"#);
}

#[test]
fn does_not_rewrite_proto_object_literal_computed_string_keys() {
  let result = minified(TopLevelMode::Global, r#"let obj={["__proto__"]:null};"#);
  assert_eq!(result, r#"let obj={["__proto__"]:null};"#);
}

#[test]
fn rewrites_object_pattern_numeric_string_keys_to_number_keys() {
  let result = minified(
    TopLevelMode::Module,
    r#"const obj={0:1};const {"0":x}=obj;console.log(x);"#,
  );
  assert_eq!(result, r#"const a={0:1};const{0:b}=a;console.log(b);"#);
}

#[test]
fn rewrites_object_pattern_computed_string_keys_to_direct_keys() {
  let result = minified(
    TopLevelMode::Module,
    r#"const obj={"a-b":1};const {["a-b"]:x}=obj;console.log(x);"#,
  );
  assert_eq!(
    result,
    r#"const a={"a-b":1};const{"a-b":b}=a;console.log(b);"#
  );
}

#[test]
fn rewrites_object_pattern_computed_proto_keys_to_direct_keys() {
  // Object patterns have no special `__proto__` semantics, so dropping computed keys is safe.
  let result = minified(
    TopLevelMode::Module,
    r#"const obj={["__proto__"]:1};const {["__proto__"]:x}=obj;console.log(x);"#,
  );
  assert_eq!(
    result,
    r#"const a={["__proto__"]:1};const{__proto__:b}=a;console.log(b);"#
  );
}

#[test]
fn rewrites_object_literal_value_properties_to_shorthand() {
  let result = minified(TopLevelMode::Global, "let a=1;let obj={a:a};");
  assert_eq!(result, "let a=1;let obj={a};");
}

#[test]
fn does_not_rewrite_proto_object_literal_value_properties_to_shorthand() {
  let result = minified(
    TopLevelMode::Global,
    "let __proto__=1;let obj={__proto__:__proto__};",
  );
  assert_eq!(result, "let __proto__=1;let obj={__proto__:__proto__};");
}

#[test]
fn renaming_expands_object_literal_shorthand_properties() {
  // When bindings are renamed, object literal shorthands must be expanded to keep
  // the original property key strings in sync with member accesses.
  let result = minified(
    TopLevelMode::Module,
    "const x=1;const obj={x};console.log(obj.x);",
  );
  assert_eq!(result, "const b=1;const a={x:b};console.log(a.x);");
}

#[test]
fn renaming_expands_object_pattern_shorthand_properties() {
  let result = minified(
    TopLevelMode::Module,
    "const obj={x:1};const {x}=obj;console.log(x);",
  );
  assert_eq!(result, "const a={x:1};const{x:b}=a;console.log(b);");
}

#[test]
fn object_literal_shorthand_rewrite_runs_after_renaming() {
  // `{x:x}` can only be rewritten to `{x}` when `x` is not renamed; ensure the
  // rewrite runs after renaming so we don't desync property keys from accesses.
  let result = minified(
    TopLevelMode::Module,
    "const x=1;const obj={x:x};console.log(obj.x);",
  );
  assert_eq!(result, "const b=1;const a={x:b};console.log(a.x);");
}

#[test]
fn rewrites_object_pattern_value_properties_to_shorthand() {
  let result = minified(
    TopLevelMode::Module,
    "const obj={x:1};export const {x:x}=obj;console.log(x);",
  );
  assert_eq!(result, "const a={x:1};export const{x}=a;console.log(x);");
}

#[test]
fn rewrites_object_pattern_value_properties_to_shorthand_with_default_value() {
  let result = minified(
    TopLevelMode::Module,
    "const obj={};export const {x:x=1}=obj;console.log(x);",
  );
  assert_eq!(result, "const a={};export const{x=1}=a;console.log(x);");
}

#[test]
fn object_pattern_shorthand_rewrite_runs_after_renaming() {
  // The binding may be renamed to match the property key; ensure we still
  // shorten the destructuring pattern afterwards.
  let result = minified(
    TopLevelMode::Module,
    "export const obj={a:1};const {a:long_name}=obj;console.log(long_name);",
  );
  assert_eq!(
    result,
    "export const obj={a:1};const{a}=obj;console.log(a);"
  );
}

#[test]
fn rewrites_if_to_logical_and() {
  let result = minified(TopLevelMode::Global, "if(foo)bar();");
  assert_eq!(result, "foo&&bar();");
}

#[test]
fn rewrites_if_to_ternary_expression() {
  let result = minified(TopLevelMode::Global, "if(foo)a();else b();");
  assert_eq!(result, "foo?a():b();");
}

#[test]
fn removes_unreachable_if_branches() {
  let result = minified(TopLevelMode::Global, "if(false)foo();bar();");
  assert_eq!(result, "bar();");
}

#[test]
fn removes_branches_after_const_folding() {
  let result = minified(TopLevelMode::Global, "if(1<2)foo();else bar();");
  assert_eq!(result, "foo();");
}

#[test]
fn folds_nullish_coalescing_with_void_zero() {
  let result = minified(TopLevelMode::Global, "console.log((void 0)??1);");
  assert_eq!(result, "console.log(1);");
}

#[test]
fn removes_unreachable_if_branches_in_arrow_expr_bodies() {
  let result = minified(
    TopLevelMode::Global,
    "const f=()=>{if(false){sideEffect()}return 1;};",
  );
  assert_eq!(result, "const f=()=>{return 1;};");
}

#[test]
fn dce_removes_unused_locals_in_arrow_expr_bodies() {
  let result = minified(TopLevelMode::Global, "const f=()=>{let x=1;return 2;};");
  assert_eq!(result, "const f=()=>{return 2;};");
}

#[test]
fn dce_removes_unused_arrow_function_initializers_in_nested_scopes() {
  let result = minified(
    TopLevelMode::Global,
    "const f=()=>{let g=()=>{if(false){sideEffect()}return 1;};return 2;};",
  );
  assert_eq!(result, "const f=()=>{return 2;};");
}

#[test]
fn dce_removes_unused_function_expr_initializers_in_nested_scopes() {
  let result = minified(
    TopLevelMode::Global,
    "const f=()=>{let g=function(){if(false){sideEffect()}return 1;};return 2;};",
  );
  assert_eq!(result, "const f=()=>{return 2;};");
}

#[test]
fn dce_removes_unused_object_literals_with_function_values() {
  let result = minified(
    TopLevelMode::Global,
    "const f=()=>{let o={f:()=>sideEffect()};return 2;};",
  );
  assert_eq!(result, "const f=()=>{return 2;};");
}

#[test]
fn dce_eliminates_transitively_unused_closure_chains() {
  let result = minified(
    TopLevelMode::Module,
    "let x=1;let y=()=>x;let z=()=>y;console.log(2);",
  );
  assert_eq!(result, "console.log(2);");
}

#[test]
fn dce_removes_unused_class_expr_initializers() {
  let result = minified(TopLevelMode::Module, "let C=class{m(){}};console.log(2);");
  assert_eq!(result, "console.log(2);");
}

#[test]
fn annex_b_block_function_used_via_hoisted_var_is_not_removed() {
  let src = "function outer(){if(false){function foo(){} }foo;}outer();";
  let (output, mut parsed) = minified_program(TopLevelMode::Global, Dialect::Js, Dialect::Js, src);

  let (_sem, diagnostics) = bind_js(&mut parsed, TopLevelMode::Global, FileId(0));
  assert!(
    diagnostics.is_empty(),
    "expected output to bind cleanly, got {diagnostics:?}"
  );

  let outer_decl = parsed
    .stx
    .body
    .iter()
    .find_map(|stmt| match stmt.stx.as_ref() {
      Stmt::FunctionDecl(decl) => Some(decl),
      _ => None,
    })
    .expect("expected top-level outer function decl");
  let Some(body) = outer_decl.stx.function.stx.body.as_ref() else {
    panic!("outer function should have a body: {output}");
  };
  let FuncBody::Block(stmts) = body else {
    panic!("outer function should have a block body: {output}");
  };
  let id_use = stmts
    .iter()
    .find_map(|stmt| match stmt.stx.as_ref() {
      Stmt::Expr(expr_stmt) => match expr_stmt.stx.expr.stx.as_ref() {
        Expr::Id(id) => Some(id),
        _ => None,
      },
      _ => None,
    })
    .expect("expected identifier use in outer function body");

  assert!(
    resolved_symbol(&id_use.assoc).is_some(),
    "expected identifier use to resolve to a local binding: {output}"
  );
}

#[test]
fn dce_removes_unused_function_decls() {
  let (output, parsed) = minified_program(
    TopLevelMode::Module,
    Dialect::Js,
    Dialect::Js,
    "function outer(){function dead(){}return 1;}outer();",
  );

  type FuncDeclNode = Node<FuncDecl>;
  #[derive(Default, Visitor)]
  #[visitor(FuncDeclNode(enter))]
  struct Counter {
    count: usize,
  }
  impl Counter {
    fn enter_func_decl_node(&mut self, _node: &FuncDeclNode) {
      self.count += 1;
    }
  }

  let mut counter = Counter::default();
  parsed.drive(&mut counter);
  assert_eq!(counter.count, 1, "unexpected output: {output}");
}

#[test]
fn dce_removes_unused_side_effect_free_class_decls() {
  let (output, parsed) = minified_program(
    TopLevelMode::Module,
    Dialect::Js,
    Dialect::Js,
    "function outer(){class C{}return 1;}outer();",
  );

  type ClassDeclNode = Node<ClassDecl>;
  #[derive(Default, Visitor)]
  #[visitor(ClassDeclNode(enter))]
  struct Counter {
    count: usize,
  }
  impl Counter {
    fn enter_class_decl_node(&mut self, _node: &ClassDeclNode) {
      self.count += 1;
    }
  }

  let mut counter = Counter::default();
  parsed.drive(&mut counter);
  assert_eq!(counter.count, 0, "unexpected output: {output}");
}

#[test]
fn dce_keeps_side_effectful_class_decls() {
  let (output, parsed) = minified_program(
    TopLevelMode::Module,
    Dialect::Js,
    Dialect::Js,
    "function outer(){class C{static{sideEffect()}}return 1;}outer();",
  );

  type ClassDeclNode = Node<ClassDecl>;
  #[derive(Default, Visitor)]
  #[visitor(ClassDeclNode(enter))]
  struct Counter {
    count: usize,
  }
  impl Counter {
    fn enter_class_decl_node(&mut self, _node: &ClassDeclNode) {
      self.count += 1;
    }
  }

  let mut counter = Counter::default();
  parsed.drive(&mut counter);
  assert_eq!(counter.count, 1, "unexpected output: {output}");
}

#[test]
fn dce_keeps_class_expr_static_blocks_with_side_effects() {
  let result = minified(
    TopLevelMode::Global,
    "function f(){let C=class{static{sideEffect()}};return 1;}f();",
  );
  assert_eq!(
    result,
    "function f(){(class{static{sideEffect();}});return 1;}f();"
  );
}

#[test]
fn dce_rewrites_unused_side_effectful_single_declarator_into_expr_stmt() {
  let result = minified(
    TopLevelMode::Global,
    "function f(){let x=sideEffect();return 1;}f();",
  );
  assert_eq!(result, "function f(){sideEffect();return 1;}f();");
}

#[test]
fn dce_preserves_order_when_dropping_leading_side_effectful_declarator() {
  let (_output, parsed) = minified_program(
    TopLevelMode::Global,
    Dialect::Js,
    Dialect::Js,
    "function f(){let a=sideEffect(),b=keep();return b;}f();",
  );
  let func = match parsed.stx.body.first().map(|stmt| stmt.stx.as_ref()) {
    Some(Stmt::FunctionDecl(func)) => func,
    other => panic!("expected function decl, got {other:?}"),
  };
  let body = match func.stx.function.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };
  let var_decl = match body.first().map(|stmt| stmt.stx.as_ref()) {
    Some(Stmt::VarDecl(decl)) => decl,
    other => panic!("expected var decl stmt, got {other:?}"),
  };
  assert_eq!(var_decl.stx.mode, VarDeclMode::Let);
  assert_eq!(var_decl.stx.declarators.len(), 1);
  let init = var_decl.stx.declarators[0]
    .initializer
    .as_ref()
    .expect("initializer");
  fn collect_calls(expr: &Node<Expr>, out: &mut Vec<String>) {
    match expr.stx.as_ref() {
      Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
        collect_calls(&bin.stx.left, out);
        collect_calls(&bin.stx.right, out);
      }
      Expr::Call(call) => match call.stx.callee.stx.as_ref() {
        Expr::Id(id) => out.push(id.stx.name.clone()),
        other => panic!("expected id callee, got {other:?}"),
      },
      other => panic!("expected comma/call expr, got {other:?}"),
    }
  }
  let mut calls: Vec<String> = Vec::new();
  collect_calls(init, &mut calls);
  assert_eq!(calls, vec!["sideEffect".to_string(), "keep".to_string()]);
}

#[test]
fn dce_preserves_order_when_dropping_trailing_side_effectful_declarator() {
  let (_output, parsed) = minified_program(
    TopLevelMode::Global,
    Dialect::Js,
    Dialect::Js,
    "function f(){let b=keep(),a=sideEffect();return b;}f();",
  );
  let func = match parsed.stx.body.first().map(|stmt| stmt.stx.as_ref()) {
    Some(Stmt::FunctionDecl(func)) => func,
    other => panic!("expected function decl, got {other:?}"),
  };
  let body = match func.stx.function.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };
  assert_eq!(body.len(), 3);
  match body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => {
      assert_eq!(decl.stx.declarators.len(), 1);
      let init = decl.stx.declarators[0]
        .initializer
        .as_ref()
        .expect("initializer");
      assert!(matches!(init.stx.as_ref(), Expr::Call(_)));
    }
    other => panic!("expected var decl stmt, got {other:?}"),
  }
  match body[1].stx.as_ref() {
    Stmt::Expr(expr_stmt) => match expr_stmt.stx.expr.stx.as_ref() {
      Expr::Call(call) => match call.stx.callee.stx.as_ref() {
        Expr::Id(id) => assert_eq!(id.stx.name, "sideEffect"),
        other => panic!("expected id callee, got {other:?}"),
      },
      other => panic!("expected call expression, got {other:?}"),
    },
    other => panic!("expected expr stmt, got {other:?}"),
  }
}

#[test]
fn dce_preserves_order_when_dropping_mid_side_effectful_declarator() {
  let (_output, parsed) = minified_program(
    TopLevelMode::Global,
    Dialect::Js,
    Dialect::Js,
    "function f(){let b=keep1(),a=sideEffect(),c=keep2();return b+c;}f();",
  );
  let func = match parsed.stx.body.first().map(|stmt| stmt.stx.as_ref()) {
    Some(Stmt::FunctionDecl(func)) => func,
    other => panic!("expected function decl, got {other:?}"),
  };
  let body = match func.stx.function.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };
  let var_decl = match body.first().map(|stmt| stmt.stx.as_ref()) {
    Some(Stmt::VarDecl(decl)) => decl,
    other => panic!("expected var decl stmt, got {other:?}"),
  };
  assert_eq!(var_decl.stx.declarators.len(), 2);
  let init = var_decl.stx.declarators[1]
    .initializer
    .as_ref()
    .expect("initializer");
  let mut calls: Vec<String> = Vec::new();
  fn collect_calls(expr: &Node<Expr>, out: &mut Vec<String>) {
    match expr.stx.as_ref() {
      Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
        collect_calls(&bin.stx.left, out);
        collect_calls(&bin.stx.right, out);
      }
      Expr::Call(call) => match call.stx.callee.stx.as_ref() {
        Expr::Id(id) => out.push(id.stx.name.clone()),
        other => panic!("expected id callee, got {other:?}"),
      },
      other => panic!("expected comma/call expr, got {other:?}"),
    }
  }
  collect_calls(init, &mut calls);
  assert_eq!(calls, vec!["sideEffect".to_string(), "keep2".to_string()]);
}

#[test]
fn dce_keeps_exported_bindings_and_converts_unused_side_effect_decls() {
  let result = minified(
    TopLevelMode::Module,
    "export const x=sideEffect();const y=sideEffect2();",
  );
  assert_eq!(result, "export const x=sideEffect();sideEffect2();");
}

#[test]
fn direct_eval_disables_dce_in_nested_arrow_expr_bodies() {
  let result = minified(
    TopLevelMode::Global,
    r#"const f=()=>{if(false){sideEffect()}let x=1;eval("x");return 2;};"#,
  );
  assert_eq!(result, r#"const f=()=>{let x=1;eval("x");return 2;};"#);
}

#[test]
fn with_statement_disables_dce_in_nested_arrow_expr_bodies() {
  let result = minified(
    TopLevelMode::Global,
    "call(()=>{with({}){let x=1;}return 2;});",
  );
  assert_eq!(result, "call(()=>{with({}){let x=1;}return 2;});");
}

#[test]
fn direct_eval_disables_dce_in_ancestor_scopes() {
  let result = minified(TopLevelMode::Module, r#"let x=1;(()=>{eval("x");})();"#);
  assert_eq!(result, r#"let x=1;(()=>{eval("x");})();"#);
}

#[test]
fn semantic_rewrite_does_not_break_dce_symbol_tracking() {
  let result = minified(
    TopLevelMode::Module,
    "let x=1;if(x===null||x===undefined)g();",
  );
  assert_eq!(result, "let a=1;a==null&&g();");
}

#[test]
fn optimizes_object_literal_methods_in_expression_position() {
  let result = minified(
    TopLevelMode::Global,
    "const o={m(){if(false){sideEffect()}return 1;}};",
  );
  assert_eq!(result, "const o={m(){return 1;}};");
}

#[test]
fn optimizes_arrow_functions_in_call_arguments() {
  let result = minified(
    TopLevelMode::Global,
    "call(()=>{if(false){sideEffect()}return 1;});",
  );
  assert_eq!(result, "call(()=>{return 1;});");
}

#[test]
fn optimizes_function_expressions_in_call_arguments() {
  let result = minified(
    TopLevelMode::Global,
    "call(function(){if(false){sideEffect()}return 1;});",
  );
  assert_eq!(result, "call(function(){return 1;});");
}

#[test]
fn optimizes_class_expression_methods_in_expression_position() {
  let result = minified(
    TopLevelMode::Global,
    "const C=class{m(){if(false){sideEffect()}return 1;}};",
  );
  assert_eq!(result, "const C=class{m(){return 1;}};");
}

#[test]
fn optimizes_static_blocks_in_class_expressions() {
  let result = minified(
    TopLevelMode::Global,
    "const C=class{static{if(false){sideEffect()}let x=1;}};",
  );
  assert_eq!(result, "const C=class{static{}};");
}

#[test]
fn optimizes_nested_arrows_inside_arrow_expression_bodies() {
  let result = minified(
    TopLevelMode::Global,
    "const f=()=>()=>{if(false){sideEffect()}return 1;};",
  );
  assert_eq!(result, "const f=()=>()=>{return 1;};");
}

#[test]
fn optimizes_getters_in_object_literals() {
  let result = minified(
    TopLevelMode::Global,
    "const o={get m(){if(false){sideEffect()}return 1;}};",
  );
  assert_eq!(result, "const o={get m(){return 1;}};");
}

#[test]
fn optimizes_setters_in_object_literals() {
  let result = minified(
    TopLevelMode::Global,
    "const o={set m(v){if(false){sideEffect()}let x=1;}};",
  );
  assert_eq!(result, "const o={set m(a){}};");
}

#[test]
fn optimizes_static_blocks_in_class_decls() {
  let result = minified(
    TopLevelMode::Global,
    "class C{static{if(false){sideEffect()}let x=1;}}",
  );
  assert_eq!(result, "class C{static{}}");
}

#[test]
fn optimizes_getters_in_class_expressions() {
  let result = minified(
    TopLevelMode::Global,
    "const C=class{get m(){if(false){sideEffect()}return 1;}};",
  );
  assert_eq!(result, "const C=class{get m(){return 1;}};");
}

#[test]
fn optimizes_arrow_functions_in_class_field_initializers() {
  let result = minified(
    TopLevelMode::Global,
    "class C{f=()=>{if(false){sideEffect()}return 1;}}",
  );
  assert_eq!(result, "class C{f=(()=>{return 1;});}");
}

#[test]
fn with_in_outer_scope_does_not_disable_dce_in_inner_arrow() {
  let result = minified(
    TopLevelMode::Global,
    "const f=()=>{with({}){}return()=>{let x=1;return 2;};};",
  );
  assert_eq!(result, "const f=()=>{with({});return()=>{return 2;};};");
}

#[test]
fn direct_eval_in_outer_scope_does_not_disable_dce_in_inner_arrow() {
  let result = minified(
    TopLevelMode::Global,
    r#"const f=()=>{eval("x");return()=>{let y=1;return 2;};};"#,
  );
  assert_eq!(result, r#"const f=()=>{eval("x");return()=>{return 2;};};"#);
}

#[test]
fn direct_eval_disables_undefined_rewrites_in_descendant_scopes() {
  // Direct `eval` can introduce new bindings in the surrounding scope at
  // runtime. Nested functions close over that environment record, so rewrites
  // that assume `undefined` is the global value are not sound in descendants.
  let result = minified(
    TopLevelMode::Global,
    r#"function f(){eval("var undefined=1");return()=>undefined;}"#,
  );
  assert_eq!(
    result,
    r#"function f(){eval("var undefined=1");return()=>undefined;}"#
  );

  let result = minified(
    TopLevelMode::Global,
    r#"function f(){eval("var undefined=1");return function(){return undefined;};}"#,
  );
  assert_eq!(
    result,
    r#"function f(){eval("var undefined=1");return function(){return undefined;};}"#
  );
}

#[test]
fn direct_eval_disables_nullish_or_rewrite_in_descendant_scopes() {
  // `x===null||x===undefined` → `x==null` is only sound when `undefined` is known
  // to be the global value. Direct `eval` in a parent scope can introduce a new
  // `undefined` binding at runtime that nested functions close over.
  let src = r#"function f(x){eval("var undefined=1");return()=>x===null||x===undefined;}"#;
  let result = minified(TopLevelMode::Global, src);
  assert_eq!(result, src);
}

#[test]
fn removes_unused_var_decls_with_pure_initializers() {
  let result = minified(TopLevelMode::Module, "let x=1;console.log(2);");
  assert_eq!(result, "console.log(2);");
}

#[test]
fn rewrites_return_undefined() {
  let result = minified(TopLevelMode::Global, "function f(){return undefined;}");
  assert_eq!(result, "function f(){return;}");
}

#[test]
fn rewrites_global_undefined_to_void_zero() {
  let result = minified(TopLevelMode::Global, "g(undefined);");
  assert_eq!(result, "g(void 0);");
}

#[test]
fn direct_eval_disables_global_undefined_to_void_zero_rewrite() {
  let src = "function f(){eval(\"x\");g(undefined);}";
  let result = minified(TopLevelMode::Global, src);
  assert_eq!(result, src);
}

#[test]
fn does_not_rewrite_shadowed_undefined() {
  let result = minified(
    TopLevelMode::Global,
    "function f(undefined){return undefined;}",
  );
  assert_eq!(result, "function f(a){return a;}");
}

#[test]
fn rewrites_nullish_or_to_loose_equality() {
  let result = minified(
    TopLevelMode::Global,
    "function f(x){if(x===null||x===undefined)g();}",
  );
  assert_eq!(result, "function f(a){a==null&&g();}");
}

#[cfg(feature = "emit-minify")]
#[test]
fn hir_emitter_matches_ast_output() {
  let cases = [
    (
      "basic minification",
      TopLevelMode::Global,
      Dialect::Js,
      "function wrap(value){return value+1;} const result=wrap(2); const doubled=wrap(result);",
    ),
    (
      "arrow function expression statement",
      TopLevelMode::Global,
      Dialect::Js,
      "long_parameter_name=>long_parameter_name;",
    ),
    (
      "object literal async/generator methods",
      TopLevelMode::Global,
      Dialect::Js,
      "const obj={async m(){await 1;},*g(){yield 1;},async *ag(){yield 1;}};console.log(obj);",
    ),
    (
      "new expression with optional chaining callee",
      TopLevelMode::Global,
      Dialect::Js,
      "new abc?.def();",
    ),
    (
      "exported class with fields/accessors/static block",
      TopLevelMode::Module,
      Dialect::Js,
      "export class Foo{static x=1;#p=2;get v(){return this.#p}set v(x){this.#p=x}static{Foo.x++}}",
    ),
    (
      "module import/export attributes",
      TopLevelMode::Module,
      Dialect::Js,
      "import * as ns from \"pkg\" with { type: \"json\" };export { a as b } from \"pkg\" with { type: \"json\" };ns;",
    ),
    (
      "side-effect export-from statement",
      TopLevelMode::Module,
      Dialect::Js,
      "export {} from \"./side\";",
    ),
    (
      "string-named import/export specifiers",
      TopLevelMode::Module,
      Dialect::Js,
      "import { \"a-b\" as c_d } from \"x\";export { c_d as \"e-f\" };",
    ),
    (
      "jsx element with nested arrow function",
      TopLevelMode::Module,
      Dialect::Jsx,
      "export const list = <ul>{items.map(item => <li>{item}</li>)}</ul>;",
    ),
    (
      "export default arrow expression",
      TopLevelMode::Module,
      Dialect::Js,
      "export default (value => ({computed: value ?? 0}));",
    ),
    (
      "export default undefined literal",
      TopLevelMode::Module,
      Dialect::Js,
      "export default undefined;",
    ),
    (
      "decorated export",
      TopLevelMode::Module,
      Dialect::Ts,
      "@dec export class C {}",
    ),
  ];

  let mut failures = Vec::new();

  for (name, mode, dialect, src) in cases {
    let hir =
      try_minified_with_backend_options(MinifyOptions::new(mode).with_dialect(dialect), src);
    let (hir_output, hir_backend) = match hir {
      Ok(ok) => ok,
      Err(diags) => {
        failures.push(format!(
          "{name}: HIR minify failed\nsrc:\n{src}\ndiagnostics:\n{diags:?}"
        ));
        continue;
      }
    };
    if hir_backend != EmitBackend::Hir {
      failures.push(format!(
        "{name}: expected HIR backend, got {hir_backend:?}\nsrc:\n{src}\noutput:\n{hir_output}"
      ));
      continue;
    }

    force_hir_emit_failure_for_tests();
    let ast =
      try_minified_with_backend_options(MinifyOptions::new(mode).with_dialect(dialect), src);
    let (ast_output, ast_backend) = match ast {
      Ok(ok) => ok,
      Err(diags) => {
        failures.push(format!(
          "{name}: AST minify failed\nsrc:\n{src}\ndiagnostics:\n{diags:?}"
        ));
        continue;
      }
    };
    if ast_backend != EmitBackend::Ast {
      failures.push(format!(
        "{name}: expected AST backend, got {ast_backend:?}\nsrc:\n{src}\noutput:\n{ast_output}"
      ));
      continue;
    }

    if hir_output != ast_output {
      failures.push(format!(
        "{name}: HIR and AST output differ\nsrc:\n{src}\nhir:\n{hir_output}\nast:\n{ast_output}"
      ));
    }
  }

  if !failures.is_empty() {
    panic!(
      "HIR/AST emission parity failures ({}):\n\n{}",
      failures.len(),
      failures.join("\n\n")
    );
  }
}

#[cfg(feature = "emit-minify")]
#[test]
fn hir_minify_preserves_decorators() {
  let src = "@dec export class C {}";
  let (output, backend) = minified_with_backend_options(
    MinifyOptions::new(TopLevelMode::Module).with_dialect(Dialect::Ts),
    src,
  );
  assert_eq!(backend, EmitBackend::Hir);
  assert!(
    output.contains("@dec"),
    "expected minified output to preserve decorators\nsrc:\n{src}\noutput:\n{output}"
  );
  parse_with_options(
    &output,
    ParseOptions {
      dialect: Dialect::Js,
      source_type: SourceType::Module,
    },
  )
  .expect("minified output should parse as JavaScript");
}

#[cfg(feature = "emit-minify")]
#[test]
fn hir_emitter_preserves_debugger_statement() {
  let (output, backend) = minified_with_backend_options(
    MinifyOptions::new(TopLevelMode::Global).with_dialect(Dialect::Js),
    "debugger;",
  );
  assert_eq!(backend, EmitBackend::Hir);
  assert_eq!(output, "debugger;");
}

#[test]
fn readme_example_is_parseable() {
  let code = "const main = () => { let my_first_variable = 1; };";
  let result = minified(TopLevelMode::Global, code);
  parse(&result).expect("minified output should be parseable JavaScript");
}

#[test]
fn test_with_statement_disables_renaming() {
  let src = "with ({x:2}){x}";
  let result = minified(TopLevelMode::Global, src);
  assert_eq!(result, "with({x:2}){x;}");
}

#[test]
fn with_statement_does_not_rewrite_undefined_property() {
  let src = "with({undefined:1}){undefined}";
  let result = minified(TopLevelMode::Global, src);
  assert_eq!(result, "with({undefined:1}){undefined;}");
}

#[test]
fn with_statement_keeps_undefined_in_nested_functions() {
  let src = "with({undefined:1}){(function(){return undefined;})()}";
  let result = minified(TopLevelMode::Global, src);
  assert!(
    result.contains("return undefined"),
    "expected `undefined` to be preserved inside nested functions in with bodies\nsrc:\n{src}\noutput:\n{result}"
  );
}

#[test]
fn with_statement_keeps_nullish_checks_in_nested_functions() {
  let src = "with({undefined:1}){(function(x){return x===null||x===undefined;})()}";
  let result = minified(TopLevelMode::Global, src);
  assert!(
    result.contains("===undefined") && result.contains("||"),
    "expected nullish-or checks to remain strict inside nested functions in with bodies\nsrc:\n{src}\noutput:\n{result}"
  );
}

#[test]
fn test_direct_eval_disables_renaming() {
  let src = "function f(){let x;eval(\"x\");}";
  let result = minified(TopLevelMode::Global, src);
  assert_eq!(result, src);
}

#[test]
fn test_shadowed_eval_allows_renaming() {
  let src = "function f(eval){let x;eval(\"x\");}";
  let result = minified(TopLevelMode::Global, src);
  assert_eq!(result, "function f(a){a(\"x\");}");
}

#[test]
fn test_with_in_nested_scope_only_disables_that_scope() {
  let src = "(()=>{function outer(){let top=1;function inner(obj){let value=obj.v;with(obj){value;}return value;}return inner({v:top})+top;}return outer();})();";
  let result = minified(TopLevelMode::Global, src);
  assert_eq!(
    result,
    "(()=>{function a(){let a=1;function b(obj){let value=obj.v;with(obj){value;}return value;}return b({v:a})+a;}return a();})();"
  );
}

#[test]
fn with_in_nested_scope_pins_outer_bindings() {
  let src =
    "(()=>{function outer(){let top=1;function inner(obj){with(obj){top;}return top;}return inner({})+top;}return outer();})();";
  let result = minified(TopLevelMode::Global, src);
  assert_eq!(
    result,
    "(()=>{function a(){let top=1;function a(obj){with(obj){top;}return top;}return a({})+top;}return a();})();"
  );
}

#[test]
fn erases_type_annotations_and_aliases() {
  let src = r#"
    type Alias = { foo: string };
    interface Foo { bar: number }
    const value: number = (foo as any) satisfies Alias ? 1 : 2;
    function wrap<T>(item: T): T { return item; }
  "#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");
  assert_eq!(parsed.stx.body.len(), 2);
  match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(_) | Stmt::Expr(_) => {}
    other => panic!("expected var decl, got {other:?}"),
  }
  match parsed.stx.body[1].stx.as_ref() {
    Stmt::FunctionDecl(_) => {}
    other => panic!("expected function decl, got {other:?}"),
  }
}

#[test]
fn erases_type_parameters_from_functions() {
  let src = "const wrap = <T>(value: T): T => value; const result: string = wrap<string>(\"x\");";
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 2);
}

#[test]
fn drops_this_parameters_from_functions() {
  let src = r#"function f(this: any, x: number) { return x; }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 1);
  let func = match parsed.stx.body[0].stx.as_ref() {
    Stmt::FunctionDecl(func) => func,
    other => panic!("expected function decl, got {other:?}"),
  };
  let params = &func.stx.function.stx.parameters;
  assert_eq!(params.len(), 1);
  match params[0].stx.pattern.stx.pat.stx.as_ref() {
    parse_js::ast::expr::pat::Pat::Id(id) => assert_eq!(id.stx.name, "x"),
    other => panic!("expected identifier param, got {other:?}"),
  };
}

#[test]
fn preserves_tsx_and_jsx_content() {
  let src = r#"
     import type { ReactNode } from "react";
     const element: ReactNode = <div className="x">{value as number}</div>;
  "#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Tsx, Dialect::Jsx, src);
  assert_eq!(parsed.stx.body.len(), 1);
  let initializer = match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => decl
      .stx
      .declarators
      .first()
      .and_then(|decl| decl.initializer.as_ref())
      .expect("initializer should exist"),
    Stmt::Expr(expr) => &expr.stx.expr,
    other => panic!("expected var decl or expr stmt, got {other:?}"),
  };
  let jsx = match initializer.stx.as_ref() {
    Expr::JsxElem(elem) => elem,
    other => panic!("expected JSX element, got {other:?}"),
  };
  let expr_child = jsx
    .stx
    .children
    .iter()
    .find_map(|child| match child {
      JsxElemChild::Expr(expr) => Some(expr),
      _ => None,
    })
    .expect("expected jsx expression child");
  match expr_child.stx.value.stx.as_ref() {
    Expr::Id(_) => {}
    other => panic!("type assertions should be erased from JSX expressions, got {other:?}"),
  }
}

#[test]
fn drops_type_only_imports() {
  let src = r#"
    import type { Foo } from "./types";
    import { type Bar, baz } from "./mod";
    export type { Foo as FooType };
    export const value = baz;
  "#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 2);
  match parsed.stx.body[0].stx.as_ref() {
    Stmt::Import(import) => {
      assert_eq!(import.stx.module, "./mod");
      match import.stx.names.as_ref() {
        Some(ImportNames::Specific(names)) => assert_eq!(names.len(), 1),
        other => panic!("expected single named import, got {other:?}"),
      }
    }
    other => panic!("expected remaining value import, got {other:?}"),
  }
  assert!(matches!(parsed.stx.body[1].stx.as_ref(), Stmt::VarDecl(_)));
}

#[test]
fn preserves_side_effect_imports() {
  let src = r#"import "./side";"#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 1);
  let import = match parsed.stx.body[0].stx.as_ref() {
    Stmt::Import(import) => import,
    other => panic!("expected import statement, got {other:?}"),
  };
  assert_eq!(import.stx.module, "./side");
  assert!(import.stx.default.is_none());
  assert!(import.stx.names.is_none());
}

#[test]
fn preserves_empty_named_imports_for_side_effects() {
  let src = r#"import {} from "./side";"#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 1);
  let import = match parsed.stx.body[0].stx.as_ref() {
    Stmt::Import(import) => import,
    other => panic!("expected import statement, got {other:?}"),
  };
  assert_eq!(import.stx.module, "./side");
  assert!(import.stx.default.is_none());
  match import.stx.names.as_ref() {
    None => {}
    Some(ImportNames::Specific(names)) => assert!(names.is_empty()),
    other => panic!("expected side-effect import with no bindings, got {other:?}"),
  }
}

#[test]
fn does_not_keep_named_imports_that_become_empty_after_stripping_types() {
  let src = r#"import { type Foo } from "./types";"#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert!(
    !parsed
      .stx
      .body
      .iter()
      .any(|stmt| matches!(stmt.stx.as_ref(), Stmt::Import(_))),
    "expected type-only named import to be removed"
  );
}

#[test]
fn preserves_empty_export_from_for_side_effects() {
  let src = r#"export {} from "./side";"#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 1);
  match parsed.stx.body[0].stx.as_ref() {
    Stmt::ExportList(export_stmt) => {
      assert_eq!(export_stmt.stx.from.as_deref(), Some("./side"));
      match &export_stmt.stx.names {
        parse_js::ast::import_export::ExportNames::Specific(names) => assert!(names.is_empty()),
        other => panic!("expected specific export list, got {other:?}"),
      }
    }
    Stmt::Import(import_stmt) => {
      assert_eq!(import_stmt.stx.module, "./side");
      assert!(import_stmt.stx.default.is_none());
      match import_stmt.stx.names.as_ref() {
        None => {}
        Some(ImportNames::Specific(names)) => assert!(names.is_empty()),
        other => panic!("expected side-effect import, got {other:?}"),
      }
    }
    other => panic!("expected export-from or import statement, got {other:?}"),
  }
}

#[test]
fn does_not_keep_type_only_export_from_as_side_effects() {
  let src = r#"export { type Foo } from "./types";"#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert!(
    !parsed.stx.body.iter().any(|stmt| match stmt.stx.as_ref() {
      Stmt::Import(import) => import.stx.module == "./types",
      Stmt::ExportList(export_list) => export_list.stx.from.as_deref() == Some("./types"),
      _ => false,
    }),
    "expected type-only export-from to be removed"
  );
}

#[test]
fn lowers_import_equals_require() {
  let src = r#"
    import foo = require("bar");
  "#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 1);
  let initializer = match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => {
      assert_eq!(decl.stx.mode, VarDeclMode::Const);
      decl
        .stx
        .declarators
        .first()
        .and_then(|declarator| declarator.initializer.as_ref())
        .expect("initializer should exist")
    }
    Stmt::Expr(expr) => &expr.stx.expr,
    other => panic!("expected var decl or expr stmt, got {other:?}"),
  };
  match initializer.stx.as_ref() {
    Expr::Call(call) => match call.stx.callee.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, "require"),
      other => panic!("expected require call, got {other:?}"),
    },
    other => panic!("expected require initializer, got {other:?}"),
  }
}

#[test]
fn lowers_export_assignment_to_module_exports() {
  let src = r#"
    const value = 1;
    export = value;
  "#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 2);
  let export_stmt = parsed.stx.body.last().expect("module.exports assignment");
  let expr_stmt = match export_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let assignment = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  assert_eq!(assignment.stx.operator, OperatorName::Assignment);
  match assignment.stx.left.stx.as_ref() {
    Expr::Member(member) => {
      assert_eq!(member.stx.right, "exports");
      match member.stx.left.stx.as_ref() {
        Expr::Id(id) => assert_eq!(id.stx.name, "module"),
        other => panic!("expected module identifier, got {other:?}"),
      }
    }
    other => panic!("expected module.exports assignment, got {other:?}"),
  }
}

#[test]
fn drops_type_only_import_equals() {
  let src = r#"import type foo = require("bar");"#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert!(parsed.stx.body.is_empty());
}

#[test]
fn lowers_runtime_enums_to_parseable_js() {
  let src = r#"
     export enum Num { A, B = 5, C }
     export enum Str { A = "a", B = `b` }
     export declare enum Gone { A }
   "#;
  let (code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert!(!code.contains("Gone"));
  assert_eq!(parsed.stx.body.len(), 4);

  let first = match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected enum var decl, got {other:?}"),
  };
  assert!(first.stx.export);

  let third = match parsed.stx.body[2].stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected enum var decl, got {other:?}"),
  };
  assert!(third.stx.export);
}

#[test]
fn inlines_const_enums_by_default() {
  let src = r#"const enum E { A = 1, B = A } const x = E.B;"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 1);
  let x_decl = match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected x var decl, got {other:?}"),
  };
  assert_eq!(x_decl.stx.mode, VarDeclMode::Const);
  let initializer = x_decl
    .stx
    .declarators
    .first()
    .and_then(|decl| decl.initializer.as_ref())
    .expect("initializer should exist");
  match initializer.stx.as_ref() {
    Expr::LitNum(num) => assert_eq!(num.stx.value.0, 1.0),
    other => panic!("expected numeric literal initializer, got {other:?}"),
  }
}

#[test]
fn lowers_runtime_namespaces_to_parseable_js() {
  let src = r#"
     export namespace NS {
       export const x: number = 1;
       export function get() { return x; }
      export namespace Inner {
        export const y = 2;
      }
    }
    export declare namespace Gone { export const z: number; }
  "#;
  let (code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert!(!code.contains("Gone"));
  assert_eq!(parsed.stx.body.len(), 2);
  let decl = match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected namespace var decl, got {other:?}"),
  };
  assert!(decl.stx.export);
}

#[test]
fn exports_namespaces_merged_with_existing_classes_without_var_redecls() {
  let src = r#"
    class C {}
    export namespace C { export const x = 1; }
  "#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 3);
  assert!(matches!(
    parsed.stx.body[0].stx.as_ref(),
    Stmt::ClassDecl(_)
  ));
  let export_stmt = match parsed.stx.body[1].stx.as_ref() {
    Stmt::ExportList(stmt) => stmt,
    other => panic!("expected export list statement, got {other:?}"),
  };
  assert!(export_stmt.stx.from.is_none());
  match &export_stmt.stx.names {
    parse_js::ast::import_export::ExportNames::Specific(names) => {
      assert_eq!(names.len(), 1);
      let name = names.first().expect("export name");
      assert_eq!(name.stx.alias.stx.name, "C");
    }
    other => panic!("expected specific exports, got {other:?}"),
  };
  assert!(
    matches!(parsed.stx.body[2].stx.as_ref(), Stmt::Expr(_)),
    "expected namespace IIFE statement"
  );

  let mut found_var_decl = false;
  for stmt in &parsed.stx.body {
    if let Stmt::VarDecl(decl) = stmt.stx.as_ref() {
      for declarator in &decl.stx.declarators {
        if let parse_js::ast::expr::pat::Pat::Id(id) = declarator.pattern.stx.pat.stx.as_ref() {
          if id.stx.name == "C" {
            found_var_decl = true;
          }
        }
      }
    }
  }
  assert!(
    !found_var_decl,
    "should not introduce `var C;` for class-merged namespaces"
  );
}

#[test]
fn lowers_dotted_runtime_namespaces_to_parseable_js() {
  let src = r#"export namespace A.B { export const x = 1; }"#;
  let (code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 2);
  let decl = match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected namespace var decl, got {other:?}"),
  };
  assert!(decl.stx.export);
  assert!(
    code.contains(".B"),
    "dotted namespace lowering should initialize A.B"
  );
}

#[test]
fn lowers_runtime_modules_to_parseable_js() {
  let src = r#"
    module Mod {
      export const x = 1;
    }
  "#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 2);
}

#[test]
fn minifies_ts_enums_and_namespaces_deterministically() {
  let src = r#"
    export enum E { A, B }
    export namespace N { export const x = 1; }
  "#;
  let first = minified(TopLevelMode::Module, src);
  let second = minified(TopLevelMode::Module, src);
  assert_eq!(first, second);
}

#[test]
fn rewrites_enum_member_references_in_initializers() {
  let src = r#"enum E { A = 1, B = A, C }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 2);
  let iife = match parsed.stx.body[1].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected enum IIFE expr stmt, got {other:?}"),
  };
  let call = match iife.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
    other => panic!("expected comma expression, got {other:?}"),
  };
  let func = match call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function callee, got {other:?}"),
  };
  let body = match func.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };
  let b_stmt = body.get(1).expect("B member statement");
  let expr_stmt = match b_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let outer_assign = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  let outer_left = match outer_assign.stx.left.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member assignment, got {other:?}"),
  };
  let name_assign = match outer_left.stx.member.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected inner assignment, got {other:?}"),
  };
  match name_assign.stx.right.stx.as_ref() {
    Expr::ComputedMember(_) => {}
    other => panic!("expected rewritten enum member reference, got {other:?}"),
  }
}

#[test]
fn rewrites_enum_member_references_in_nested_scopes() {
  let src = r#"enum E { A = 1, B = (() => A)(), C = (function(){ return A; })() }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 2);
  let iife = match parsed.stx.body[1].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected enum IIFE expr stmt, got {other:?}"),
  };
  let call = match iife.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
    other => panic!("expected comma expression, got {other:?}"),
  };
  let func = match call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function callee, got {other:?}"),
  };
  let body = match func.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };

  fn get_value_expr<'a>(stmt: &'a Node<Stmt>) -> &'a Node<Expr> {
    let expr_stmt = match stmt.stx.as_ref() {
      Stmt::Expr(expr) => expr,
      other => panic!("expected expression statement, got {other:?}"),
    };
    let outer_assign = match expr_stmt.stx.expr.stx.as_ref() {
      Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
      other => panic!("expected assignment expression, got {other:?}"),
    };
    let outer_left = match outer_assign.stx.left.stx.as_ref() {
      Expr::ComputedMember(member) => member,
      other => panic!("expected computed member assignment, got {other:?}"),
    };
    let name_assign = match outer_left.stx.member.stx.as_ref() {
      Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
      other => panic!("expected inner assignment, got {other:?}"),
    };
    &name_assign.stx.right
  }

  let b_stmt = body.get(1).expect("B member statement");
  let b_value = get_value_expr(b_stmt);
  let b_call = match b_value.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for B initializer, got {other:?}"),
  };
  let b_arrow = match b_call.stx.callee.stx.as_ref() {
    Expr::ArrowFunc(arrow) => arrow,
    other => panic!("expected arrow function callee, got {other:?}"),
  };
  let b_arrow_body = match b_arrow.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Expression(expr)) => expr,
    other => panic!("expected arrow expression body, got {other:?}"),
  };
  assert!(
    matches!(b_arrow_body.stx.as_ref(), Expr::ComputedMember(_)),
    "expected A in arrow initializer to rewrite to E[\"A\"]"
  );

  let c_stmt = body.get(2).expect("C member statement");
  let c_value = get_value_expr(c_stmt);
  let c_call = match c_value.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for C initializer, got {other:?}"),
  };
  let c_func = match c_call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function expression callee, got {other:?}"),
  };
  let c_body = match c_func.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };
  let ret = c_body.iter().find_map(|stmt| match stmt.stx.as_ref() {
    Stmt::Return(ret) => ret.stx.value.as_ref(),
    _ => None,
  });
  let ret = ret.expect("expected return statement in function initializer");
  assert!(
    matches!(ret.stx.as_ref(), Expr::ComputedMember(_)),
    "expected A in function initializer to rewrite to E[\"A\"]"
  );
}

#[test]
fn rewrites_enum_member_references_in_jsx_expression_containers() {
  let src = r#"enum E { A = 1, B = (() => <div data-x={A}>{A}</div>)(), C }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Tsx,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 2);
  let iife = match parsed.stx.body[1].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected enum IIFE expr stmt, got {other:?}"),
  };
  let call = match iife.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
    other => panic!("expected comma expression, got {other:?}"),
  };
  let func = match call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function callee, got {other:?}"),
  };
  let body = match func.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };

  fn get_value_expr<'a>(stmt: &'a Node<Stmt>) -> &'a Node<Expr> {
    let expr_stmt = match stmt.stx.as_ref() {
      Stmt::Expr(expr) => expr,
      other => panic!("expected expression statement, got {other:?}"),
    };
    let outer_assign = match expr_stmt.stx.expr.stx.as_ref() {
      Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
      other => panic!("expected assignment expression, got {other:?}"),
    };
    let outer_left = match outer_assign.stx.left.stx.as_ref() {
      Expr::ComputedMember(member) => member,
      other => panic!("expected computed member assignment, got {other:?}"),
    };
    let name_assign = match outer_left.stx.member.stx.as_ref() {
      Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
      other => panic!("expected inner assignment, got {other:?}"),
    };
    &name_assign.stx.right
  }

  let b_stmt = body.get(1).expect("B member statement");
  let b_value = get_value_expr(b_stmt);
  let b_call = match b_value.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for B initializer, got {other:?}"),
  };
  let b_arrow = match b_call.stx.callee.stx.as_ref() {
    Expr::ArrowFunc(arrow) => arrow,
    other => panic!("expected arrow function callee, got {other:?}"),
  };
  let b_arrow_body = match b_arrow.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Expression(expr)) => expr,
    other => panic!("expected arrow expression body, got {other:?}"),
  };
  let jsx = match b_arrow_body.stx.as_ref() {
    Expr::JsxElem(elem) => elem,
    other => panic!("expected JSX element, got {other:?}"),
  };

  let attr = jsx.stx.attributes.first().expect("JSX attribute");
  let attr_expr = match attr {
    JsxAttr::Named {
      value: Some(JsxAttrVal::Expression(expr)),
      ..
    } => expr,
    other => panic!("expected JSX expression attribute, got {other:?}"),
  };
  let computed = match attr_expr.stx.value.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected rewritten enum member ref in JSX attribute, got {other:?}"),
  };
  match computed.stx.object.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "E"),
    other => panic!("expected enum identifier, got {other:?}"),
  };
  match computed.stx.member.stx.as_ref() {
    Expr::LitStr(key) => assert_eq!(key.stx.value, "A"),
    other => panic!("expected string literal member, got {other:?}"),
  };

  let child_expr = jsx
    .stx
    .children
    .iter()
    .find_map(|child| match child {
      JsxElemChild::Expr(expr) => Some(expr),
      _ => None,
    })
    .expect("JSX expression child");
  let computed = match child_expr.stx.value.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected rewritten enum member ref in JSX child, got {other:?}"),
  };
  match computed.stx.object.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "E"),
    other => panic!("expected enum identifier, got {other:?}"),
  };
  match computed.stx.member.stx.as_ref() {
    Expr::LitStr(key) => assert_eq!(key.stx.value, "A"),
    other => panic!("expected string literal member, got {other:?}"),
  };
}

#[test]
fn rewrites_enum_member_references_in_jsx_element_names() {
  let src = r#"enum E { A = 1, B = (() => <A />)(), C }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Tsx,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 2);
  let iife = match parsed.stx.body[1].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected enum IIFE expr stmt, got {other:?}"),
  };
  let call = match iife.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
    other => panic!("expected comma expression, got {other:?}"),
  };
  let func = match call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function callee, got {other:?}"),
  };
  let body = match func.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };

  fn get_value_expr<'a>(stmt: &'a Node<Stmt>) -> &'a Node<Expr> {
    let expr_stmt = match stmt.stx.as_ref() {
      Stmt::Expr(expr) => expr,
      other => panic!("expected expression statement, got {other:?}"),
    };
    let outer_assign = match expr_stmt.stx.expr.stx.as_ref() {
      Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
      other => panic!("expected assignment expression, got {other:?}"),
    };
    let outer_left = match outer_assign.stx.left.stx.as_ref() {
      Expr::ComputedMember(member) => member,
      other => panic!("expected computed member assignment, got {other:?}"),
    };
    let name_assign = match outer_left.stx.member.stx.as_ref() {
      Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
      other => panic!("expected inner assignment, got {other:?}"),
    };
    &name_assign.stx.right
  }

  let b_stmt = body.get(1).expect("B member statement");
  let b_value = get_value_expr(b_stmt);
  let b_call = match b_value.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for B initializer, got {other:?}"),
  };
  let b_arrow = match b_call.stx.callee.stx.as_ref() {
    Expr::ArrowFunc(arrow) => arrow,
    other => panic!("expected arrow function callee, got {other:?}"),
  };
  let b_arrow_body = match b_arrow.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Expression(expr)) => expr,
    other => panic!("expected arrow expression body, got {other:?}"),
  };
  let jsx = match b_arrow_body.stx.as_ref() {
    Expr::JsxElem(elem) => elem,
    other => panic!("expected JSX element, got {other:?}"),
  };
  let name = jsx.stx.name.as_ref().expect("JSX element name");
  let member = match name {
    JsxElemName::Member(member) => member,
    other => panic!("expected rewritten JSX member element name, got {other:?}"),
  };
  assert_eq!(member.stx.base.stx.name, "E");
  assert_eq!(member.stx.path, vec!["A".to_string()]);
}

#[test]
fn rewrites_enum_member_references_in_jsx_element_names_using_alias_when_enum_name_shadowed() {
  let src = r#"enum E { A = 1, B = ((E) => <A />)(0) }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Tsx,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 2);
  let iife = match parsed.stx.body[1].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected enum IIFE expr stmt, got {other:?}"),
  };
  let call = match iife.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
    other => panic!("expected comma expression, got {other:?}"),
  };
  let func = match call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function callee, got {other:?}"),
  };
  let body = match func.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };

  assert_eq!(body.len(), 3);
  let alias_stmt = body.first().expect("enum alias var decl statement");
  let alias_decl = match alias_stmt.stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected enum alias var decl, got {other:?}"),
  };
  let alias_declarator = alias_decl
    .stx
    .declarators
    .first()
    .expect("alias declarator");
  match alias_declarator.pattern.stx.pat.stx.as_ref() {
    parse_js::ast::expr::pat::Pat::Id(id) => assert_eq!(id.stx.name, "__minify_ts_enum_E"),
    other => panic!("expected identifier pattern, got {other:?}"),
  };

  let b_stmt = body.get(2).expect("B member statement");
  let expr_stmt = match b_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let outer_assign = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  let outer_left = match outer_assign.stx.left.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member assignment, got {other:?}"),
  };
  let name_assign = match outer_left.stx.member.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected inner assignment, got {other:?}"),
  };
  let value_expr = &name_assign.stx.right;
  let call = match value_expr.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for B initializer, got {other:?}"),
  };
  let arrow = match call.stx.callee.stx.as_ref() {
    Expr::ArrowFunc(arrow) => arrow,
    other => panic!("expected arrow function callee, got {other:?}"),
  };
  let arrow_body = match arrow.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Expression(expr)) => expr,
    other => panic!("expected arrow expression body, got {other:?}"),
  };
  let jsx = match arrow_body.stx.as_ref() {
    Expr::JsxElem(elem) => elem,
    other => panic!("expected JSX element, got {other:?}"),
  };
  let name = jsx.stx.name.as_ref().expect("JSX element name");
  let member = match name {
    JsxElemName::Member(member) => member,
    other => panic!("expected rewritten JSX member element name, got {other:?}"),
  };
  assert_eq!(member.stx.base.stx.name, "__minify_ts_enum_E");
  assert_eq!(member.stx.path, vec!["A".to_string()]);
}

#[test]
fn does_not_rewrite_shadowed_enum_member_references() {
  let src = r#"enum E { A = 1, B = ((A) => A)(2) }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 2);
  let iife = match parsed.stx.body[1].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected enum IIFE expr stmt, got {other:?}"),
  };
  let call = match iife.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
    other => panic!("expected comma expression, got {other:?}"),
  };
  let func = match call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function callee, got {other:?}"),
  };
  let body = match func.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };

  let b_stmt = body.get(1).expect("B member statement");
  let expr_stmt = match b_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let outer_assign = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  let outer_left = match outer_assign.stx.left.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member assignment, got {other:?}"),
  };
  let name_assign = match outer_left.stx.member.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected inner assignment, got {other:?}"),
  };
  let value_expr = &name_assign.stx.right;
  let call = match value_expr.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for B initializer, got {other:?}"),
  };
  let arrow = match call.stx.callee.stx.as_ref() {
    Expr::ArrowFunc(arrow) => arrow,
    other => panic!("expected arrow function callee, got {other:?}"),
  };
  let arrow_body = match arrow.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Expression(expr)) => expr,
    other => panic!("expected arrow expression body, got {other:?}"),
  };
  assert!(
    matches!(arrow_body.stx.as_ref(), Expr::Id(_)),
    "shadowed A in arrow initializer should remain an identifier"
  );
}

#[test]
fn rewrites_enum_member_references_using_alias_when_enum_name_shadowed() {
  let src = r#"enum E { A = 1, B = ((E) => A)(0) }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 2);
  let iife = match parsed.stx.body[1].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected enum IIFE expr stmt, got {other:?}"),
  };
  let call = match iife.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
    other => panic!("expected comma expression, got {other:?}"),
  };
  let func = match call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function callee, got {other:?}"),
  };
  let body = match func.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };

  assert_eq!(body.len(), 3);
  let alias_stmt = body.first().expect("enum alias var decl statement");
  let alias_decl = match alias_stmt.stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected enum alias var decl, got {other:?}"),
  };
  assert_eq!(alias_decl.stx.mode, VarDeclMode::Var);
  let alias_declarator = alias_decl
    .stx
    .declarators
    .first()
    .expect("alias declarator");
  match alias_declarator.pattern.stx.pat.stx.as_ref() {
    parse_js::ast::expr::pat::Pat::Id(id) => assert_eq!(id.stx.name, "__minify_ts_enum_E"),
    other => panic!("expected identifier pattern, got {other:?}"),
  };
  let alias_init = alias_declarator
    .initializer
    .as_ref()
    .expect("alias initializer");
  match alias_init.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "E"),
    other => panic!("expected initializer identifier, got {other:?}"),
  };

  let b_stmt = body.get(2).expect("B member statement");
  let expr_stmt = match b_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let outer_assign = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  let outer_left = match outer_assign.stx.left.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member assignment, got {other:?}"),
  };
  let name_assign = match outer_left.stx.member.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected inner assignment, got {other:?}"),
  };
  let value_expr = &name_assign.stx.right;
  let call = match value_expr.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for B initializer, got {other:?}"),
  };
  let arrow = match call.stx.callee.stx.as_ref() {
    Expr::ArrowFunc(arrow) => arrow,
    other => panic!("expected arrow function callee, got {other:?}"),
  };
  let arrow_body = match arrow.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Expression(expr)) => expr,
    other => panic!("expected arrow expression body, got {other:?}"),
  };
  let computed = match arrow_body.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member access, got {other:?}"),
  };
  match computed.stx.object.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "__minify_ts_enum_E"),
    other => panic!("expected enum alias identifier, got {other:?}"),
  };
  match computed.stx.member.stx.as_ref() {
    Expr::LitStr(key) => assert_eq!(key.stx.value, "A"),
    other => panic!("expected string literal member, got {other:?}"),
  };
}

#[test]
fn rewrites_enum_member_references_in_object_shorthand() {
  let src = r#"enum E { A = 1, B = (() => ({ A }))() }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 2);
  let iife = match parsed.stx.body[1].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected enum IIFE expr stmt, got {other:?}"),
  };
  let call = match iife.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
    other => panic!("expected comma expression, got {other:?}"),
  };
  let func = match call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function callee, got {other:?}"),
  };
  let body = match func.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };

  let b_stmt = body.get(1).expect("B member statement");
  let expr_stmt = match b_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let outer_assign = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  let outer_left = match outer_assign.stx.left.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member assignment, got {other:?}"),
  };
  let name_assign = match outer_left.stx.member.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected inner assignment, got {other:?}"),
  };
  let value_expr = &name_assign.stx.right;
  let call = match value_expr.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for B initializer, got {other:?}"),
  };
  let arrow = match call.stx.callee.stx.as_ref() {
    Expr::ArrowFunc(arrow) => arrow,
    other => panic!("expected arrow function callee, got {other:?}"),
  };
  let arrow_body = match arrow.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Expression(expr)) => expr,
    other => panic!("expected arrow expression body, got {other:?}"),
  };
  let obj = match arrow_body.stx.as_ref() {
    Expr::LitObj(obj) => obj,
    other => panic!("expected object literal, got {other:?}"),
  };
  let member = obj.stx.members.first().expect("object member");
  let (key, value) = match &member.stx.typ {
    ObjMemberType::Valued { key, val } => (key, val),
    other => panic!("expected valued member, got {other:?}"),
  };
  match key {
    ClassOrObjKey::Direct(name) => assert_eq!(name.stx.key, "A"),
    other => panic!("expected direct key, got {other:?}"),
  };
  let value = match value {
    ClassOrObjVal::Prop(Some(expr)) => expr,
    other => panic!("expected property value expression, got {other:?}"),
  };
  let computed = match value.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member access, got {other:?}"),
  };
  match computed.stx.object.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "E"),
    other => panic!("expected enum identifier, got {other:?}"),
  };
  match computed.stx.member.stx.as_ref() {
    Expr::LitStr(key) => assert_eq!(key.stx.value, "A"),
    other => panic!("expected string literal member, got {other:?}"),
  };
}

#[test]
fn does_not_rewrite_shadowed_enum_member_references_in_object_shorthand() {
  let src = r#"enum E { A = 1, B = ((A) => ({ A }))(2) }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 2);
  let iife = match parsed.stx.body[1].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected enum IIFE expr stmt, got {other:?}"),
  };
  let call = match iife.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
    other => panic!("expected comma expression, got {other:?}"),
  };
  let func = match call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function callee, got {other:?}"),
  };
  let body = match func.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };

  let b_stmt = body.get(1).expect("B member statement");
  let expr_stmt = match b_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let outer_assign = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  let outer_left = match outer_assign.stx.left.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member assignment, got {other:?}"),
  };
  let name_assign = match outer_left.stx.member.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected inner assignment, got {other:?}"),
  };
  let value_expr = &name_assign.stx.right;
  let call = match value_expr.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for B initializer, got {other:?}"),
  };
  let arrow = match call.stx.callee.stx.as_ref() {
    Expr::ArrowFunc(arrow) => arrow,
    other => panic!("expected arrow function callee, got {other:?}"),
  };
  let arrow_body = match arrow.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Expression(expr)) => expr,
    other => panic!("expected arrow expression body, got {other:?}"),
  };
  let obj = match arrow_body.stx.as_ref() {
    Expr::LitObj(obj) => obj,
    other => panic!("expected object literal, got {other:?}"),
  };
  let member = obj.stx.members.first().expect("object member");
  match &member.stx.typ {
    ObjMemberType::Shorthand { id } => assert_eq!(id.stx.name, "A"),
    other => panic!("expected shorthand member, got {other:?}"),
  };
}

#[test]
fn lowers_parameter_properties_in_constructors() {
  let src = r#"class C { constructor(public x: number, readonly y: string) {} }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  let class_decl = match parsed.stx.body.first().map(|stmt| stmt.stx.as_ref()) {
    Some(Stmt::ClassDecl(decl)) => decl,
    other => panic!("expected class decl, got {other:?}"),
  };
  let ctor = class_decl
    .stx
    .members
    .iter()
    .find(|member| match &member.stx.key {
      ClassOrObjKey::Direct(key) => key.stx.key == "constructor",
      _ => false,
    })
    .expect("constructor member");
  let method = match &ctor.stx.val {
    ClassOrObjVal::Method(method) => method,
    other => panic!("expected constructor method, got {other:?}"),
  };
  let body = match method.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected constructor body block, got {other:?}"),
  };

  fn assert_this_property_assignment(stmt: &Node<Stmt>, name: &str) {
    let expr_stmt = match stmt.stx.as_ref() {
      Stmt::Expr(expr) => expr,
      other => panic!("expected expression statement, got {other:?}"),
    };
    let assign = match expr_stmt.stx.expr.stx.as_ref() {
      Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
      other => panic!("expected assignment expression, got {other:?}"),
    };
    let left = match assign.stx.left.stx.as_ref() {
      Expr::ComputedMember(member) => member,
      other => panic!("expected computed member assignment, got {other:?}"),
    };
    assert!(
      matches!(left.stx.object.stx.as_ref(), Expr::This(_)),
      "expected this[...] on assignment LHS"
    );
    match left.stx.member.stx.as_ref() {
      Expr::LitStr(key) => assert_eq!(key.stx.value, name),
      other => panic!("expected string member, got {other:?}"),
    };
    match assign.stx.right.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, name),
      other => panic!("expected identifier RHS, got {other:?}"),
    };
  }

  assert_eq!(body.len(), 2);
  assert_this_property_assignment(&body[0], "x");
  assert_this_property_assignment(&body[1], "y");
}

#[test]
fn lowers_parameter_properties_after_super_in_derived_constructors() {
  let src = r#"
    class Base { constructor(x: number) {} }
    class Derived extends Base {
      constructor(public x: number) {
        console.log(x);
        super(x);
      }
    }
  "#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert!(parsed.stx.body.len() >= 2);
  let derived = match parsed.stx.body.get(1).map(|stmt| stmt.stx.as_ref()) {
    Some(Stmt::ClassDecl(decl)) => decl,
    other => panic!("expected derived class decl, got {other:?}"),
  };
  let ctor = derived
    .stx
    .members
    .iter()
    .find(|member| match &member.stx.key {
      ClassOrObjKey::Direct(key) => key.stx.key == "constructor",
      _ => false,
    })
    .expect("constructor member");
  let method = match &ctor.stx.val {
    ClassOrObjVal::Method(method) => method,
    other => panic!("expected constructor method, got {other:?}"),
  };
  let body = match method.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected constructor body block, got {other:?}"),
  };

  assert_eq!(body.len(), 3);
  let super_stmt = body.get(1).expect("super call statement");
  let expr_stmt = match super_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let call = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected super call, got {other:?}"),
  };
  assert!(
    matches!(call.stx.callee.stx.as_ref(), Expr::Super(_)),
    "expected super(...) call"
  );

  let assign_stmt = body.get(2).expect("parameter property assignment");
  let expr_stmt = match assign_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let assign = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  let left = match assign.stx.left.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member assignment, got {other:?}"),
  };
  assert!(
    matches!(left.stx.object.stx.as_ref(), Expr::This(_)),
    "expected this[...] on assignment LHS"
  );
  match left.stx.member.stx.as_ref() {
    Expr::LitStr(key) => assert_eq!(key.stx.value, "x"),
    other => panic!("expected string member, got {other:?}"),
  };
  match assign.stx.right.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "x"),
    other => panic!("expected identifier RHS, got {other:?}"),
  };
}

#[test]
fn lowers_parameter_properties_after_var_super_in_derived_constructors() {
  let src = r#"
    class Base { constructor(x: number) {} }
    class Derived extends Base {
      constructor(public x: number) {
        const self = super(x);
      }
    }
  "#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  let derived = match parsed.stx.body.get(1).map(|stmt| stmt.stx.as_ref()) {
    Some(Stmt::ClassDecl(decl)) => decl,
    other => panic!("expected derived class decl, got {other:?}"),
  };
  let ctor = derived
    .stx
    .members
    .iter()
    .find(|member| match &member.stx.key {
      ClassOrObjKey::Direct(key) => key.stx.key == "constructor",
      _ => false,
    })
    .expect("constructor member");
  let method = match &ctor.stx.val {
    ClassOrObjVal::Method(method) => method,
    other => panic!("expected constructor method, got {other:?}"),
  };
  let body = match method.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected constructor body block, got {other:?}"),
  };

  assert_eq!(body.len(), 2);
  assert!(
    matches!(body[0].stx.as_ref(), Stmt::VarDecl(_)),
    "expected first statement to be a var decl containing super(...)"
  );
  let assign_stmt = body.get(1).expect("parameter property assignment");
  let expr_stmt = match assign_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let assign = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  let left = match assign.stx.left.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member assignment, got {other:?}"),
  };
  assert!(
    matches!(left.stx.object.stx.as_ref(), Expr::This(_)),
    "expected this[...] on assignment LHS"
  );
}

#[test]
fn rewrites_return_super_before_inserting_parameter_properties() {
  let src = r#"
    class Base { constructor(x: number) {} }
    class Derived extends Base {
      constructor(public x: number) {
        return super(x);
      }
    }
  "#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  let derived = match parsed.stx.body.get(1).map(|stmt| stmt.stx.as_ref()) {
    Some(Stmt::ClassDecl(decl)) => decl,
    other => panic!("expected derived class decl, got {other:?}"),
  };
  let ctor = derived
    .stx
    .members
    .iter()
    .find(|member| match &member.stx.key {
      ClassOrObjKey::Direct(key) => key.stx.key == "constructor",
      _ => false,
    })
    .expect("constructor member");
  let method = match &ctor.stx.val {
    ClassOrObjVal::Method(method) => method,
    other => panic!("expected constructor method, got {other:?}"),
  };
  let body = match method.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected constructor body block, got {other:?}"),
  };

  assert_eq!(body.len(), 3);
  let super_stmt = body.first().expect("super call statement");
  let expr_stmt = match super_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let call = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected super call, got {other:?}"),
  };
  assert!(
    matches!(call.stx.callee.stx.as_ref(), Expr::Super(_)),
    "expected super(...) call"
  );

  let assign_stmt = body.get(1).expect("parameter property assignment");
  let expr_stmt = match assign_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let assign = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  assert!(
    matches!(assign.stx.left.stx.as_ref(), Expr::ComputedMember(_)),
    "expected this[...] assignment"
  );

  let ret_stmt = body.get(2).expect("return this statement");
  let ret = match ret_stmt.stx.as_ref() {
    Stmt::Return(ret) => ret,
    other => panic!("expected return statement, got {other:?}"),
  };
  let value = ret.stx.value.as_ref().expect("return value should exist");
  assert!(
    matches!(value.stx.as_ref(), Expr::This(_)),
    "expected `return this;`"
  );
}

#[test]
fn constructor_parameter_properties_preserve_directive_prologue() {
  let src = r#"class C { constructor(public x: number) { "use strict"; } }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  let class_decl = match parsed.stx.body.first().map(|stmt| stmt.stx.as_ref()) {
    Some(Stmt::ClassDecl(decl)) => decl,
    other => panic!("expected class decl, got {other:?}"),
  };
  let ctor = class_decl
    .stx
    .members
    .iter()
    .find(|member| match &member.stx.key {
      ClassOrObjKey::Direct(key) => key.stx.key == "constructor",
      _ => false,
    })
    .expect("constructor member");
  let method = match &ctor.stx.val {
    ClassOrObjVal::Method(method) => method,
    other => panic!("expected constructor method, got {other:?}"),
  };
  let body = match method.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected constructor body block, got {other:?}"),
  };
  assert_eq!(body.len(), 2);

  let directive = match body[0].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  match directive.stx.expr.stx.as_ref() {
    Expr::LitStr(lit) => assert_eq!(lit.stx.value, "use strict"),
    other => panic!("expected string literal directive, got {other:?}"),
  };

  let assign = match body[1].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let assign = match assign.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  match assign.stx.left.stx.as_ref() {
    Expr::ComputedMember(member) => {
      assert!(matches!(member.stx.object.stx.as_ref(), Expr::This(_)));
      assert!(matches!(member.stx.member.stx.as_ref(), Expr::LitStr(_)));
    }
    other => panic!("expected computed member assignment, got {other:?}"),
  };
}

#[test]
fn lowers_class_fields_with_define_for_class_fields_semantics() {
  let src = r#"
    class C {
      foo = 1;
    }
    new C();
  "#;
  let mode = TopLevelMode::Global;

  let emit = |use_define_for_class_fields: bool| -> (String, Node<TopLevel>) {
    let mut out = Vec::new();
    minify_with_options(
      MinifyOptions::new(mode).with_ts_erase_options(TsEraseOptions {
        lower_class_fields: true,
        use_define_for_class_fields,
        ..TsEraseOptions::default()
      }),
      src,
      &mut out,
    )
    .unwrap();
    let output = String::from_utf8(out).unwrap();
    let parsed = parse_with_options(
      &output,
      ParseOptions {
        dialect: Dialect::Js,
        source_type: SourceType::Script,
      },
    )
    .expect("output should parse as JavaScript");
    (output, parsed)
  };

  let (define_output, define_parsed) = emit(true);
  let (assign_output, assign_parsed) = emit(false);
  assert_ne!(define_output, assign_output);

  fn ctor_body(top_level: &Node<TopLevel>) -> &Vec<Node<Stmt>> {
    let class_decl = match top_level.stx.body.first().map(|stmt| stmt.stx.as_ref()) {
      Some(Stmt::ClassDecl(decl)) => decl,
      other => panic!("expected class decl, got {other:?}"),
    };
    let ctor = class_decl
      .stx
      .members
      .iter()
      .find(|member| match &member.stx.key {
        ClassOrObjKey::Direct(key) => key.stx.key == "constructor",
        _ => false,
      })
      .expect("constructor member");
    let method = match &ctor.stx.val {
      ClassOrObjVal::Method(method) => method,
      other => panic!("expected constructor method, got {other:?}"),
    };
    match method.stx.func.stx.body.as_ref() {
      Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
      other => panic!("expected constructor body block, got {other:?}"),
    }
  }

  let define_body = ctor_body(&define_parsed);
  let assign_body = ctor_body(&assign_parsed);

  let define_stmt = define_body.first().expect("define mode constructor stmt");
  match define_stmt.stx.as_ref() {
    Stmt::Expr(expr) => match expr.stx.expr.stx.as_ref() {
      Expr::Call(call) => match call.stx.callee.stx.as_ref() {
        Expr::Member(member) => {
          assert!(matches!(member.stx.left.stx.as_ref(), Expr::Id(id) if id.stx.name == "Object"));
          assert_eq!(member.stx.right, "defineProperty");
        }
        other => panic!("expected Object.defineProperty callee, got {other:?}"),
      },
      other => panic!("expected call expression, got {other:?}"),
    },
    other => panic!("expected expression statement, got {other:?}"),
  }

  let assign_stmt = assign_body.first().expect("assign mode constructor stmt");
  match assign_stmt.stx.as_ref() {
    Stmt::Expr(expr) => match expr.stx.expr.stx.as_ref() {
      Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => {
        let Expr::Member(member) = bin.stx.left.stx.as_ref() else {
          panic!("expected this.foo=... assignment, got {:?}", bin.stx.left);
        };
        assert!(matches!(member.stx.left.stx.as_ref(), Expr::This(_)));
        assert_eq!(member.stx.right, "foo");
      }
      other => panic!("expected assignment expression, got {other:?}"),
    },
    other => panic!("expected expression statement, got {other:?}"),
  }
}

#[test]
fn drops_method_signatures_in_abstract_classes() {
  let src = r#"
    abstract class C {
      foo(): void;
      bar() {}
    }
  "#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 1);
  let class_decl = match parsed.stx.body[0].stx.as_ref() {
    Stmt::ClassDecl(decl) => decl,
    other => panic!("expected class decl, got {other:?}"),
  };
  assert!(!class_decl.stx.abstract_);
  assert_eq!(class_decl.stx.members.len(), 1);
  let member = class_decl.stx.members.first().expect("class member");
  match &member.stx.key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "bar"),
    other => panic!("expected direct class member key, got {other:?}"),
  };
}

#[test]
fn erases_class_auto_accessors_to_parseable_js() {
  let src = r#"class Foo { protected override accessor bar!: number; }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");
  assert_eq!(parsed.stx.body.len(), 1);

  let class_decl = match parsed.stx.body[0].stx.as_ref() {
    Stmt::ClassDecl(decl) => decl,
    other => panic!("expected class decl, got {other:?}"),
  };
  assert_eq!(class_decl.stx.members.len(), 1);
  let member = class_decl
    .stx
    .members
    .first()
    .expect("class member")
    .stx
    .as_ref();

  match &member.key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "bar"),
    other => panic!("expected direct class member key, got {other:?}"),
  };
  assert!(
    !member.accessor,
    "expected TS auto-accessor modifier to be erased in JS output"
  );
  assert!(member.accessibility.is_none());
  assert!(!member.override_);
  assert!(!member.readonly);
  assert!(!member.optional);
  assert!(!member.definite_assignment);
  assert!(member.type_annotation.is_none());
  match &member.val {
    ClassOrObjVal::Prop(None) => {}
    other => panic!("expected erased accessor to be a property, got {other:?}"),
  }
}

#[test]
fn string_enum_aliases_do_not_emit_reverse_mappings() {
  let src = r#"enum S { A = "a", B = A }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 2);
  let iife = match parsed.stx.body[1].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected enum IIFE expr stmt, got {other:?}"),
  };
  let call = match iife.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
    other => panic!("expected comma expression, got {other:?}"),
  };
  let func = match call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function callee, got {other:?}"),
  };
  let body = match func.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };
  let b_stmt = body.get(1).expect("B member statement");
  let expr_stmt = match b_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let assign = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  let left = match assign.stx.left.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member assignment, got {other:?}"),
  };
  assert!(matches!(left.stx.member.stx.as_ref(), Expr::LitStr(_)));
  assert!(matches!(
    assign.stx.right.stx.as_ref(),
    Expr::ComputedMember(_)
  ));
}
