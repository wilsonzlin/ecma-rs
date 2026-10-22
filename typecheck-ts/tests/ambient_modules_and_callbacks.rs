//! `declare module "name"` (string-literal name) is an ambient *external
//! module* declaration: its body is a separate module scope whose
//! declarations never merge with the enclosing globals
//! (`ambientDeclarations.ts`).
//! And JSDoc `@callback Name` declares a function type: its `@param` /
//! `@returns` belong to the callback's signature (never validated against the
//! host function), and `@type {Name}` resolves to it
//! (`callbackOnConstructor.js`).

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes_ts(src: &str) -> Vec<String> {
  let mut host = MemoryHost::default();
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  out.sort();
  out
}

fn codes_js(src: &str) -> Vec<String> {
  let mut options = CompilerOptions::default();
  options.check_js = Some(true);
  let mut host = MemoryHost::with_options(options);
  let file = FileKey::new("t.js");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  out.sort();
  out
}

#[test]
fn ambient_external_module_scope_is_separate() {
  let src = "var q = 1;\ndeclare module 'external1' {\n    var q;\n}\n";
  assert!(codes_ts(src).is_empty());
}

#[test]
fn ambient_module_and_namespace_coexist() {
  let src = "declare namespace M1 {\n    function fn(): number;\n}\nvar q = M1.fn();\ndeclare module 'external1' {\n    var q;\n}\n";
  assert!(codes_ts(src).is_empty());
}

#[test]
fn jsdoc_callback_params_are_not_host_params() {
  let src = "export class Preferences {\n  assignability = \"no\"\n  /**\n   * @callback ValueGetter_2\n   * @param {string} name\n   * @returns {boolean|number|string|undefined}\n   */\n  constructor() {}\n}\n\n/** @type {ValueGetter_2} */\nvar ooscope2 = s => s.length > 0\n";
  assert!(codes_js(src).is_empty());
}

#[test]
fn jsdoc_callback_nested_params_fold_into_root_shape() {
  // `callbackTagNestedParameter.ts`: nested `@param person.prop` tags refine
  // the declared objectish root's shape — they are not separate parameters.
  let src = "/**\n * @callback WorksWithPeopleCallback\n * @param {Object} person\n * @param {string} person.name\n * @param {number} [person.age]\n * @returns {void}\n */\n\n/**\n * @param {WorksWithPeopleCallback} callback\n * @returns {void}\n */\nfunction eachPerson(callback) {\n    callback({ name: \"Empty\" });\n}\n";
  assert!(codes_js(src).is_empty());
}

#[test]
fn jsdoc_callback_nested_params_check_shape_and_arity() {
  // Same callback: the root is one parameter typed by the folded shape, so
  // missing/extra props and arity errors all surface (tsc parity).
  let src = "/**\n * @callback Cb\n * @param {Object} person\n * @param {string} person.name\n * @param {number} [person.age]\n * @returns {void}\n */\n/** @param {Cb} callback @returns {void} */\nfunction use(callback) {\n    callback({});\n    callback({ name: \"E\", extra: 1 });\n    callback({ name: 42 });\n    callback({ name: \"E\" }, 2);\n}\n";
  assert_eq!(
    codes_js(src),
    vec!["TS2322", "TS2345", "TS2353", "TS2554"],
  );
}

#[test]
fn jsdoc_callback_unabsorbed_qualified_params_stay_positional() {
  // Without a declared objectish root, qualified `@param opts.name` tags are
  // ordinary positional parameters (tsc expects 4 arguments here).
  let src = "/**\n * @callback Cb2\n * @param {string} first\n * @param {string} opts.name\n * @param {number} opts.count\n * @param {boolean} last\n * @returns {void}\n */\n/** @param {Cb2} cb @returns {void} */\nfunction use2(cb) {\n  cb(\"a\", { name: \"x\", count: 1 }, true);\n}\n";
  assert_eq!(codes_js(src), vec!["TS2554"]);
}
