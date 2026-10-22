//! Private-identifier incompatible modifiers:
//! TS18010 / TS18019 / TS1024 / TS1031 / TS1042.
//! Mirrors conformance `privateNamesIncompatibleModifiers{,Js}`.

use typecheck_ts::lib_support::{CompilerOptions, ScriptTarget};
use typecheck_ts::{FileKey, MemoryHost, Program};

fn diags(opts: CompilerOptions, name: &str, src: &str) -> Vec<(String, u32, u32, String)> {
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new(name);
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| {
      (
        d.code.as_str().to_string(),
        d.primary.range.start,
        d.primary.range.end,
        d.message.clone(),
      )
    })
    .collect();
  out.sort();
  out
}

fn es2015() -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2015;
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  // These tests exercise JS semantic checking (tsc `--checkJs`).
  opts.check_js = Some(true);
  opts
}

#[test]
fn accessibility_on_private_field_is_ts18010() {
  let src = "class A {\n  public #foo = 3;\n}\n";
  let d = diags(es2015(), "t.ts", src);
  let hits: Vec<_> = d.iter().filter(|(c, _, _, _)| c == "TS18010").collect();
  assert_eq!(hits.len(), 1, "{d:?}");
  let slice = &src[hits[0].1 as usize..hits[0].2 as usize];
  assert_eq!(slice, "public", "span should be the modifier: {hits:?}");
}

#[test]
fn declare_on_private_field_is_ts18019() {
  let src = "class A {\n  declare #what: number;\n}\n";
  let d = diags(es2015(), "t.ts", src);
  assert!(
    d.iter().any(|(c, _, _, _)| c == "TS18019"),
    "expected TS18019: {d:?}"
  );
  assert!(
    !d.iter().any(|(c, _, _, _)| c == "TS2564"),
    "declare fields are SPI-exempt: {d:?}"
  );
}

#[test]
fn readonly_on_private_method_is_ts1024() {
  let src = "class A {\n  readonly #m() { return 1; }\n}\n";
  let d = diags(es2015(), "t.ts", src);
  assert!(
    d.iter().any(|(c, _, _, _)| c == "TS1024"),
    "expected TS1024: {d:?}"
  );
}

#[test]
fn async_on_private_getter_is_ts1042() {
  let src = "class A {\n  async get #p() { return 1; }\n}\n";
  let d = diags(es2015(), "t.ts", src);
  assert!(
    d.iter().any(|(c, _, _, _)| c == "TS1042"),
    "expected TS1042: {d:?}"
  );
}

#[test]
fn jsdoc_public_on_private_field_is_ts18010() {
  let src = "class A {\n  /**\n   * @public\n   */\n  #a = 1;\n}\n";
  // Force JS file kind via .js name (enables JSDoc scanning).
  let d = diags(es2015(), "t.js", src);
  let hits: Vec<_> = d.iter().filter(|(c, _, _, _)| c == "TS18010").collect();
  assert_eq!(hits.len(), 1, "{d:?}");
  let slice = &src[hits[0].1 as usize..hits[0].2 as usize];
  assert!(
    slice.starts_with("@public"),
    "span should start at @public (tsc): {slice:?} from {hits:?}"
  );
  assert!(
    slice.ends_with("*/") == false && src[hits[0].2 as usize..].starts_with("*/"),
    "span should end at closing */ (exclusive): {slice:?}"
  );
}

#[test]
fn js_getter_setter_pair_no_tc3000_on_setter_param() {
  // Mirrors privateNamesIncompatibleModifiersJs: paired get/set #prop with
  // @public — tsc emits only TS18010 (setter param typed from getter return).
  let mut opts = es2015();
  opts.no_implicit_any = true;
  opts.strict_null_checks = true;
  let src = r#"
class A {
  /**
   * @public
   */
  get #aProp() { return 1; }
  /**
   * @public
   */
  set #aProp(value) { }
}
"#;
  let d = diags(opts, "t.js", src);
  assert!(
    d.iter().any(|(c, _, _, _)| c == "TS18010"),
    "expected TS18010: {d:?}"
  );
  assert!(
    !d.iter().any(|(c, _, _, _)| c == "TC3000"),
    "setter param must be contextual from getter: {d:?}"
  );
}
