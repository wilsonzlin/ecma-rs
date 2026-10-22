//! Grammar diagnostics on private identifiers survive the `checkJs: false`
//! filter: tsc reports them as parser errors regardless of `checkJs`
//! (`privateNameUncheckedJsOptionalChain.js`). TS18030 (optional chain +
//! private identifier), and its siblings TS18016 (outside class) / TS18028
//! (target too low), are retained alongside parse-level codes.

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes_with(src: &str, key: &str, options: CompilerOptions) -> Vec<String> {
  let mut host = MemoryHost::with_options(options);
  let file = FileKey::new(key);
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
fn optional_chain_private_identifier_survives_check_js_off() {
  let src = "class C {\n    #bar;\n    constructor () {\n        this?.#foo;\n        this?.#bar;\n    }\n}\n";
  let mut options = CompilerOptions::default();
  options.check_js = Some(false);
  assert_eq!(codes_with(src, "a.js", options), ["TS18030", "TS18030"],);
}

#[test]
fn optional_chain_private_identifier_reports_in_ts() {
  let src = "class C {\n    #bar;\n    constructor () {\n        this?.#foo;\n    }\n}\n";
  assert_eq!(
    codes_with(src, "a.ts", CompilerOptions::default()),
    ["TS18030"],
  );
}
