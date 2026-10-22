//! Residual privateNames: bare `#` (TS1127) + object rest strips privates (TS2339).

use typecheck_ts::lib_support::{CompilerOptions, ScriptTarget};
use typecheck_ts::{FileKey, MemoryHost, Program};

fn check(src: &str) -> Vec<(String, u32, u32, String)> {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2015;
  opts.strict_null_checks = true;
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  program
    .check()
    .into_iter()
    .map(|d| {
      (
        d.code.as_str().to_string(),
        d.primary.range.start,
        d.primary.range.end,
        src[d.primary.range.start as usize..d.primary.range.end as usize].to_string(),
      )
    })
    .collect()
}

#[test]
fn bare_hash_char_name_is_ts1127_thrice() {
  let src = "\n#\n\nclass C {\n    #\n\n    m() {\n        this.#\n    }\n}\n";
  let diags = check(src);
  let hashes: Vec<_> = diags
    .iter()
    .filter(|d| d.0 == "PS0030" || d.0 == "TS1127")
    .collect();
  assert_eq!(hashes.len(), 3, "expected 3 bare-hash diags, got {diags:?}");
  for h in &hashes {
    assert_eq!(h.3, "#");
  }
  // Prefer no semantic cascade on recovered bare hashes.
  let extras: Vec<_> = diags
    .iter()
    .filter(|d| d.0 != "PS0030" && d.0 != "TS1127")
    .collect();
  assert!(
    extras.is_empty(),
    "unexpected extras alongside TS1127: {extras:?}"
  );
}

#[test]
fn object_rest_spread_private_is_ts2339_four() {
  let src = r#"
class C {
    #prop = 1;
    static #propStatic = 1;
    method(other: C) {
        const obj = { ...other };
        obj.#prop;
        const { ...rest } = other;
        rest.#prop;
        const statics = { ... C};
        statics.#propStatic
        const { ...sRest } = C;
        sRest.#propStatic;
    }
}
"#;
  let diags = check(src);
  let ts2339: Vec<_> = diags.iter().filter(|d| d.0 == "TS2339").collect();
  assert_eq!(ts2339.len(), 4, "expected 4×TS2339, got {diags:?}");
  for d in &ts2339 {
    assert!(d.3.starts_with('#'), "{d:?}");
  }
  let extras: Vec<_> = diags.iter().filter(|d| d.0 != "TS2339").collect();
  assert!(extras.is_empty(), "unexpected extras: {extras:?}");
}
