use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn probe_callback_arity() {
  let src = "/**\n * @callback Cb\n * @param {Object} person\n * @param {string} person.name\n * @param {number} [person.age]\n * @returns {void}\n */\n/** @param {Cb} callback @returns {void} */\nfunction use(callback) {\n    callback({ name: \"E\" }, 2);\n}\n";
  let mut options = CompilerOptions::default();
  options.check_js = Some(true);
  let mut host = MemoryHost::with_options(options);
  let file = FileKey::new("t.js");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  for d in program.check() {
    println!("DIAG {} {}", d.code.as_str(), d.message);
  }
  let src2 = "/**\n * @callback Cb2\n * @param {string} first\n * @param {string} opts.name\n * @param {number} opts.count\n * @param {boolean} last\n * @returns {void}\n */\n/** @param {Cb2} cb @returns {void} */\nfunction use2(cb) {\n  cb(\"a\", { name: \"x\" }, true);\n}\n";
  let mut options = CompilerOptions::default();
  options.check_js = Some(true);
  let mut host = MemoryHost::with_options(options);
  let file = FileKey::new("t.js");
  host.insert(file.clone(), src2);
  let program = Program::new(host, vec![file]);
  for d in program.check() {
    println!("DIAG2 {} {}", d.code.as_str(), d.message);
  }
}
