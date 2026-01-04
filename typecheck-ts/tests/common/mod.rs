use std::sync::Arc;

use typecheck_ts::lib_support::{FileKind, LibFile};
use typecheck_ts::FileKey;

const CORE_GLOBAL_TYPES: &str = r#"
interface Array<T> {}
interface Boolean {}
interface Function {}
interface IArguments {}
interface Number {}
interface Object {}
interface RegExp {}
interface String {}

declare var Array: any;
declare var Boolean: any;
declare var Function: any;
declare var Number: any;
declare var Object: any;
declare var RegExp: any;
declare var String: any;
"#;

pub fn core_globals_lib() -> LibFile {
  LibFile {
    key: FileKey::new("core_globals.d.ts"),
    name: Arc::from("core_globals.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(CORE_GLOBAL_TYPES),
  }
}

