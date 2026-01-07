#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
  types_ts_interned::fuzz_type_graph(data);
});

