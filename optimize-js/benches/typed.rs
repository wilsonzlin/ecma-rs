// When the `typed` feature is disabled we still want this benchmark target to
// compile (so `cargo bench -p optimize-js` works). Criterion is only used when
// `typed` is enabled.
#[cfg(not(feature = "typed"))]
fn main() {}

#[cfg(feature = "typed")]
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
#[cfg(feature = "typed")]
use optimize_js::{
  compile_source, compile_source_typed, compile_source_with_typecheck, TopLevelMode,
};
#[cfg(feature = "typed")]
use std::hint::black_box;
#[cfg(feature = "typed")]
use std::sync::Arc;
#[cfg(feature = "typed")]
use std::time::Duration;

/// Small-but-nontrivial TypeScript source that triggers typed optimizations:
/// - optional chaining (`console?.log`)
/// - nullish coalescing (`??`)
/// - `typeof` folding (`typeof s === "string"`)
/// - boolean literal-returning functions (`alwaysFalse(): false`, `alwaysTrue(): true`)
#[cfg(feature = "typed")]
const SOURCE: &str = r#"
function alwaysFalse(): false {
  return false;
}

function alwaysTrue(): true {
  return true;
}

function sideEffect(): number {
  return Math.round(Math.random() * 10);
}

let s: string = "x";
let u: string | number = 1;

if (typeof s === "string") {
  console?.log(s ?? "fallback", u?.toString());
} else {
  console?.log("never");
}

console.log(console ?? sideEffect());

if (alwaysFalse()) {
  console.log(1);
} else {
  console.log(2);
}

if (alwaysTrue()) {
  console.log(3);
} else {
  console.log(4);
}
"#;

#[cfg(feature = "typed")]
fn build_multifile_type_program(
  source: &str,
) -> (Arc<typecheck_ts::Program>, typecheck_ts::FileId) {
  let mut host = typecheck_ts::MemoryHost::new();
  let dummy = typecheck_ts::FileKey::new("file0.ts");
  let target = typecheck_ts::FileKey::new("file1.ts");

  // The dummy file ensures that the optimized file has a nonzero `FileId` (the
  // `file{N}.ts` naming pattern reserves `FileId(N)`).
  host.insert(dummy.clone(), "let dummy = 0;");
  host.insert(target.clone(), source);

  let program = Arc::new(typecheck_ts::Program::new(
    host,
    vec![dummy, target.clone()],
  ));
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected typecheck to succeed; diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&target).expect("typecheck file id");
  assert_ne!(file_id.0, 0, "expected nonzero file id for target file");

  // Pre-warm per-body caches so the benchmark measures mapping + optimization,
  // rather than first-use type checking costs.
  for body in program.bodies_in_file(file_id) {
    let _ = program.check_body(body);
  }

  (program, file_id)
}

#[cfg(feature = "typed")]
fn bench_typed_compile(c: &mut Criterion) {
  let source = SOURCE;

  let (type_program, type_file) = build_multifile_type_program(source);

  let mut group = c.benchmark_group("typed_compile");
  group.throughput(Throughput::Bytes(source.len() as u64));
  group.sample_size(100);

  group.bench_function(BenchmarkId::new("compile_source", "untyped"), |b| {
    b.iter(|| {
      let program =
        compile_source(black_box(source), TopLevelMode::Module, false).expect("compile");
      black_box(program);
    });
  });

  // This variant includes full typechecking, which makes it much slower than the
  // untyped baseline. Use fewer samples so `cargo bench` stays reasonably fast.
  group.sample_size(10);
  group.measurement_time(Duration::from_secs(10));
  group.bench_function(
    BenchmarkId::new("compile_source_typed", "internal_host"),
    |b| {
      b.iter(|| {
        let program = compile_source_typed(black_box(source), TopLevelMode::Module, false)
          .expect("compile typed");
        black_box(program);
      });
    },
  );

  group.sample_size(100);
  group.measurement_time(Duration::from_secs(5));
  group.bench_function(
    BenchmarkId::new("compile_source_with_typecheck", "external_multifile"),
    |b| {
      b.iter(|| {
        let program = compile_source_with_typecheck(
          black_box(source),
          TopLevelMode::Module,
          false,
          Arc::clone(&type_program),
          type_file,
        )
        .expect("compile with external typecheck program");
        black_box(program);
      });
    },
  );

  group.finish();
}

#[cfg(feature = "typed")]
criterion_group!(typed_compile, bench_typed_compile);
#[cfg(feature = "typed")]
criterion_main!(typed_compile);
