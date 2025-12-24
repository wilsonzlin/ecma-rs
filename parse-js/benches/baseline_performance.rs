use criterion::criterion_group;
use criterion::criterion_main;
use criterion::BenchmarkId;
use criterion::Criterion;
use criterion::Throughput;
use parse_js::parse;
use std::hint::black_box;

fn bench_type_parsing(c: &mut Criterion) {
  let samples = vec![
    // Small files (< 100 lines)
    (
      "primitive_types",
      include_str!("../samples/primitive_types.ts"),
      27,
    ),
    (
      "simple_interface",
      include_str!("../samples/simple_interface.ts"),
      53,
    ),
    // Medium files (100-1000 lines)
    (
      "complex_types",
      include_str!("../samples/complex_types.ts"),
      120,
    ),
    (
      "medium_file",
      include_str!("../samples/medium_file.ts"),
      318,
    ),
    // Large files (> 1000 lines)
    ("large_file", include_str!("../samples/large_file.ts"), 836),
    (
      "very_large_file",
      include_str!("../samples/very_large_file.ts"),
      2508,
    ),
  ];

  let mut group = c.benchmark_group("type_parsing");

  for (name, source, lines) in samples {
    let bytes = source.len();

    group.throughput(Throughput::Bytes(bytes as u64));

    group.bench_with_input(BenchmarkId::from_parameter(name), &source, |b, &src| {
      b.iter(|| {
        let result = parse(black_box(src));
        // Force evaluation
        result.ok();
      });
    });

    // Report metadata
    eprintln!("{}: {} lines, {} bytes", name, lines, bytes);
  }

  group.finish();
}

fn bench_specific_features(c: &mut Criterion) {
  let mut group = c.benchmark_group("type_features");

  // Benchmark specific type constructs
  let features = vec![
    ("union_small", "type T = A | B | C;"),
    (
      "union_large",
      "type T = A | B | C | D | E | F | G | H | I | J;",
    ),
    (
      "conditional",
      "type T<U> = U extends string ? true : false;",
    ),
    ("mapped", "type T<O> = { [K in keyof O]: O[K] };"),
    ("template", "type T = `Hello ${string}`;"),
    ("tuple", "type T = [string, number, boolean];"),
    (
      "nested_conditional",
      "type T<A, B, C, D> = A extends B ? C extends D ? E : F : G extends H ? I : J;",
    ),
    (
      "intersection",
      "type T = { a: string } & { b: number } & { c: boolean };",
    ),
    ("indexed_access", "type T<O, K extends keyof O> = O[K];"),
    (
      "function_type",
      "type T = (a: string, b: number) => boolean;",
    ),
    ("generic_function", "type T = <A, B>(a: A, b: B) => [A, B];"),
    ("array_type", "type T = Array<string | number>;"),
    ("readonly_array", "type T = readonly [string, number];"),
    ("optional_props", "type T = { a?: string; b?: number; };"),
    (
      "string_literal_union",
      r#"type T = "foo" | "bar" | "baz" | "qux";"#,
    ),
  ];

  for (name, source) in features {
    group.bench_function(name, |b| b.iter(|| parse(black_box(source))));
  }

  group.finish();
}

fn bench_real_world_patterns(c: &mut Criterion) {
  let mut group = c.benchmark_group("real_world_patterns");

  // Realistic code patterns
  let patterns = vec![
    (
      "interface_with_methods",
      r#"
            interface User {
                id: number;
                name: string;
                email: string;
                getFullName(): string;
                updateEmail(email: string): Promise<void>;
                delete(): Promise<boolean>;
            }
            "#,
    ),
    (
      "class_with_generics",
      r#"
            class Container<T> {
                private value: T;
                constructor(value: T) {
                    this.value = value;
                }
                getValue(): T {
                    return this.value;
                }
                setValue(value: T): void {
                    this.value = value;
                }
            }
            "#,
    ),
    (
      "react_component_type",
      r#"
            type Props = {
                title: string;
                onClick: (event: MouseEvent) => void;
                children?: ReactNode;
            };
            type ComponentType = React.FC<Props>;
            "#,
    ),
    (
      "api_response_type",
      r#"
            interface APIResponse<T> {
                success: boolean;
                data?: T;
                error?: {
                    code: string;
                    message: string;
                    details?: Record<string, any>;
                };
                meta: {
                    requestId: string;
                    timestamp: number;
                };
            }
            "#,
    ),
    (
      "discriminated_union",
      r#"
            type Result<T, E> =
                | { ok: true; value: T }
                | { ok: false; error: E };

            type Shape =
                | { kind: 'circle'; radius: number }
                | { kind: 'square'; size: number }
                | { kind: 'rectangle'; width: number; height: number };
            "#,
    ),
  ];

  for (name, source) in patterns {
    group.bench_function(name, |b| b.iter(|| parse(black_box(source))));
  }

  group.finish();
}

fn bench_stress_test(c: &mut Criterion) {
  let mut group = c.benchmark_group("stress_test");

  // Generate deeply nested types
  let deep_nesting = {
    let mut s = String::from("type T0 = string;\n");
    for i in 1..20 {
      s.push_str(&format!("type T{} = T{} | T{};\n", i, i - 1, i - 1));
    }
    s
  };

  // Generate wide union type
  let wide_union = {
    let mut s = String::from("type T = ");
    for i in 0..50 {
      if i > 0 {
        s.push_str(" | ");
      }
      s.push_str(&format!("Type{}", i));
    }
    s.push(';');
    s
  };

  // Generate many small types
  let many_types = {
    let mut s = String::new();
    for i in 0..100 {
      s.push_str(&format!("type T{} = string | number;\n", i));
    }
    s
  };

  group.bench_function("deep_nesting", |b| {
    b.iter(|| parse(black_box(&deep_nesting)))
  });

  group.bench_function("wide_union", |b| b.iter(|| parse(black_box(&wide_union))));

  group.bench_function("many_types", |b| b.iter(|| parse(black_box(&many_types))));

  group.finish();
}

criterion_group!(
  benches,
  bench_type_parsing,
  bench_specific_features,
  bench_real_world_patterns,
  bench_stress_test
);
criterion_main!(benches);
