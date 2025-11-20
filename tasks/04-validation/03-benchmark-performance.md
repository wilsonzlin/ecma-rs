---
task_id: "04-validation/03-benchmark-performance"
phase: "04-validation"
title: "Benchmark Performance Post-Implementation"
dependencies:
  - "04-validation/01-run-conformance"
  - "04-validation/02-validate-real-world"
inputs:
  - "workspace/outputs/01-analysis/06-baseline-performance/baseline-performance.json"
  - "workspace/outputs/04-validation/02-validate-real-world/project-results.json"
outputs:
  - "workspace/outputs/04-validation/03-benchmark-performance/final-performance.json"
  - "workspace/outputs/04-validation/03-benchmark-performance/performance-report.md"
  - "workspace/outputs/04-validation/03-benchmark-performance/regression-analysis.md"
estimated_duration: "3-4 hours"
complexity: "medium"
priority: "high"
---

# Task: Benchmark Performance Post-Implementation

## Objective

Measure parser performance after Phase 3 implementations, compare against baseline metrics, identify any performance regressions, and document performance characteristics for future optimization work.

## Context

Performance benchmarking serves multiple purposes:
1. **Regression detection**: Ensure new features didn't slow down parsing
2. **Baseline for optimization**: Establish metrics before Phase 5 optimization work
3. **Production readiness**: Validate performance is acceptable for real-world use
4. **Bottleneck identification**: Find hot paths for optimization

### Performance Goals
- **No regression**: New features shouldn't slow existing parsing by >10%
- **Acceptable absolute performance**: Parse TypeScript stdlib in <100ms
- **Scalability**: Linear scaling with file size
- **Memory efficiency**: <500MB for large files

## Instructions

### Step 1: Set Up Benchmarking Infrastructure

**File**: `benches/parser_bench.rs`

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use parse_js::parse;
use std::fs;

fn bench_type_parsing(c: &mut Criterion) {
    let samples = vec![
        // Small files (fast iteration)
        ("simple_types", "type T = string | number;"),
        ("generic_function", "function f<T, U>(x: T, y: U): [T, U] { return [x, y]; }"),

        // Medium complexity
        ("mapped_type", include_str!("../samples/mapped_types.ts")),
        ("conditional_type", include_str!("../samples/conditional_types.ts")),

        // Large real-world files
        ("lib_es5", include_str!("../tests/TypeScript/src/lib/es5.d.ts")),
        ("lib_es2015", include_str!("../tests/TypeScript/src/lib/es2015.d.ts")),
        ("lib_dom", include_str!("../tests/TypeScript/src/lib/dom.d.ts")),

        // Stress tests
        ("deep_nesting", include_str!("../samples/deep_nesting.ts")),
        ("wide_union", include_str!("../samples/wide_union.ts")),
    ];

    let mut group = c.benchmark_group("type_parsing");

    for (name, source) in samples {
        group.bench_with_input(
            BenchmarkId::from_parameter(name),
            &source,
            |b, src| {
                b.iter(|| {
                    parse(black_box(src)).expect("parse should succeed")
                });
            },
        );
    }

    group.finish();
}

fn bench_real_world_files(c: &mut Criterion) {
    let files = vec![
        "workspace/real-world-projects/TypeScript/src/compiler/checker.ts",
        "workspace/real-world-projects/TypeScript/src/compiler/parser.ts",
        "workspace/real-world-projects/vscode/src/vs/editor/editor.api.ts",
        "workspace/real-world-projects/vue3/packages/runtime-core/src/component.ts",
    ];

    let mut group = c.benchmark_group("real_world");
    group.sample_size(10);  // Slower, so fewer samples

    for file_path in files {
        if let Ok(source) = fs::read_to_string(file_path) {
            let name = file_path.split('/').last().unwrap();
            group.bench_with_input(
                BenchmarkId::from_parameter(name),
                &source,
                |b, src| {
                    b.iter(|| {
                        parse(black_box(src)).expect("parse should succeed")
                    });
                },
            );
        }
    }

    group.finish();
}

fn bench_scaling(c: &mut Criterion) {
    // Test how performance scales with input size
    let base_type = "type T = string | number;\n";

    let mut group = c.benchmark_group("scaling");

    for size in [10, 100, 1000, 10000].iter() {
        let source = base_type.repeat(*size);

        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &source,
            |b, src| {
                b.iter(|| {
                    parse(black_box(src)).expect("parse should succeed")
                });
            },
        );
    }

    group.finish();
}

criterion_group!(benches, bench_type_parsing, bench_real_world_files, bench_scaling);
criterion_main!(benches);
```

### Step 2: Create Benchmark Samples

Create sample files for specific benchmarks:

**File**: `samples/mapped_types.ts`
```typescript
type ReadonlyRecord<K extends string, V> = {
    +readonly [P in K]: V;
};

type Required<T> = {
    [P in keyof T]-?: T[P];
};

type Getters<T> = {
    +readonly [K in keyof T as `get${Capitalize<K & string>}`]: () => T[K];
};
```

**File**: `samples/conditional_types.ts`
```typescript
type Awaited<T> = T extends Promise<infer U> ? U : T;
type UnwrapArray<T> = T extends Array<infer U> ? U : T;
type ReturnType<T> = T extends (...args: any[]) => infer R ? R : never;
```

**File**: `samples/deep_nesting.ts`
```typescript
type Deep = {
    a: {
        b: {
            c: {
                d: {
                    e: {
                        f: {
                            g: {
                                h: string
                            }
                        }
                    }
                }
            }
        }
    }
};
```

**File**: `samples/wide_union.ts`
```typescript
type Wide =
    | "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j"
    | "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t"
    | "u" | "v" | "w" | "x" | "y" | "z";
// ... repeat for 100+ members
```

### Step 3: Run Benchmarks

```bash
# Run all benchmarks
cargo bench --bench parser_bench

# Save results
cargo bench --bench parser_bench -- --save-baseline post-impl

# If baseline exists, compare
cargo bench --bench parser_bench -- --baseline baseline --save-baseline post-impl
```

### Step 4: Parse Benchmark Results

Criterion outputs to `target/criterion/`. Parse the results:

**File**: `scripts/parse-bench-results.js`

```javascript
const fs = require('fs');
const path = require('path');

const criterionDir = 'target/criterion';

function parseBenchmarkGroup(groupName) {
    const groupDir = path.join(criterionDir, groupName);
    const estimatesPath = path.join(groupDir, 'base/estimates.json');

    if (!fs.existsSync(estimatesPath)) {
        return null;
    }

    const estimates = JSON.parse(fs.readFileSync(estimatesPath, 'utf8'));

    return {
        group: groupName,
        mean: estimates.mean.point_estimate,
        std_dev: estimates.std_dev.point_estimate,
        median: estimates.median.point_estimate,
        unit: 'nanoseconds'
    };
}

function getAllBenchmarks() {
    const groups = fs.readdirSync(criterionDir)
        .filter(name => fs.statSync(path.join(criterionDir, name)).isDirectory())
        .filter(name => name !== 'report');

    return groups.map(parseBenchmarkGroup).filter(x => x !== null);
}

const benchmarks = getAllBenchmarks();

fs.writeFileSync(
    'workspace/outputs/04-validation/03-benchmark-performance/raw-results.json',
    JSON.stringify(benchmarks, null, 2)
);

console.log('Parsed benchmark results:', benchmarks.length, 'groups');
```

### Step 5: Compare with Baseline

**File**: `scripts/compare-performance.js`

```javascript
const fs = require('fs');

const baseline = JSON.parse(
    fs.readFileSync('workspace/outputs/01-analysis/06-baseline-performance/baseline-performance.json', 'utf8')
);

const current = JSON.parse(
    fs.readFileSync('workspace/outputs/04-validation/03-benchmark-performance/raw-results.json', 'utf8')
);

function findBaseline(benchmarkName) {
    return baseline.benchmarks?.find(b => b.name === benchmarkName);
}

function nsToMs(ns) {
    return ns / 1_000_000;
}

const comparison = current.map(bench => {
    const base = findBaseline(bench.group);

    if (!base) {
        return {
            name: bench.group,
            current_ms: nsToMs(bench.mean),
            baseline_ms: null,
            change_percent: null,
            regression: false
        };
    }

    const current_ms = nsToMs(bench.mean);
    const baseline_ms = nsToMs(base.mean);
    const change_percent = ((current_ms - baseline_ms) / baseline_ms) * 100;

    return {
        name: bench.group,
        current_ms,
        baseline_ms,
        change_percent,
        regression: change_percent > 10  // >10% slower is regression
    };
});

const summary = {
    timestamp: new Date().toISOString(),
    total_benchmarks: comparison.length,
    regressions: comparison.filter(c => c.regression).length,
    improvements: comparison.filter(c => c.change_percent < -5).length,
    avg_change_percent: comparison.reduce((sum, c) => sum + (c.change_percent || 0), 0) / comparison.length,
    benchmarks: comparison
};

fs.writeFileSync(
    'workspace/outputs/04-validation/03-benchmark-performance/final-performance.json',
    JSON.stringify(summary, null, 2)
);

console.log('=== Performance Comparison ===');
console.log(`Total benchmarks: ${summary.total_benchmarks}`);
console.log(`Regressions: ${summary.regressions}`);
console.log(`Improvements: ${summary.improvements}`);
console.log(`Average change: ${summary.avg_change_percent.toFixed(2)}%`);

if (summary.regressions > 0) {
    console.log('\n⚠️ Regressions detected:');
    comparison.filter(c => c.regression).forEach(c => {
        console.log(`  ${c.name}: +${c.change_percent.toFixed(2)}% (${c.current_ms.toFixed(2)}ms vs ${c.baseline_ms.toFixed(2)}ms)`);
    });
}
```

```bash
node scripts/compare-performance.js
```

### Step 6: Create Performance Report

**File**: `workspace/outputs/04-validation/03-benchmark-performance/performance-report.md`

```markdown
# Performance Benchmark Report

## Executive Summary

After implementing 10 TypeScript features in Phase 3, performance analysis shows:

- **Average performance change**: X%
- **Regressions detected**: Y benchmarks
- **Improvements**: Z benchmarks
- **Overall assessment**: ✅ Acceptable / ⚠️ Needs attention / ❌ Critical issues

## Benchmark Results

### Type Parsing Benchmarks

| Benchmark | Baseline | Current | Change | Status |
|-----------|----------|---------|--------|--------|
| simple_types | X ms | Y ms | +Z% | ✅ / ⚠️ / ❌ |
| generic_function | X ms | Y ms | +Z% | ✅ |
| mapped_type | X ms | Y ms | +Z% | ✅ |
| conditional_type | X ms | Y ms | +Z% | ✅ |
| lib_es5 | X ms | Y ms | +Z% | ✅ |
| lib_es2015 | X ms | Y ms | +Z% | ✅ |
| lib_dom | X ms | Y ms | +Z% | ✅ |

### Real-World File Benchmarks

| File | Baseline | Current | Change | Status |
|------|----------|---------|--------|--------|
| checker.ts | X ms | Y ms | +Z% | ✅ |
| parser.ts | X ms | Y ms | +Z% | ✅ |
| editor.api.ts | X ms | Y ms | +Z% | ✅ |
| component.ts | X ms | Y ms | +Z% | ✅ |

### Scaling Benchmarks

| Input Size | Time | Per-Item | Scaling Factor |
|------------|------|----------|----------------|
| 10 lines | X ms | Y μs | 1.0x |
| 100 lines | X ms | Y μs | Z.Zx |
| 1K lines | X ms | Y μs | Z.Zx |
| 10K lines | X ms | Y μs | Z.Zx |

**Scaling analysis**: Linear / Sub-linear / Super-linear

## Regression Analysis

### Critical Regressions (>25% slower)
[List if any]

### Moderate Regressions (10-25% slower)
[List if any]

### Minor Regressions (5-10% slower)
[List if any]

### Analysis
[For each regression, explain why and whether it's acceptable]

## Performance Improvements

### Significant Improvements (>10% faster)
[List if any - unexpected but good!]

### Analysis
[Why did performance improve? Better algorithms? Compiler optimizations?]

## Absolute Performance Metrics

### TypeScript Standard Library
- **lib.es5.d.ts**: X ms (Y LOC, Z KB)
- **lib.dom.d.ts**: X ms (Y LOC, Z KB)
- **Total stdlib**: X ms

**Goal**: <100ms ✅ / ❌

### Large Real-World Files
- **Largest file tested**: path/to/file.ts (X LOC, Y KB, Z ms)
- **Average parse time**: X ms per file
- **Throughput**: Y files/second

## Memory Usage

### Peak Memory
- **Small files (<1KB)**: X MB
- **Medium files (10-100KB)**: X MB
- **Large files (>100KB)**: X MB

**Goal**: <500MB for large files ✅ / ❌

### Memory Scaling
[How does memory usage scale with file size?]

## Performance Hotspots

Based on profiling:

1. **Hottest function**: `function_name` (X% of time)
2. **Second hottest**: `function_name` (X% of time)
3. **Third hottest**: `function_name` (X% of time)

**Opportunities for Phase 5 optimization**:
- [ ] Optimize [hotspot 1]
- [ ] Optimize [hotspot 2]

## Comparison with Other Parsers

### Parse Speed (if data available)

| Parser | TypeScript stdlib | Speedup |
|--------|------------------|---------|
| ecma-rs (ours) | X ms | 1.0x |
| oxc | Y ms | Z.Zx |
| swc | Y ms | Z.Zx |
| TypeScript (tsc) | Y ms | Z.Zx |

## Production Readiness Assessment

### Performance Criteria

- [ ] Parse stdlib in <100ms: ✅ / ❌ (X ms)
- [ ] No critical regressions: ✅ / ❌ (Y regressions)
- [ ] Linear scaling: ✅ / ❌ (Z.Zx factor)
- [ ] Acceptable memory usage: ✅ / ❌ (X MB)
- [ ] Throughput >50 files/sec: ✅ / ❌ (X files/sec)

**Overall**: Ready / Needs optimization / Needs fixes

## Recommendations for Phase 5

### High Priority Optimizations
1. [Specific optimization] - could improve by X%
2. [Another optimization] - could improve by Y%

### Medium Priority
1. [Optimization]
2. [Optimization]

### Low Priority
1. [Optimization]

## Conclusion

**Performance verdict**: Acceptable / Needs work / Critical issues

**Recommendation**: Proceed to Phase 5 / Fix regressions first

**Expected Phase 5 improvement**: X-Y% faster
```

### Step 7: Regression Analysis

**File**: `workspace/outputs/04-validation/03-benchmark-performance/regression-analysis.md`

```markdown
# Performance Regression Analysis

## Regressions Detected

[For each regression:]

### Regression #1: [Benchmark Name]

**Magnitude**: +X% slower (Y ms → Z ms)

**Severity**: Critical / High / Medium / Low

**Likely cause**:
[Analysis of what changed in Phase 3 that could cause this]

**Affected code paths**:
- `function_name_1` in `file.rs`
- `function_name_2` in `file.rs`

**Justification analysis**:
- **Is regression acceptable?** Yes / No
- **Reason**: [e.g., "Feature X requires additional parsing passes, but enables critical functionality"]
- **Can be optimized in Phase 5?** Yes / No

**Action items**:
- [ ] Profile this specific case
- [ ] Identify optimization opportunities
- [ ] Add to Phase 5 optimization backlog

---

[Repeat for each regression]

## Overall Regression Analysis

**Total regression impact**: +X% average slowdown

**Acceptable?**: Yes / No

**Rationale**:
[Overall assessment of whether regressions are justified by functionality gains]
```

## Verification Commands

```bash
# 1. Check benchmarks ran
ls -lh target/criterion/

# 2. View results
cat workspace/outputs/04-validation/03-benchmark-performance/final-performance.json | jq '.'

# 3. Check for regressions
cat workspace/outputs/04-validation/03-benchmark-performance/final-performance.json | \
    jq '.benchmarks[] | select(.regression == true)'
```

## Common Issues

### Issue 1: Unstable Benchmarks
**Problem**: Results vary between runs

**Solution**: Increase sample size, disable CPU scaling, close other programs

### Issue 2: Baseline Missing
**Problem**: No baseline to compare against

**Solution**: Use current run as baseline for future comparisons

### Issue 3: Criterion Not Installed
**Problem**: Benchmark harness missing

**Solution**: Add to `Cargo.toml`:
```toml
[dev-dependencies]
criterion = "0.5"

[[bench]]
name = "parser_bench"
harness = false
```

## Acceptance Criteria

- [ ] All benchmarks executed successfully
- [ ] Results compared with baseline
- [ ] Performance report generated
- [ ] Regression analysis complete
- [ ] No critical performance regressions (>25% slower)
- [ ] Absolute performance goals met (<100ms for stdlib)
- [ ] Scaling characteristics documented

## Success Metrics

**Minimum**: No regressions >10%, stdlib <150ms
**Target**: No regressions >5%, stdlib <100ms
**Exceptional**: Performance improvements, stdlib <50ms

## Resources

- Criterion docs: https://bheisler.github.io/criterion.rs/
- Rust profiling: https://nnethercote.github.io/perf-book/
- Baseline results: `workspace/outputs/01-analysis/06-baseline-performance/`

## Notes

Performance benchmarking is critical for:
1. Ensuring features don't negatively impact speed
2. Establishing baseline for Phase 5 optimization
3. Validating production readiness

Be thorough and document all regressions, even if acceptable.
