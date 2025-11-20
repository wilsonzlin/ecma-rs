---
task_id: "01-analysis/06-baseline-performance"
title: "Baseline Performance Benchmarking"
phase: "analysis"
estimated_duration: "2-3 hours"
complexity: "low"
dependencies: []
inputs: []
outputs:
  - "baseline-performance.json"
  - "performance-report.md"
  - "benchmark-results/"
  - "profiling-data/"
skills_required:
  - "Rust development"
  - "Performance analysis"
  - "Benchmarking"
---

# Task: Baseline Performance Benchmarking

## Objective

Establish current parser performance baseline metrics to measure improvements and regressions during implementation. Benchmark parsing speed, memory usage, and identify performance bottlenecks.

## Context

### Why This Matters

Need baseline to:
1. **Measure progress**: Track whether optimizations actually help
2. **Prevent regressions**: Ensure new features don't slow down parser
3. **Set targets**: Know what "good" performance looks like
4. **Identify bottlenecks**: Find hot paths before optimizing

### What We're Measuring

1. **Parsing speed**: Files/second, lines/second
2. **Memory usage**: Peak RSS, allocations
3. **Hot paths**: Where time is spent (profiling)
4. **Comparison**: vs TypeScript, vs oxc/swc

### Current State

Parser exists and works. Unknown:
- How fast is it?
- Where are bottlenecks?
- How much memory does it use?

## Prerequisites

### Tools to Install

```bash
# Criterion for benchmarking
cd /home/user/ecma-rs/parse-js
cargo add --dev criterion

# Flamegraph for profiling
cargo install flamegraph

# Hyperfine for command-line benchmarking
cargo install hyperfine

# Memory profiling (optional)
cargo install cargo-instruments  # macOS only
# or use valgrind/massif on Linux
```

### Sample Files for Benchmarking

Use TypeScript stdlib and real-world files:

```bash
# TypeScript standard library (already in repo)
ls parse-js/tests/TypeScript/src/lib/

# Extract representative samples
# Small: <100 lines
# Medium: 100-1000 lines
# Large: >1000 lines
# Complex: Heavy type usage
```

## Instructions

### Step 1: Create Benchmark Suite

Create `parse-js/benches/baseline_performance.rs`:

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId, Throughput};
use parse_js::parse;
use std::fs;

fn bench_type_parsing(c: &mut Criterion) {
    let samples = vec![
        // Small files (< 100 lines)
        ("primitive_types", include_str!("../samples/primitive_types.ts")),
        ("simple_interface", include_str!("../samples/simple_interface.ts")),

        // Medium files (100-1000 lines)
        ("lib_es5_d_ts", include_str!("../tests/TypeScript/src/lib/es5.d.ts")),
        ("lib_dom_d_ts", include_str!("../tests/TypeScript/src/lib/dom.d.ts")),

        // Large files (> 1000 lines)
        ("lib_es2020_d_ts", include_str!("../tests/TypeScript/src/lib/es2020.full.d.ts")),

        // Complex types
        ("react_types", include_str!("../samples/react.d.ts")),
        ("vue_types", include_str!("../samples/vue.d.ts")),
    ];

    let mut group = c.benchmark_group("type_parsing");

    for (name, source) in samples {
        let lines = source.lines().count();
        let bytes = source.len();

        group.throughput(Throughput::Bytes(bytes as u64));

        group.bench_with_input(
            BenchmarkId::from_parameter(name),
            &source,
            |b, &src| {
                b.iter(|| {
                    let result = parse(black_box(src));
                    // Force evaluation
                    result.ok();
                });
            },
        );

        // Report throughput
        println!("{}: {} lines, {} bytes", name, lines, bytes);
    }

    group.finish();
}

fn bench_specific_features(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_features");

    // Benchmark specific type constructs
    let features = vec![
        ("union_small", "type T = A | B | C;"),
        ("union_large", "type T = A | B | C | D | E | F | G | H | I | J;"),
        ("conditional", "type T = A extends B ? C : D;"),
        ("mapped", "type T = { [K in keyof O]: O[K] };"),
        ("template", "type T = `Hello ${string}`;"),
        ("tuple", "type T = [string, number, boolean];"),
        ("nested_conditional", "type T = A extends B ? C extends D ? E : F : G extends H ? I : J;"),
    ];

    for (name, source) in features {
        group.bench_function(name, |b| {
            b.iter(|| parse(black_box(source)))
        });
    }

    group.finish();
}

fn bench_stdlib(c: &mut Criterion) {
    // Benchmark TypeScript standard library
    let lib_files = vec![
        "es5.d.ts",
        "dom.d.ts",
        "es2015.core.d.ts",
        "es2015.promise.d.ts",
    ];

    let mut group = c.benchmark_group("typescript_stdlib");

    for filename in lib_files {
        let path = format!("tests/TypeScript/src/lib/{}", filename);
        if let Ok(source) = fs::read_to_string(&path) {
            group.bench_function(filename, |b| {
                b.iter(|| parse(black_box(&source)))
            });
        }
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_type_parsing,
    bench_specific_features,
    bench_stdlib
);
criterion_main!(benches);
```

### Step 2: Run Benchmarks

```bash
cd /home/user/ecma-rs/parse-js

# Run all benchmarks
cargo bench --bench baseline_performance

# Save results
cargo bench --bench baseline_performance -- --save-baseline initial

# Results saved to target/criterion/
```

Expected output:
```
type_parsing/primitive_types
                        time:   [45.2 µs 45.8 µs 46.5 µs]
                        thrpt:  [2.15 MiB/s 2.18 MiB/s 2.21 MiB/s]

type_parsing/lib_es5_d_ts
                        time:   [2.34 ms 2.38 ms 2.42 ms]
                        thrpt:  [15.2 MiB/s 15.5 MiB/s 15.7 MiB/s]
```

### Step 3: Profile Hot Paths

Generate flamegraph to see where time is spent:

```bash
# Create profiling script
cat > profile.sh << 'EOF'
#!/bin/bash
# Profile parsing a large file

cat > /tmp/large_type_file.ts << 'TYPESCRIPT'
// Include complex TypeScript with many type expressions
type A = string;
type B = number;
type C = A | B;
type D = { [K in keyof C]: C[K] };
// ... repeat 1000 times with variations
TYPESCRIPT

# Run under profiler
cargo flamegraph --bench baseline_performance -- --bench
EOF

chmod +x profile.sh
./profile.sh

# Output: flamegraph.svg
```

Analyze flamegraph:
- What functions take most time?
- Is time in lexing or parsing?
- Any obvious inefficiencies?

### Step 4: Memory Profiling

```bash
# Linux: Use valgrind massif
valgrind --tool=massif \
    --massif-out-file=massif.out \
    cargo bench --bench baseline_performance

ms_print massif.out > memory_profile.txt

# Look for:
# - Peak memory usage
# - Memory growth patterns
# - Allocation hot spots

# macOS: Use cargo-instruments
cargo instruments -t Allocations --bench baseline_performance

# Windows: Use Windows Performance Analyzer or VS profiler
```

### Step 5: Compare with Other Parsers

Benchmark TypeScript tsc and oxc for comparison:

```bash
# Create test file
cat > /tmp/benchmark_test.ts << 'EOF'
// 1000 lines of mixed TypeScript types
type User = {
  id: number;
  name: string;
  email: string;
};

interface Post {
  id: number;
  title: string;
  author: User;
}

// ... repeat with variations
EOF

# Benchmark with hyperfine

# TypeScript (just parsing, not checking)
hyperfine --warmup 3 \
    'tsc --noEmit --skipLibCheck /tmp/benchmark_test.ts' \
    --export-json tsc_bench.json

# Note: tsc always type-checks, can't isolate parsing

# If oxc is available:
hyperfine --warmup 3 \
    'oxc /tmp/benchmark_test.ts' \
    --export-json oxc_bench.json

# ecma-rs (create CLI wrapper if needed)
hyperfine --warmup 3 \
    'cargo run --release -- /tmp/benchmark_test.ts' \
    --export-json ecma_bench.json
```

### Step 6: Create Performance Report

**baseline-performance.json**:

```json
{
  "benchmark_date": "2025-11-20",
  "git_commit": "c2f4063",
  "rust_version": "1.75.0",
  "cpu": "Apple M3 Pro",
  "memory": "18 GB",

  "parsing_speed": {
    "small_files": {
      "primitive_types": {
        "lines": 25,
        "bytes": 512,
        "time_us": 45.8,
        "throughput_mib_s": 2.18,
        "lines_per_second": 546448
      },
      "simple_interface": {
        "lines": 50,
        "bytes": 1024,
        "time_us": 89.2,
        "throughput_mib_s": 2.24,
        "lines_per_second": 560538
      }
    },

    "medium_files": {
      "lib_es5_d_ts": {
        "lines": 4500,
        "bytes": 156823,
        "time_us": 2380,
        "throughput_mib_s": 15.5,
        "lines_per_second": 1890756
      },
      "lib_dom_d_ts": {
        "lines": 12000,
        "bytes": 487234,
        "time_us": 7234,
        "throughput_mib_s": 12.8,
        "lines_per_second": 1658745
      }
    },

    "large_files": {
      "lib_es2020_full_d_ts": {
        "lines": 25000,
        "bytes": 1234567,
        "time_us": 18234,
        "throughput_mib_s": 11.2,
        "lines_per_second": 1370919
      }
    },

    "averages": {
      "small_avg_throughput_mib_s": 2.21,
      "medium_avg_throughput_mib_s": 14.15,
      "large_avg_throughput_mib_s": 11.2,
      "overall_avg_lines_per_second": 1505092
    }
  },

  "feature_benchmarks": {
    "union_small": {"time_us": 12.3},
    "union_large": {"time_us": 34.5},
    "conditional": {"time_us": 28.7},
    "mapped": {"time_us": 45.2},
    "template": {"time_us": 38.9},
    "tuple": {"time_us": 18.4},
    "nested_conditional": {"time_us": 67.3}
  },

  "memory_usage": {
    "small_file_peak_mb": 2.3,
    "medium_file_peak_mb": 8.7,
    "large_file_peak_mb": 24.5,
    "stdlib_parse_peak_mb": 45.2,
    "allocations_per_line": 23,
    "average_allocation_size_bytes": 156
  },

  "profiling_insights": {
    "top_functions_by_time": [
      {"function": "type_primary", "percent": 32.5},
      {"function": "type_union", "percent": 15.3},
      {"function": "consume_token", "percent": 12.8},
      {"function": "peek_token", "percent": 8.4},
      {"function": "type_postfix", "percent": 7.2}
    ],
    "lexer_time_percent": 25.3,
    "parser_time_percent": 64.7,
    "ast_construction_percent": 10.0
  },

  "bottlenecks_identified": [
    {
      "location": "type_primary function",
      "issue": "Large match statement, many branches",
      "impact": "32.5% of parse time",
      "recommendation": "Split into smaller functions or use jump table"
    },
    {
      "location": "is_start_of_type_arguments",
      "issue": "Lookahead scans tokens twice",
      "impact": "~5% of parse time",
      "recommendation": "Cache speculation results"
    },
    {
      "location": "String allocations",
      "issue": "Frequent small allocations",
      "impact": "High allocation count",
      "recommendation": "Use arena allocation or string interning"
    }
  ],

  "comparison_with_others": {
    "typescript_tsc": {
      "note": "Can't isolate parsing from type checking",
      "full_pipeline_time_ms": 450,
      "estimated_parsing_percent": 20,
      "estimated_parsing_time_ms": 90
    },
    "oxc": {
      "available": false,
      "note": "Install oxc for comparison"
    },
    "swc": {
      "available": false,
      "note": "Install swc for comparison"
    },
    "ecma_rs_vs_tsc_parsing": {
      "speedup": "~5x faster (estimated)",
      "note": "TypeScript does more (type checking)"
    }
  }
}
```

**performance-report.md**:

```markdown
# Baseline Performance Report

**Date**: 2025-11-20
**Commit**: c2f4063
**Hardware**: Apple M3 Pro, 18 GB RAM
**Rust**: 1.75.0

## Executive Summary

### Parsing Speed
- **Small files** (<100 lines): ~2.2 MiB/s, 550K lines/second
- **Medium files** (100-1000 lines): ~14 MiB/s, 1.8M lines/second
- **Large files** (>1000 lines): ~11 MiB/s, 1.4M lines/second
- **Average**: ~1.5 million lines/second

### Memory Usage
- **Small files**: ~2 MB peak
- **Medium files**: ~9 MB peak
- **Large files**: ~25 MB peak
- **TypeScript stdlib**: ~45 MB peak

### Performance Assessment
- **Speed**: Good (1.5M lines/sec competitive with fast parsers)
- **Memory**: Moderate (could be optimized)
- **Scalability**: Linear with file size (good)

## Detailed Benchmarks

### Small Files (< 100 lines)

| File | Lines | Time (µs) | Throughput | Lines/sec |
|------|-------|-----------|------------|-----------|
| primitive_types | 25 | 45.8 | 2.18 MiB/s | 546K |
| simple_interface | 50 | 89.2 | 2.24 MiB/s | 561K |
| **Average** | 38 | 67.5 | 2.21 MiB/s | 554K |

### Medium Files (100-1000 lines)

| File | Lines | Time (µs) | Throughput | Lines/sec |
|------|-------|-----------|------------|-----------|
| lib/es5.d.ts | 4,500 | 2,380 | 15.5 MiB/s | 1.89M |
| lib/dom.d.ts | 12,000 | 7,234 | 12.8 MiB/s | 1.66M |
| **Average** | 8,250 | 4,807 | 14.15 MiB/s | 1.78M |

### Large Files (> 1000 lines)

| File | Lines | Time (µs) | Throughput | Lines/sec |
|------|-------|-----------|------------|-----------|
| lib/es2020.full.d.ts | 25,000 | 18,234 | 11.2 MiB/s | 1.37M |

### Feature-Specific Benchmarks

| Feature | Time (µs) | Relative |
|---------|-----------|----------|
| Union (3 types) | 12.3 | 1.0x |
| Union (10 types) | 34.5 | 2.8x |
| Conditional | 28.7 | 2.3x |
| Mapped type | 45.2 | 3.7x |
| Template literal | 38.9 | 3.2x |
| Tuple | 18.4 | 1.5x |
| Nested conditional | 67.3 | 5.5x |

**Observation**: Complex types (nested conditional, mapped) take 3-5x longer than simple unions.

## Profiling Results

### Time Distribution

| Component | Percentage |
|-----------|------------|
| Lexing | 25.3% |
| Parsing | 64.7% |
| AST construction | 10.0% |

### Hot Functions (Top 5)

1. **type_primary** - 32.5%
   - Most time spent here
   - Large match statement
   - Opportunity for optimization

2. **type_union** - 15.3%
   - Union type parsing
   - Reasonable for common feature

3. **consume_token** - 12.8%
   - Lexer function
   - Called very frequently

4. **peek_token** - 8.4%
   - Lookahead
   - Many calls

5. **type_postfix** - 7.2%
   - Array types, property access
   - Moderate time

### Flamegraph Insights

See `workspace/outputs/01-analysis/06-baseline-performance/flamegraph.svg`

Key observations:
- **type_primary dominates**: 32.5% in one function is high
- **Lexer is fast**: Only 25% is good
- **Parser is main cost**: 65% expected for complex grammar

## Memory Profile

### Peak Usage

| File Size | Peak RSS |
|-----------|----------|
| Small (<1 KB) | 2.3 MB |
| Medium (~500 KB) | 8.7 MB |
| Large (~1.2 MB) | 24.5 MB |

**Memory growth**: Roughly 20 bytes per line of input (includes AST)

### Allocation Pattern

- **Allocations per line**: ~23
- **Average allocation size**: 156 bytes
- **Dominated by**: AST nodes, Vec allocations

**Observation**: Frequent small allocations → Arena allocation could help

## Bottlenecks Identified

### 1. type_primary Function (HIGH IMPACT)
**Time**: 32.5% of parse time
**Issue**: Large match statement, many branches
**Why it matters**: Hot path, called for every type expression
**Optimization potential**: HIGH

**Recommendations**:
- Split into smaller functions
- Use jump table for keyword dispatch
- Add fast paths for common cases

### 2. Lookahead Speculation (MEDIUM IMPACT)
**Time**: ~5% of parse time
**Issue**: `is_start_of_type_arguments` scans tokens, then parser scans again
**Why it matters**: Repeated work
**Optimization potential**: MEDIUM

**Recommendations**:
- Cache speculation results
- Use speculative parsing with checkpoints
- Reduce lookahead distance where possible

### 3. Frequent Small Allocations (MEDIUM IMPACT)
**Impact**: Memory fragmentation, cache misses
**Issue**: Vec and Box allocations for every AST node
**Why it matters**: Allocation overhead accumulates
**Optimization potential**: HIGH

**Recommendations**:
- Arena allocation for AST nodes
- Pool frequently-created objects
- Use inline storage for small strings

## Comparison with Other Parsers

### vs TypeScript tsc

| Parser | Time (ms) | Notes |
|--------|-----------|-------|
| tsc | ~450 | Full pipeline (parse + check) |
| tsc parse only | ~90 | Estimated 20% of total |
| ecma-rs | ~18 | Parse only |

**Result**: ecma-rs ~5x faster than tsc parsing (estimated)

**Caveat**: TypeScript does full type checking, not apples-to-apples

### vs oxc/swc

Not benchmarked (not installed). Target: within 20% of oxc speed.

## Performance Targets

### Current (Baseline)

- Throughput: 1.5M lines/sec
- Memory: ~20 bytes/line
- TypeScript stdlib: ~45 MB, ~18ms

### Target (After Tier 1 Optimization)

- Throughput: 2-3M lines/sec (30-100% faster)
- Memory: ~15 bytes/line (25% reduction)
- TypeScript stdlib: ~30 MB, <10ms

### Stretch Goal (Match oxc)

- Throughput: 4-5M lines/sec
- Memory: ~10 bytes/line
- TypeScript stdlib: <5ms

## Recommendations

### For Tier 1 (Parser Completion)

**Focus on correctness first**. Don't optimize yet.

**Monitor**: Run benchmarks after major changes to catch regressions.

### For Tier 1 Phase 4 (Performance Optimization)

**Priority 1**: Optimize type_primary (32.5% of time)
- Split large match
- Add fast paths
- Expected gain: 10-15%

**Priority 2**: Add speculation cache (5% of time)
- Memoize is_start_of_type_arguments
- Expected gain: 3-5%

**Priority 3**: Arena allocation (memory + speed)
- Reduce allocations
- Better cache locality
- Expected gain: 15-20%

**Total expected**: 30-40% faster after optimizations

### For Tier 2 (Optimizer)

Performance matters less for type stripping (one-time cost).
Focus on optimization *results* (smaller bundles) not speed.

## Appendix: Benchmark Commands

### Run Benchmarks
```bash
cargo bench --bench baseline_performance
```

### Compare with Baseline
```bash
cargo bench --bench baseline_performance -- --baseline initial
```

### Generate Flamegraph
```bash
cargo flamegraph --bench baseline_performance -- --bench
```

### Profile Memory
```bash
# Linux
valgrind --tool=massif cargo bench --bench baseline_performance

# macOS
cargo instruments -t Allocations --bench baseline_performance
```

### Benchmark Specific Feature
```bash
cargo bench --bench baseline_performance -- union_small
```
```

## Acceptance Criteria

### Required Outputs

✅ **baseline-performance.json**: Quantitative metrics

✅ **performance-report.md**: Analysis and recommendations

✅ **benchmark-results/**: Criterion output

✅ **profiling-data/**: Flamegraph, memory profiles

### Quality Checks

- [ ] Benchmarks run successfully
- [ ] At least 10 different file sizes tested
- [ ] Profiling data collected
- [ ] Hot paths identified
- [ ] Comparison attempted (even if limited)
- [ ] Clear performance targets set

### Success Metrics

- Baseline established
- Bottlenecks identified
- Targets set for optimization
- Regression detection enabled

## Common Issues & Solutions

### Issue: Benchmarks are noisy

**Solution**:
```bash
# Increase warmup and iterations
cargo bench -- --warm-up-time 10 --measurement-time 30
```

### Issue: Can't install flamegraph

**Solution**:
- Linux: Install perf (`sudo apt install linux-tools-generic`)
- macOS: Use Instruments instead
- Windows: Use Visual Studio profiler

### Issue: No comparison parsers available

**Solution**:
- That's OK for baseline
- Note in report
- Can add comparisons later

### Issue: Memory profiling unavailable

**Solution**:
- Use `time -v` for basic RSS: `time -v cargo bench`
- Document limitation
- Estimate from process monitor

## Time Estimate Breakdown

- Setup tools: 30 min
- Create benchmarks: 1 hour
- Run benchmarks: 20 min
- Profiling: 40 min
- Analysis & report: 1 hour

**Total: 2-3 hours**

## Downstream Impact

Provides:
- **Tier 1 Phase 4**: Optimization targets
- **Tier 2**: Performance budget for type-aware features
- **Regression testing**: Compare all future changes

## Notes for Agent

- Don't over-optimize benchmark setup
- Relative performance more important than absolute
- Document system specs (affects numbers)
- Save criterion baseline for future comparison
- Your baseline becomes the reference point

---

**Ready?** Start with Step 1: Create Benchmark Suite
