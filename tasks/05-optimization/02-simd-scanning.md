---
task_id: "05-optimization/02-simd-scanning"
phase: "05-optimization"
title: "Implement SIMD Token Scanning"
dependencies:
  - "04-validation/03-benchmark-performance"
inputs:
  - "workspace/outputs/04-validation/03-benchmark-performance/final-performance.json"
  - "parse-js/src/lex/mod.rs"
outputs:
  - "parse-js/src/lex/simd.rs"
  - "workspace/outputs/05-optimization/02-simd-scanning/optimization-report.md"
  - "workspace/outputs/05-optimization/02-simd-scanning/performance-comparison.json"
estimated_duration: "8-12 hours"
complexity: "high"
priority: "medium"
---

# Task: Implement SIMD Token Scanning

## Objective

Implement SIMD (Single Instruction Multiple Data) optimizations for hot paths in the lexer, particularly for:
- Whitespace skipping
- Identifier scanning
- String literal scanning
- Comment skipping

Target: 15-30% lexer speedup

## Context

SIMD allows processing multiple bytes in parallel using special CPU instructions. Modern CPUs (x86-64, ARM) support 128-bit or 256-bit SIMD operations.

### Why SIMD for Lexing?

Lexing involves many character-by-character operations that are embarrassingly parallel:
- Skipping runs of whitespace
- Checking if characters are alphanumeric
- Finding string terminators
- Detecting newlines

### Prior Art

- **oxc**: Uses SIMD for identifier scanning
- **simdjson**: Fast JSON parsing with SIMD
- **memchr crate**: SIMD-accelerated substring search

## Instructions

### Step 1: Profile Current Lexer

Identify hot spots:

```bash
# Install cargo-flamegraph
cargo install flamegraph

# Profile lexer
cargo flamegraph --bench parser_bench -- --bench

# Open flamegraph.svg to see hot functions
```

Expected hot spots:
- `skip_whitespace()`
- `scan_identifier()`
- `scan_string()`

### Step 2: Set Up SIMD Dependencies

**File**: `Cargo.toml`

```toml
[dependencies]
# Portable SIMD (works on stable Rust)
simd-abstraction = "0.7"

# Or use std::simd (requires nightly)
# [features]
# default = []
# simd = []

[target.'cfg(any(target_arch = "x86", target_arch = "x86_64"))'.dependencies]
# x86-specific SIMD
```

### Step 3: Implement SIMD Whitespace Skipping

**File**: `parse-js/src/lex/simd.rs`

```rust
use std::arch::x86_64::*;

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sse2")]
unsafe fn skip_whitespace_simd(bytes: &[u8], mut pos: usize) -> usize {
    const SPACE: u8 = b' ';
    const TAB: u8 = b'\t';
    const LF: u8 = b'\n';
    const CR: u8 = b'\r';

    // SIMD registers hold 16 bytes (SSE2) or 32 bytes (AVX2)
    const SIMD_WIDTH: usize = 16;

    // Process 16 bytes at a time
    while pos + SIMD_WIDTH <= bytes.len() {
        // Load 16 bytes
        let chunk = _mm_loadu_si128(bytes.as_ptr().add(pos) as *const __m128i);

        // Create comparison vectors
        let spaces = _mm_set1_epi8(SPACE as i8);
        let tabs = _mm_set1_epi8(TAB as i8);
        let lfs = _mm_set1_epi8(LF as i8);
        let crs = _mm_set1_epi8(CR as i8);

        // Compare chunk against each whitespace character
        let eq_space = _mm_cmpeq_epi8(chunk, spaces);
        let eq_tab = _mm_cmpeq_epi8(chunk, tabs);
        let eq_lf = _mm_cmpeq_epi8(chunk, lfs);
        let eq_cr = _mm_cmpeq_epi8(chunk, crs);

        // OR all comparisons together
        let is_ws = _mm_or_si128(
            _mm_or_si128(eq_space, eq_tab),
            _mm_or_si128(eq_lf, eq_cr),
        );

        // Convert to bitmask
        let mask = _mm_movemask_epi8(is_ws) as u16;

        // If not all bits set, we found non-whitespace
        if mask != 0xFFFF {
            // Find first zero bit (non-whitespace)
            let first_non_ws = mask.trailing_ones() as usize;
            return pos + first_non_ws;
        }

        pos += SIMD_WIDTH;
    }

    // Handle remaining bytes with scalar code
    scalar_skip_whitespace(bytes, pos)
}

fn scalar_skip_whitespace(bytes: &[u8], mut pos: usize) -> usize {
    while pos < bytes.len() {
        match bytes[pos] {
            b' ' | b'\t' | b'\n' | b'\r' => pos += 1,
            _ => break,
        }
    }
    pos
}

/// Public API that dispatches to SIMD or scalar version
pub fn skip_whitespace(bytes: &[u8], pos: usize) -> usize {
    #[cfg(target_arch = "x86_64")]
    {
        if is_x86_feature_detected!("sse2") {
            return unsafe { skip_whitespace_simd(bytes, pos) };
        }
    }

    // Fallback to scalar
    scalar_skip_whitespace(bytes, pos)
}
```

### Step 4: Implement SIMD Identifier Scanning

```rust
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sse2")]
unsafe fn is_identifier_char_simd(bytes: &[u8], start: usize, end: usize) -> bool {
    let mut pos = start;
    const SIMD_WIDTH: usize = 16;

    while pos + SIMD_WIDTH <= end {
        let chunk = _mm_loadu_si128(bytes.as_ptr().add(pos) as *const __m128i);

        // Check if all characters are alphanumeric, underscore, or dollar
        let is_alpha_lower = _mm_and_si128(
            _mm_cmpgt_epi8(chunk, _mm_set1_epi8(b'a' as i8 - 1)),
            _mm_cmplt_epi8(chunk, _mm_set1_epi8(b'z' as i8 + 1)),
        );

        let is_alpha_upper = _mm_and_si128(
            _mm_cmpgt_epi8(chunk, _mm_set1_epi8(b'A' as i8 - 1)),
            _mm_cmplt_epi8(chunk, _mm_set1_epi8(b'Z' as i8 + 1)),
        );

        let is_digit = _mm_and_si128(
            _mm_cmpgt_epi8(chunk, _mm_set1_epi8(b'0' as i8 - 1)),
            _mm_cmplt_epi8(chunk, _mm_set1_epi8(b'9' as i8 + 1)),
        );

        let is_underscore = _mm_cmpeq_epi8(chunk, _mm_set1_epi8(b'_' as i8));
        let is_dollar = _mm_cmpeq_epi8(chunk, _mm_set1_epi8(b'$' as i8));

        // Combine all valid characters
        let is_valid = _mm_or_si128(
            _mm_or_si128(is_alpha_lower, is_alpha_upper),
            _mm_or_si128(
                is_digit,
                _mm_or_si128(is_underscore, is_dollar),
            ),
        );

        let mask = _mm_movemask_epi8(is_valid);

        // If not all bits set, found invalid character
        if mask != 0xFFFF {
            return false;
        }

        pos += SIMD_WIDTH;
    }

    // Check remaining bytes scalar
    for &b in &bytes[pos..end] {
        if !is_identifier_char_scalar(b) {
            return false;
        }
    }

    true
}

fn is_identifier_char_scalar(b: u8) -> bool {
    matches!(b, b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_' | b'$')
}
```

### Step 5: Integrate into Lexer

**File**: `parse-js/src/lex/mod.rs`

```rust
mod simd;

impl<'a> Lexer<'a> {
    fn skip_whitespace(&mut self) {
        self.pos = simd::skip_whitespace(self.source.as_bytes(), self.pos);
    }

    fn scan_identifier(&mut self) -> Token {
        let start = self.pos;

        // First character must be letter, underscore, or dollar
        if !self.is_identifier_start(self.peek()) {
            panic!("Not an identifier");
        }

        self.pos += 1;

        // Scan rest of identifier
        while self.pos < self.source.len() {
            if !simd::is_identifier_char(self.source.as_bytes(), self.pos) {
                break;
            }
            self.pos += 1;
        }

        let name = &self.source[start..self.pos];

        // Check if keyword
        if let Some(keyword) = self.check_keyword(name) {
            Token::new(keyword, name.to_string(), self.loc(start))
        } else {
            Token::new(TokenType::Identifier, name.to_string(), self.loc(start))
        }
    }
}
```

### Step 6: Benchmark SIMD vs Scalar

**File**: `benches/simd_bench.rs`

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use parse_js::lex::simd;

fn bench_whitespace_skipping(c: &mut Criterion) {
    let samples = vec![
        ("short", "   \t\n   code"),
        ("medium", " ".repeat(100) + "code"),
        ("long", " ".repeat(1000) + "code"),
    ];

    let mut group = c.benchmark_group("whitespace_skip");

    for (name, input) in samples {
        group.bench_with_input(
            BenchmarkId::new("simd", name),
            &input,
            |b, s| {
                b.iter(|| {
                    simd::skip_whitespace(black_box(s.as_bytes()), 0)
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("scalar", name),
            &input,
            |b, s| {
                b.iter(|| {
                    simd::skip_whitespace_scalar(black_box(s.as_bytes()), 0)
                });
            },
        );
    }

    group.finish();
}

criterion_group!(benches, bench_whitespace_skipping);
criterion_main!(benches);
```

```bash
cargo bench --bench simd_bench
```

### Step 7: Measure Overall Impact

```bash
# Benchmark full parser with SIMD optimizations
cargo bench --bench parser_bench -- --save-baseline with-simd

# Compare with baseline
cargo bench --bench parser_bench -- --baseline post-impl --baseline with-simd
```

### Step 8: Create Optimization Report

**File**: `workspace/outputs/05-optimization/02-simd-scanning/optimization-report.md`

```markdown
# SIMD Token Scanning Optimization Report

## Summary

Implemented SIMD optimizations for lexer hot paths.

**Performance improvement**: X% faster lexing

## Changes Made

### Functions Optimized

1. **skip_whitespace()**: X% faster
2. **scan_identifier()**: Y% faster
3. **scan_string()**: Z% faster (if implemented)

### SIMD Instructions Used

- SSE2 (128-bit, baseline x86-64)
- AVX2 (256-bit, if available)
- NEON (ARM, if implemented)

## Benchmark Results

| Function | Scalar | SIMD | Speedup |
|----------|--------|------|---------|
| skip_whitespace | X ms | Y ms | Z.Zx |
| scan_identifier | X ms | Y ms | Z.Zx |
| Overall lexing | X ms | Y ms | Z.Zx |

## Full Parser Impact

- **Before SIMD**: X ms (average)
- **After SIMD**: Y ms (average)
- **Improvement**: Z% faster

## Platform Support

- ✅ x86-64 (SSE2, AVX2)
- ✅ x86 (SSE2)
- ❌ ARM (NEON) - not implemented
- ✅ Fallback scalar code for unsupported platforms

## Code Complexity

- **Lines added**: X
- **New dependencies**: simd-abstraction
- **Maintenance cost**: Low (isolated in simd.rs module)

## Trade-offs

**Pros**:
- Significant speedup for long whitespace runs
- Minimal code complexity
- Portable with fallback

**Cons**:
- Requires unsafe code
- Platform-specific testing needed
- Marginal benefit for short inputs

## Recommendations

- ✅ Keep whitespace skipping SIMD
- ⚠️ Identifier scanning SIMD - benefit unclear
- ❓ Consider SIMD for string scanning

## Future Optimizations

- [ ] Implement AVX-512 for newer CPUs
- [ ] Add ARM NEON support
- [ ] Explore SIMD for JSON-like structures
```

## Common Issues

### Issue 1: SIMD Not Available
**Solution**: Always provide scalar fallback

### Issue 2: Alignment Issues
**Solution**: Use `loadu` (unaligned load) instead of `load`

### Issue 3: Platform-Specific Bugs
**Solution**: Extensive testing on different CPUs

## Acceptance Criteria

- [ ] SIMD whitespace skipping implemented
- [ ] Scalar fallback works
- [ ] Benchmarks show >10% improvement
- [ ] All tests pass on x86-64
- [ ] No regressions on ARM/fallback
- [ ] Optimization report created

## Success Metrics

**Minimum**: 10% lexer speedup
**Target**: 20% lexer speedup
**Exceptional**: 30%+ speedup

## Resources

- std::arch docs: https://doc.rust-lang.org/std/arch/
- SIMD tutorial: https://rust-lang.github.io/packed_simd/perf-guide/
- simdjson paper: https://arxiv.org/abs/1902.08318
