---
task_id: "05-optimization/01-arena-allocation"
title: "Implement Arena Allocation for AST"
phase: "optimization"
estimated_duration: "12-20 hours"
complexity: "high"
dependencies:
  - "04-validation/01-run-conformance"
inputs:
  - "../../04-validation/01-run-conformance/performance-baseline.json"
  - "../../04-validation/03-benchmark-performance/benchmark-results.json"
outputs:
  - "implementation-notes.md"
  - "performance-comparison.md"
  - "memory-analysis.md"
  - "migration-guide.md"
  - "git-patch.diff"
skills_required:
  - "Rust expert"
  - "Memory management"
  - "Performance engineering"
  - "Lifetimes & borrowing"
---

# Task: Implement Arena Allocation for AST

## Objective

Replace heap allocations (Vec, Box, etc.) with arena allocation using `bumpalo` to improve:
- **Parsing speed**: 20-40% faster allocation
- **Memory efficiency**: Better cache locality
- **Deallocation**: O(1) instead of traversing tree

## Context

### Why Arena Allocation?

**Current approach**: Each AST node allocates individually
```rust
pub struct TypeUnion {
    pub types: Vec<Node<TypeExpr>>,  // Heap allocation
}
```

**Problem**:
- Each `Vec` is a separate heap allocation
- Scattered in memory (poor cache locality)
- Deallocation requires traversing entire tree

**Arena approach**: All nodes in one contiguous block
```rust
pub struct TypeUnion<'ast> {
    pub types: &'ast [Node<TypeExpr>],  // Arena slice
}
```

**Benefits**:
- All nodes allocated from same memory region
- Better cache locality → faster parsing
- Drop entire arena at once → faster cleanup
- Proven: oxc uses this, 3x faster than swc

### Trade-offs

**Pros**:
- 20-40% faster parsing (measured in oxc)
- Lower memory fragmentation
- Simpler cleanup

**Cons**:
- Adds lifetime parameters throughout codebase
- Cannot free individual nodes
- Complexity: lifetimes can be tricky
- Breaking change: affects all downstream code

## Prerequisites

### Files to Modify

1. **AST definitions**: `parse-js/src/ast/*.rs`
   - Add `'ast` lifetime to structs
   - Change `Vec<T>` to `&'ast [T]`
   - Change `Box<T>` to `&'ast T`

2. **Parser**: `parse-js/src/parse/*.rs`
   - Thread arena through parser
   - Allocate from arena instead of heap

3. **Node wrapper**: `parse-js/src/ast/node.rs`
   - Add lifetime to `Node<T>`

### Dependencies

Add to `parse-js/Cargo.toml`:
```toml
[dependencies]
bumpalo = { version = "3.14", features = ["collections"] }
```

### Research

Study oxc's approach:
```rust
// oxc_allocator
pub struct Allocator {
    bump: Bump,
}

impl Allocator {
    pub fn alloc<T>(&self, val: T) -> &T {
        self.bump.alloc(val)
    }

    pub fn alloc_slice_copy<T: Copy>(&self, slice: &[T]) -> &[T] {
        self.bump.alloc_slice_copy(slice)
    }
}

// Usage in parser
pub struct Parser<'a> {
    allocator: &'a Allocator,
}

impl<'a> Parser<'a> {
    fn parse_union(&mut self) -> &'a TypeUnion<'a> {
        let types = vec![...];  // Temp vec
        let types_slice = self.allocator.alloc_slice_copy(&types);
        self.allocator.alloc(TypeUnion { types: types_slice })
    }
}
```

## Instructions

### Step 1: Design Phase

**Create design document first**: `design/arena-allocation.md`

Key decisions:
1. **Lifetime naming**: Use `'ast` throughout
2. **Allocator struct**: Wrap `bumpalo::Bump` or use directly?
3. **Migration strategy**: All at once or incremental?
4. **Backward compatibility**: Can we keep old API?

**Recommended**:
- Use `'ast` lifetime consistently
- Create `Arena` wrapper type
- Migrate incrementally (start with TypeExpr)
- No backward compat (breaking change)

### Step 2: Implement Arena Type

Create `parse-js/src/arena.rs`:

```rust
use bumpalo::Bump;

pub struct Arena {
    bump: Bump,
}

impl Arena {
    pub fn new() -> Self {
        Arena {
            bump: Bump::new(),
        }
    }

    pub fn alloc<T>(&self, val: T) -> &T {
        self.bump.alloc(val)
    }

    pub fn alloc_slice_copy<T: Copy>(&self, slice: &[T]) -> &[T] {
        self.bump.alloc_slice_copy(slice)
    }

    // For non-Copy types, use BumpVec
    pub fn alloc_vec<T>(&self, vec: Vec<T>) -> &[T] {
        self.bump.alloc_slice_fill_iter(vec.into_iter())
    }
}
```

### Step 3: Update AST Nodes (Incremental)

Start with `TypeExpr` as proof of concept:

**Before** (`parse-js/src/ast/type_expr.rs`):
```rust
#[derive(Debug, Serialize)]
pub struct TypeUnion {
    pub types: Vec<Node<TypeExpr>>,
}
```

**After**:
```rust
#[derive(Debug, Serialize)]
pub struct TypeUnion<'ast> {
    pub types: &'ast [Node<TypeExpr>],
}

// Update TypeExpr enum
pub enum TypeExpr<'ast> {
    Union(Node<TypeUnion<'ast>>),
    Intersection(Node<TypeIntersection<'ast>>),
    // ... all variants now have 'ast lifetime
}
```

### Step 4: Update Parser

**Before**:
```rust
pub struct Parser<'src> {
    lexer: Lexer<'src>,
}

impl<'src> Parser<'src> {
    fn parse_union(&mut self) -> TypeUnion {
        let mut types = Vec::new();
        // ... parse ...
        TypeUnion { types }
    }
}
```

**After**:
```rust
pub struct Parser<'src, 'ast> {
    lexer: Lexer<'src>,
    arena: &'ast Arena,
}

impl<'src, 'ast> Parser<'src, 'ast> {
    fn parse_union(&mut self) -> &'ast TypeUnion<'ast> {
        let mut types = Vec::new();  // Temp vec
        // ... parse into types ...

        let types_slice = self.arena.alloc_vec(types);
        self.arena.alloc(TypeUnion { types: types_slice })
    }
}
```

### Step 5: Update Public API

**Before** (`parse-js/src/lib.rs`):
```rust
pub fn parse(source: &str) -> SyntaxResult<Node<TopLevel>> {
    let lexer = Lexer::new(source);
    let mut parser = Parser::new(lexer);
    parser.parse_top_level()
}
```

**After**:
```rust
pub fn parse(source: &str) -> SyntaxResult<ParsedOutput> {
    let arena = Arena::new();
    let lexer = Lexer::new(source);
    let mut parser = Parser::new(lexer, &arena);
    let ast = parser.parse_top_level()?;

    Ok(ParsedOutput {
        arena,  // Keep arena alive!
        ast,
    })
}

pub struct ParsedOutput<'ast> {
    arena: Arena,
    ast: &'ast Node<TopLevel<'ast>>,
}

impl<'ast> ParsedOutput<'ast> {
    pub fn ast(&self) -> &Node<TopLevel<'ast>> {
        self.ast
    }
}
```

**Critical**: Arena must live as long as AST!

### Step 6: Comprehensive Testing

```rust
#[test]
fn test_arena_allocation_basic() {
    let src = "type T = A | B | C;";
    let result = parse(src);
    assert!(result.is_ok());

    let output = result.unwrap();
    // AST is valid while output is alive
    let ast = output.ast();
    assert!(matches!(ast.statements[0], Stmt::TypeAlias(_)));
}

#[test]
fn test_arena_lifetime_correctness() {
    let output = {
        let src = String::from("type T = number;");
        parse(&src).unwrap()
    }; // src dropped here

    // AST still valid (arena owns memory)
    let ast = output.ast();
    assert!(matches!(ast.statements[0], Stmt::TypeAlias(_)));
}

#[test]
fn test_large_ast() {
    // Test with deeply nested types
    let src = "type T = ".to_string() + &"A | ".repeat(1000) + "Z;";
    let result = parse(&src);
    assert!(result.is_ok());
}
```

### Step 7: Benchmark

```rust
// benches/arena_vs_heap.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_without_arena(c: &mut Criterion) {
    // Use old implementation (save as parse_old)
    let src = include_str!("samples/large-types.ts");

    c.bench_function("heap_allocation", |b| {
        b.iter(|| parse_old(black_box(src)))
    });
}

fn bench_with_arena(c: &mut Criterion) {
    let src = include_str!("samples/large-types.ts");

    c.bench_function("arena_allocation", |b| {
        b.iter(|| parse(black_box(src)))
    });
}

criterion_group!(benches, bench_without_arena, bench_with_arena);
criterion_main!(benches);
```

Run benchmarks:
```bash
cargo bench --bench arena_vs_heap
```

Expected: 20-40% improvement

### Step 8: Memory Analysis

Use Valgrind or similar to measure:

```bash
# Before arena
valgrind --tool=massif --massif-out-file=massif.out.before \
    cargo run --release --bin parse_bench

# After arena
valgrind --tool=massif --massif-out-file=massif.out.after \
    cargo run --release --bin parse_bench

# Compare
ms_print massif.out.before > memory_before.txt
ms_print massif.out.after > memory_after.txt
```

Measure:
- Peak memory usage
- Allocation count
- Cache misses (with perf)

### Step 9: Document Migration

Create `migration-guide.md`:

```markdown
# Arena Allocation Migration Guide

## Breaking Changes

### API Change

**Before**:
```rust
let ast = parse_js::parse(source)?;
// ast: Node<TopLevel>
```

**After**:
```rust
let output = parse_js::parse(source)?;
let ast = output.ast();
// output: ParsedOutput<'ast>
// ast: &'ast Node<TopLevel<'ast>>
```

### Lifetime Requirements

All AST traversal code now needs `'ast` lifetime:

**Before**:
```rust
fn visit_type(ty: &TypeExpr) { ... }
```

**After**:
```rust
fn visit_type<'ast>(ty: &TypeExpr<'ast>) { ... }
```

## Migration Checklist

Downstream users must:
- [ ] Update parse() call to handle ParsedOutput
- [ ] Add 'ast lifetime to visitor functions
- [ ] Ensure ParsedOutput lives long enough
- [ ] Update tests

## Benefits

- 20-40% faster parsing
- Lower memory usage
- Better cache locality

## Rollout Plan

1. Release as 0.25.0 (breaking change)
2. Update all internal uses first
3. Provide migration examples
4. Support questions in GitHub discussions
```

## Acceptance Criteria

### Required Outputs

✅ **implementation-notes.md**: Technical details

✅ **performance-comparison.md**: Before/after benchmarks

✅ **memory-analysis.md**: Memory usage comparison

✅ **migration-guide.md**: User-facing documentation

✅ **git-patch.diff**: Complete implementation

### Quality Checks

- [ ] All tests pass
- [ ] No memory leaks (valgrind clean)
- [ ] 20%+ performance improvement
- [ ] Lifetimes compile correctly
- [ ] Backward compat documented (breaking change acknowledged)

### Success Metrics

- Parsing speed: >20% faster
- Memory usage: Lower or equal
- Code quality: No warnings
- Ready for production

## Common Issues & Solutions

### Issue: Lifetime errors everywhere
**Diagnosis**: Forgot to add 'ast to some struct
**Solution**: Systematically add 'ast to all AST types

### Issue: "borrowed value does not live long enough"
**Diagnosis**: Arena dropped before AST used
**Solution**: Ensure ParsedOutput owns arena

### Issue: Performance worse, not better
**Diagnosis**: Too many temporary Vecs, not using arena
**Solution**: Profile to find heap allocations

### Issue: Serialize fails with lifetimes
**Diagnosis**: Serde doesn't like `&'ast [T]`
**Solution**: Use `#[serde(borrow)]` or custom serializer

## Time Estimate Breakdown

- Design & research: 3 hours
- Implement Arena type: 1 hour
- Update AST nodes: 4 hours
- Update parser: 4 hours
- Fix lifetime errors: 3 hours (inevitable!)
- Testing: 2 hours
- Benchmarking: 1 hour
- Documentation: 2 hours

**Total: 12-20 hours**

## Downstream Impact

This optimization:
- Improves parser performance significantly
- Sets foundation for further optimizations
- Demonstrates Rust expertise
- Matches oxc's architecture

## Notes for Agent

- This is HARD - lifetimes are tricky
- Take breaks when frustrated with lifetime errors
- Incremental approach: start with TypeExpr only
- Don't optimize prematurely - measure first
- Document every decision

---

**Ready?** Start with Step 1: Design Phase
