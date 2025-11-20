# Tier 1: Complete Type Parsing

**Duration**: 3-4 weeks
**Goal**: 100% TypeScript syntax coverage
**Complexity**: Medium
**Value**: HIGH - Foundation for everything else

---

## Overview

Complete the TypeScript parser to handle 100% of valid TypeScript syntax. This is the foundation - everything else builds on this.

**Success Criteria**:
- ✅ Parse >95% of TypeScript conformance tests
- ✅ Match or exceed oxc parser speed
- ✅ Memory usage <50MB for stdlib types
- ✅ Zero panics on fuzz testing

---

## Phase 1.1: Coverage Analysis (Week 1)

### Step 1: Run Conformance Tests

First, fix the conformance test runner dependency:

```bash
cd parse-js
cargo add --dev rayon
cargo test --release conformance_runner
```

Expected output:
```
📊 Found 21,065 test files
🚀 Running tests in parallel...
...
📈 TEST RESULTS SUMMARY
Total tests:  21065
✅ Passed:     18958 (90.00%)
❌ Failed:     2107 (10.00%)
```

**Action**: Examine failure patterns

### Step 2: Categorize Failures

Create analysis tool:

```rust
// parse-js/src/bin/analyze_failures.rs
use std::collections::HashMap;

fn main() {
    let failures = read_failure_report("typescript_conformance_failures.txt");

    let mut by_category = HashMap::new();
    for failure in failures {
        let category = categorize_failure(&failure);
        by_category.entry(category).or_insert(Vec::new()).push(failure);
    }

    // Print top categories
    for (cat, failures) in by_category.iter().sorted_by_key(|(_, v)| v.len()).rev() {
        println!("{}: {} failures", cat, failures.len());
        println!("  Sample: {}", failures[0].path.display());
    }
}

fn categorize_failure(failure: &TestResult) -> FailureCategory {
    if failure.error.contains("TIMEOUT") {
        FailureCategory::Timeout
    } else if failure.error.contains("Expected") {
        FailureCategory::ParserError
    } else if failure.error.contains("PANIC") {
        FailureCategory::Panic
    } else {
        // Parse error message to determine category
        FailureCategory::Unknown
    }
}

enum FailureCategory {
    Timeout,
    ParserError,
    Panic,
    MissingFeature(&'static str),
    Unknown,
}
```

### Step 3: Create Feature Matrix

Document what's implemented vs. what's missing:

```rust
// parse-js/src/features.rs

#[derive(Debug, PartialEq)]
pub enum TSFeatureStatus {
    Implemented,
    Partial,
    Missing,
}

pub struct TSFeatureMatrix {
    features: HashMap<TSFeature, TSFeatureStatus>,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum TSFeature {
    // Base types
    PrimitiveTypes,
    TypeReferences,
    UnionIntersection,

    // Literals
    StringLiterals,
    NumberLiterals,
    TemplateLiterals,

    // Advanced
    ConditionalTypes,
    MappedTypes,
    IndexedAccess,

    // Modifiers
    ReadonlyModifier,
    OptionalModifier,
    RestElements,

    // Declarations
    Interface,
    TypeAlias,
    Enum,
    ConstEnum,
    Namespace,
    Module,

    // TypeScript 5.x
    ConstTypeParameters,
    SatisfiesOperator,
    UsingDeclarations,
    Decorators,

    // Edge cases
    AbstractConstructSignatures,
    PrivateIdentifiersInTypes,
    ImportTypeWithTypeOf,
    // ... etc
}

impl TSFeatureMatrix {
    pub fn check_codebase() -> Self {
        // Analyze AST and parser to determine what's implemented
        unimplemented!()
    }

    pub fn prioritize_missing(&self) -> Vec<(TSFeature, Priority)> {
        // Return missing features sorted by priority
        unimplemented!()
    }
}
```

**Deliverable**: `typescript_coverage_report.md` with:
- Current pass rate
- Missing features prioritized by frequency
- Sample failing test cases for each category

---

## Phase 1.2: Fill the Gaps (Week 2-3)

### Common Missing Features (Likely)

Based on TypeScript evolution and edge cases:

#### 1. Readonly Tuple with Rest Elements

```typescript
type T = readonly [string, ...number[]];
type U = readonly [first: string, ...rest: number[]];
```

**Implementation**:
```rust
// parse-js/src/parse/type_expr.rs

fn tuple_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let readonly = if self.peek().typ == TT::KeywordReadonly {
        self.consume();
        true
    } else {
        false
    };

    self.require(TT::BracketOpen)?;

    let mut elements = Vec::new();
    while self.peek().typ != TT::BracketClose {
        elements.push(self.tuple_element(ctx)?);

        if !self.consume_if(TT::Comma).is_match() {
            break;
        }
    }

    self.require(TT::BracketClose)?;

    Ok(Node::new(
        start_loc,
        TypeExpr::TupleType(Node::new(start_loc, TypeTuple {
            readonly,
            elements,
        })),
    ))
}
```

**Test**:
```rust
#[test]
fn test_readonly_tuple_with_rest() {
    let src = r#"type T = readonly [string, ...number[]];"#;
    let ast = parse(src).unwrap();

    // Assert AST structure
    assert!(matches!(
        ast.statements[0],
        Stmt::TypeAlias(TypeAliasDecl {
            type_expr: TypeExpr::TupleType(TypeTuple {
                readonly: true,
                elements: ...
            })
        })
    ));
}
```

#### 2. Import Type with Typeof

```typescript
type T = typeof import("./module");
type U = typeof import("./module").default;
```

**Implementation**:
```rust
fn type_query(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    self.require(TT::KeywordTypeof)?;

    let expr_name = if self.peek().typ == TT::KeywordImport {
        // typeof import(...)
        let import_expr = self.import_call(ctx)?;
        TypeEntityName::Import(import_expr)
    } else {
        self.parse_type_entity_name()?
    };

    // Handle .property after import
    while self.consume_if(TT::Dot).is_match() {
        let property = self.require_identifier()?;
        // Extend expr_name with property access
    }

    Ok(Node::new(start_loc, TypeExpr::TypeQuery(Node::new(start_loc, TypeQuery {
        expr_name,
    }))))
}
```

#### 3. Abstract Constructor Signatures

```typescript
interface Foo {
    abstract new (...args: any[]): any;
}
```

**Implementation**:
```rust
// parse-js/src/parse/type_expr.rs

fn type_member(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeMember>> {
    // Check for 'abstract' keyword before 'new'
    let abstract_ = self.consume_if(TT::KeywordAbstract).is_match();

    if abstract_ && self.peek().typ == TT::KeywordNew {
        // Abstract constructor signature
        return self.construct_signature(ctx, true);
    }

    // ... rest of implementation
}

fn construct_signature(
    &mut self,
    ctx: ParseCtx,
    abstract_: bool
) -> SyntaxResult<Node<TypeMember>> {
    // Add abstract field to TypeConstructSignature if needed
    // or encode in flags
}
```

#### 4. `-?` and `+?` Modifiers in Mapped Types

```typescript
type Required<T> = { [K in keyof T]-?: T[K] };
type Partial<T> = { [K in keyof T]+?: T[K] };
```

**Already implemented!** ✅ (Check `parse_mapped_type_modifier`)

#### 5. `satisfies` Operator

```typescript
const config = {
    apiUrl: "https://api.com",
    timeout: 5000,
} satisfies Config;
```

**Check if implemented**:
```rust
// Search for:
// parse-js/src/ast/expr/mod.rs - SatisfiesExpr
// parse-js/src/parse/expr/mod.rs - parsing logic
```

Likely already done, verify with test.

### Systematic Implementation Process

For each missing feature:

#### Step 1: Write Failing Test
```rust
#[test]
fn test_feature_name() {
    let src = r#"<TypeScript source using feature>"#;
    let result = parse(src);

    // Currently fails
    assert!(result.is_err());
}
```

#### Step 2: Extend AST (if needed)
```rust
// parse-js/src/ast/type_expr.rs

#[derive(Debug, Serialize)]
pub struct NewTypeConstruct {
    pub field1: Type1,
    pub field2: Type2,
}

// Add variant to TypeExpr
pub enum TypeExpr {
    // ...existing variants
    NewConstruct(Node<NewTypeConstruct>),
}
```

#### Step 3: Implement Parser
```rust
// parse-js/src/parse/type_expr.rs

fn parse_new_construct(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    // Implementation
}

// Add to type_primary or appropriate place
fn type_primary(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    match self.peek().typ {
        // ... existing cases
        TT::TriggerTokenForNewFeature => self.parse_new_construct(ctx),
        // ...
    }
}
```

#### Step 4: Update Visitor (if needed)
```rust
// Ensure derive_visitor macros work correctly
// Test traversal
```

#### Step 5: Verify Test Passes
```rust
#[test]
fn test_feature_name() {
    let src = r#"<TypeScript source using feature>"#;
    let ast = parse(src).unwrap();  // Should pass now

    // Assert correct AST structure
    assert!(matches!(ast.statements[0], Stmt::...));
}
```

#### Step 6: Run Conformance Tests
```bash
cargo test --release conformance_runner
```

Watch pass rate increase!

---

## Phase 1.3: Parser Performance Optimization (Week 4)

### Benchmarking Setup

```rust
// benches/type_parsing.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use parse_js::parse;

fn bench_type_parsing(c: &mut Criterion) {
    let samples = vec![
        ("primitive", "type T = string"),
        ("union_small", "type T = A | B | C"),
        ("union_large", "type T = A | B | C | D | E | F | G | H | I | J"),
        ("mapped", "type T = { [K in keyof O]: O[K] }"),
        ("conditional", "type T = A extends B ? C : D"),
        ("nested_conditional",
         "type T = A extends B ? C extends D ? E : F : G extends H ? I : J"),
        ("react_types", include_str!("../samples/react.d.ts")),
        ("typescript_lib", include_str!("../samples/lib.d.ts")),
        ("vscode_api", include_str!("../samples/vscode.d.ts")),
    ];

    let mut group = c.benchmark_group("type_parsing");
    for (name, src) in samples {
        group.bench_with_input(BenchmarkId::from_parameter(name), &src, |b, &src| {
            b.iter(|| parse(black_box(src)))
        });
    }
    group.finish();
}

criterion_group!(benches, bench_type_parsing);
criterion_main!(benches);
```

Run baseline:
```bash
cargo bench --bench type_parsing
```

### Optimization 1: Hot Path Analysis

Use profiling to find hot paths:

```bash
cargo install cargo-flamegraph
cargo flamegraph --bench type_parsing -- --bench
```

Look for:
- Token consumption (likely hot)
- Type expression allocation
- String copying
- Backtracking in is_start_of_type_arguments

### Optimization 2: Reduce Allocations

**Before**:
```rust
pub struct TypeUnion {
    pub types: Vec<Node<TypeExpr>>,  // Heap allocation per union
}
```

**After (if using arena)**:
```rust
pub struct Parser<'src, 'ast> {
    arena: &'ast Bump,
}

pub struct TypeUnion<'ast> {
    pub types: &'ast [Node<TypeExpr>],  // Arena-allocated slice
}

impl<'src, 'ast> Parser<'src, 'ast> {
    fn parse_union(&mut self) -> &'ast TypeUnion<'ast> {
        let mut types = Vec::new();  // Temp vec
        // ... parse types

        // Copy to arena
        let types_slice = self.arena.alloc_slice_copy(&types);

        self.arena.alloc(TypeUnion {
            types: types_slice,
        })
    }
}
```

**Consideration**: This requires threading lifetime through entire codebase. Major refactor.

**Alternative**: Use `bumpalo::collections::Vec` directly:
```rust
use bumpalo::collections::Vec as BumpVec;

impl Parser {
    fn parse_union(&mut self) -> TypeUnion {
        let types = BumpVec::with_capacity_in(4, &self.arena);
        // ... parse into BumpVec

        TypeUnion { types }
    }
}
```

### Optimization 3: Fast Path for Common Cases

```rust
fn type_primary_fast(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    // Fast path: common keywords
    match self.peek().typ {
        TT::KeywordString => {
            let loc = self.consume().loc;
            return Ok(Node::new(loc, TypeExpr::String(Node::new(loc, TypeString {}))));
        }
        TT::KeywordNumber => {
            let loc = self.consume().loc;
            return Ok(Node::new(loc, TypeExpr::Number(Node::new(loc, TypeNumber {}))));
        }
        // ... other primitives

        _ => self.type_primary_slow(ctx),  // Slow path
    }
}
```

### Optimization 4: Memoize Speculation

Currently `is_start_of_type_arguments()` scans tokens, then `type_arguments()` scans again.

**Optimization**: Cache the lookahead result

```rust
pub struct Parser<'src> {
    // ... existing fields
    speculation_cache: RefCell<HashMap<usize, Option<Vec<TypeExpr>>>>,
}

impl Parser {
    fn type_arguments_with_cache(&mut self) -> Option<Vec<TypeExpr>> {
        let pos = self.pos();

        // Check cache
        if let Some(cached) = self.speculation_cache.borrow().get(&pos) {
            return cached.clone();
        }

        // Try parse
        let checkpoint = self.checkpoint();
        let result = match self.try_parse_type_arguments() {
            Ok(args) => Some(args),
            Err(_) => {
                self.restore(checkpoint);
                None
            }
        };

        // Cache result
        self.speculation_cache.borrow_mut().insert(pos, result.clone());

        result
    }
}
```

### Target Performance

Compare with oxc:

```bash
# Clone oxc
git clone https://github.com/oxc-project/oxc
cd oxc

# Run their benchmarks
cargo bench --package oxc_parser

# Compare with ours
cd ../ecma-rs
cargo bench --bench type_parsing
```

**Target**: Within 20% of oxc

---

## Deliverables

### Week 1
- ✅ Conformance test results
- ✅ Coverage analysis report
- ✅ Prioritized feature list

### Week 2-3
- ✅ All high-priority features implemented
- ✅ Tests passing
- ✅ Conformance pass rate >95%

### Week 4
- ✅ Performance benchmarks
- ✅ Optimizations implemented
- ✅ Performance within 20% of oxc

### Final
- ✅ Production-ready TypeScript parser
- ✅ Zero known panics
- ✅ Comprehensive test coverage
- ✅ Documentation updated

---

**Next**: [TIER2-OPTIMIZER.md](TIER2-OPTIMIZER.md) - Type-aware minification
