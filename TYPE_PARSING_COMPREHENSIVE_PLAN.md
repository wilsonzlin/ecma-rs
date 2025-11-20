# TypeScript Type Parsing: Comprehensive Architecture & Implementation Plan

> **Mission**: Design and implement a blazingly fast, modern, elegant TypeScript type system for ecma-rs that leverages Rust's performance while learning from TypeScript's 12-year evolution and the cutting-edge innovations in typescript-go, oxc, and modern type theory.

---

## Executive Summary

### Current State Assessment

**✅ ALREADY IMPLEMENTED** (Excellent Foundation!):
- **Complete TypeScript type expression AST** (~427 lines, `type_expr.rs`)
- **Full type expression parser** (~1,743 lines, `parse/type_expr.rs`)
- **TypeScript declarations**: interfaces, type aliases, enums, namespaces, modules
- **Type annotations**: variables, functions, parameters, class members, return types
- **Advanced types**: conditional, mapped, template literal, indexed access
- **Type operators**: typeof, keyof, infer, readonly, unique symbol
- **Variance annotations**: in, out, in out
- **Type predicates** and **assertion signatures**
- **21,065 TypeScript test files** from microsoft/TypeScript repo
- **Conformance test runner** with parallel execution

**🎯 PROJECT GOAL**: JavaScript minification (NOT type checking)
- Parse TypeScript → Strip types → Minify JavaScript
- Type checking is out of scope for minification
- BUT: Type-aware optimizations could unlock next-level minification

### The Three Paths Forward

1. **Path A: Type-Preserving Parser** (Status Quo Enhancement)
   - Complete the type parsing for 100% TypeScript syntax coverage
   - Strip types during minification
   - Focus: Speed, correctness, completeness

2. **Path B: Type-Aware Optimizer** (Advanced Minification)
   - Add lightweight type inference for dead code elimination
   - Use type information to enable aggressive optimizations
   - No full type checking, just enough to minify better

3. **Path C: Full Type System** (Moonshot)
   - Implement complete bidirectional type checking
   - Build the "TypeScript killer" - 100x faster, written in Rust
   - Enable ecosystem tooling: IDE support, linting, etc.

**RECOMMENDATION**: Start with Path A (complete), layer on Path B (innovate), keep Path C as a north star (inspire).

---

## I. DEEP DIVE: What IS Type Parsing?

### Philosophical Foundation

Type parsing exists at the intersection of:
- **Syntax**: Recognizing `function f<T>(x: T): T` as valid TypeScript
- **Semantics**: Understanding what `T` means in different contexts
- **Pragmatics**: Enabling tools to use type information effectively

### The Spectrum of Type Systems

```
Parsing ──────► Binding ──────► Checking ──────► Inference ──────► Proving
   ▲                ▲                ▲                 ▲                ▲
   │                │                │                 │                │
 You are        Scope &         Type             Bidirectional      Formal
 here now      Symbols       Relations           Flow Analysis    Verification

 ~2K LOC      ~5K LOC         ~50K LOC             ~100K LOC        ∞ LOC
```

**Where ecma-rs sits**: Between Parsing and Binding
**Where TypeScript sits**: At Inference
**Where this plan proposes**: Pragmatic point between Binding and Checking

---

## II. ARCHITECTURE: Learning from the Giants

### A. TypeScript's Architecture (The Incumbent)

**Pipeline**: `Scanner → Parser → Binder → Checker → Emitter`

**Lessons Learned**:
1. **checker.ts is 53,960 lines** - type checking is MASSIVE
2. **Cyclic data structures everywhere** - AST ↔ Symbols ↔ Types
3. **Lazy evaluation** - only compute what's needed
4. **Single-threaded by design** (2012 decision) - hard to parallelize later
5. **JavaScript implementation** - sacrifices performance for portability

**Key Innovation**: Control Flow Analysis
- Backward traversal of control flow graph
- Type narrowing based on guards, branches, assignments
- Up to 5 levels of indirection
- Enables Union types to "just work"

### B. typescript-go's Revolution (The Disruptor)

**Performance Gains**: 10x faster (3-4x native, 3-4x parallelization)

**Architectural Decisions**:
1. **Structural similarity** - kept TypeScript's patterns in Go
2. **Goroutines for parallelization** - parse files concurrently
3. **Shared memory concurrency** - unlike JavaScript workers
4. **GC for cyclic structures** - no manual memory management
5. **1-1.5 months for scanner + parser** - rapid prototyping

**Key Insight**: Don't innovate on architecture AND language simultaneously. Port the proven architecture, then optimize.

### C. oxc & swc (The Speedsters)

**oxc Performance**: 3x faster than swc, 5x faster than Biome

**Architecture Secrets**:
1. **Bump allocation arena** (bumpalo) - fast alloc/dealloc
2. **Inline small strings** (CompactString) - reduce heap allocations
3. **Recursive descent + Pratt parsing** - handle deep nesting
4. **Lazy semantic analysis** - delegate to semantic pass
5. **Speculative parsing** - lookahead + backtracking for arrow functions

**Memory Profile** (cal.com.tsx):
- oxc: 11.5 MB
- swc: 16.6 MB (1.44x)
- biome: 22.5 MB (1.95x)

**Key Tradeoff**: FFI overhead (JSON.parse) makes Rust tools slower than TypeScript for small files in JS environments, but dominates for large codebases.

### D. Isolated Declarations (The Game Changer)

**Insight**: Type inference is the bottleneck for .d.ts generation

**Solution**: Require explicit types for exports
- Turns type emission into syntax stripping
- Enables non-TypeScript tools (oxc) to generate declarations
- **40x faster** than tsc for .d.ts generation
- **Real-world**: vue-macros 76s → 16s (4.75x improvement)

**Relevance**: For minification, we don't need inference either! Just strip types.

### E. Modern Type Theory (The Academic)

**Bidirectional Type Checking**:
- **Synthesis mode** (⇒): Compute type from expression
- **Checking mode** (⇐): Verify expression matches expected type
- **Advantage**: Scales to expressive type systems (unlike Hindley-Milner)
- **Error quality**: Natural error messages at type boundaries
- **Performance**: Local reasoning, no global constraint solving

**Flow-Sensitive Typing**:
- Type changes as control flow progresses
- Required for TypeScript's union narrowing
- Backward analysis from use sites

---

## III. THE PLAN: Three-Tiered Implementation Strategy

### TIER 1: Complete Type Parsing (3-4 weeks)

**Goal**: 100% TypeScript syntax support for parsing

#### Phase 1.1: Coverage Analysis (Week 1)
```rust
// Tools to build:
// 1. AST Coverage Analyzer
fn analyze_ast_coverage(typescript_cases: &[TestCase]) -> CoverageReport {
    // Parse all TypeScript conformance tests
    // Identify which AST nodes are hit vs missed
    // Generate heatmap of what's implemented
}

// 2. Feature Matrix
enum TSFeature {
    // Base
    PrimitiveTypes,           // ✅ DONE
    TypeReferences,           // ✅ DONE
    UnionIntersection,        // ✅ DONE

    // Advanced
    ConditionalTypes,         // ✅ DONE
    MappedTypes,              // ✅ DONE
    TemplateLiterals,         // ✅ DONE

    // Bleeding Edge
    ConstTypeParameters,      // ✅ DONE
    SatisfiesOperator,        // ❓ CHECK
    UsingAwaitUsing,          // ❓ CHECK
    Decorators,               // ✅ DONE

    // TypeScript 5.6+
    NoInferType,              // ❌ MISSING?
    SymbolTypes,              // ✅ DONE
}
```

**Deliverables**:
- Run conformance tests: `cargo test --release conformance_runner`
- Generate coverage report: `typescript_coverage_report.md`
- Prioritized list of missing features
- Test case suite for each missing feature

#### Phase 1.2: Fill the Gaps (Week 2-3)

**Missing Features Likely Needed**:

1. **Type Modifiers Edge Cases**
   ```typescript
   type T1 = readonly [string, ...number[]];  // readonly tuples with rest
   type T2 = { readonly [K in keyof T]-?: T[K] };  // -? modifier
   ```

2. **Import Type Enhancements**
   ```typescript
   type T = import("./mod").Type<number>;  // Already done?
   type T = typeof import("./mod").value;  // typeof + import
   ```

3. **Type-Only Imports/Exports**
   ```typescript
   import type { Foo } from "bar";  // Already done?
   export type { Foo };
   ```

4. **Exotic Syntax**
   ```typescript
   abstract new (...args: any[]) => any;  // Abstract construct signatures
   asserts this is string;  // Assertion signatures with this
   ```

5. **JSDoc Types** (if needed for JS minification)
   ```javascript
   /** @type {import('./types').Foo<number>} */
   ```

**Implementation Strategy**:
```rust
// For each missing feature:

// 1. Write test cases first
#[test]
fn test_readonly_tuple_with_rest() {
    let src = r#"
        type T = readonly [string, ...number[]];
    "#;
    let ast = parse(src).unwrap();
    // Assert correct AST structure
}

// 2. Extend AST if needed
#[derive(Debug, Serialize)]
pub struct TypeTupleElement {
    pub label: Option<String>,
    pub optional: bool,
    pub rest: bool,
    pub readonly: bool,  // ← May need to add this
    pub type_expr: Node<TypeExpr>,
}

// 3. Implement parser
impl<'a> Parser<'a> {
    fn tuple_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
        // Handle readonly prefix
        let readonly = self.consume_if(TT::KeywordReadonly).is_match();
        // ... rest of implementation
    }
}

// 4. Run conformance tests to verify
```

#### Phase 1.3: Parser Performance Optimization (Week 4)

**Benchmarking Infrastructure**:
```rust
// benches/parser_bench.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_type_parsing(c: &mut Criterion) {
    let samples = [
        ("primitive", "type T = string"),
        ("union", "type T = A | B | C | D | E"),
        ("mapped", "type T = { [K in keyof O]: O[K] }"),
        ("conditional", "type T = A extends B ? C : D"),
        ("complex", include_str!("samples/react.d.ts")),
    ];

    let mut group = c.benchmark_group("type_parsing");
    for (name, src) in samples {
        group.bench_function(name, |b| {
            b.iter(|| parse_js::parse(black_box(src)))
        });
    }
}
```

**Optimization Targets**:

1. **Hot Path Optimization**
   ```rust
   // Before: Check token type multiple times
   fn type_primary(&mut self) -> TypeExpr {
       match self.peek().typ {
           TT::KeywordString => self.parse_string_type(),
           TT::KeywordNumber => self.parse_number_type(),
           // ... 30 more cases
       }
   }

   // After: Use lookup table + computed goto
   static TYPE_KEYWORD_MAP: phf::Map<TT, TypeKind> = phf_map! {
       TT::KeywordString => TypeKind::String,
       TT::KeywordNumber => TypeKind::Number,
       // ...
   };

   fn type_primary_fast(&mut self) -> TypeExpr {
       if let Some(&kind) = TYPE_KEYWORD_MAP.get(&self.peek().typ) {
           self.parse_type_keyword(kind)
       } else {
           self.type_primary_slow()
       }
   }
   ```

2. **Reduce Allocations**
   ```rust
   // Before: Vec allocations for every union
   pub struct TypeUnion {
       pub types: Vec<Node<TypeExpr>>,  // Heap allocation
   }

   // After: Arena allocation + slice
   pub struct TypeUnion<'ast> {
       pub types: &'ast [Node<TypeExpr>],  // Arena-allocated
   }

   // Requires threading arena through parser:
   pub struct Parser<'src, 'ast> {
       lexer: Lexer<'src>,
       arena: &'ast Arena,
   }
   ```

3. **Speculative Parsing for Type Arguments**
   ```rust
   // Current: is_start_of_type_arguments() does lookahead
   // Problem: Scans tokens twice (lookahead + actual parse)

   // Solution: Use Result-based parsing
   fn try_type_arguments(&mut self) -> Option<Vec<TypeExpr>> {
       let checkpoint = self.checkpoint();

       if let Ok(args) = self.parse_type_arguments() {
           Some(args)
       } else {
           self.restore(checkpoint);
           None
       }
   }

   // Even better: Cache the parse attempt
   fn type_arguments_cached(&mut self) -> Option<&'ast [TypeExpr]> {
       // Memoize based on position
       self.speculation_cache.get_or_insert(self.pos(), || {
           self.try_type_arguments()
       })
   }
   ```

4. **SIMD for Token Classification**
   ```rust
   // For scanning type keywords, use SIMD string matching
   use std::simd::*;

   fn is_type_keyword_simd(s: &str) -> bool {
       // Pack first 4 chars into u32x4
       // Compare against all type keywords in parallel
       // Fallback to linear scan for non-matches
   }
   ```

**Target Metrics**:
- Parse TypeScript stdlib types (<1ms on M3)
- Parse large .d.ts files (50K lines) <50ms
- Match or exceed oxc parser performance

---

### TIER 2: Type-Aware Minification (4-6 weeks)

**Goal**: Use type information to enable optimizations that vanilla JS minifiers can't do

#### Phase 2.1: Type Stripping with Preservation (Week 5-6)

**Challenge**: Remove types while preserving runtime behavior

**Subtle Cases**:
```typescript
// 1. Type vs Value namespace
type T = { x: number };
const T = { x: 1 };  // Both T coexist!

// After minification:
const T = { x: 1 };  // Type removed, value stays

// 2. Enum value inlining
enum Color { Red = 1, Green = 2 }
console.log(Color.Red);  // Should become: console.log(1)

// 3. Const enum (must inline)
const enum Direction { Up, Down }
let x = Direction.Up;  // MUST become: let x = 0

// 4. Namespace merging
namespace N { export type T = number; }
namespace N { export const x = 1; }
// After: namespace N { export const x = 1; }

// 5. typeof operator context
type T = typeof x;  // Remove entire statement
if (typeof x === "string") {}  // Keep! Runtime typeof
```

**Implementation**:
```rust
pub struct TypeStripper<'ast> {
    /// Track which identifiers are types vs values
    type_symbols: HashSet<&'ast str>,
    value_symbols: HashSet<&'ast str>,

    /// Enum constants for inlining
    enum_values: HashMap<&'ast str, HashMap<&'ast str, i64>>,
}

impl<'ast> TypeStripper<'ast> {
    /// Phase 1: Collect type/value bindings
    fn analyze_bindings(&mut self, ast: &'ast TopLevel) {
        // Walk AST, populate symbol tables
    }

    /// Phase 2: Strip types
    fn strip(&mut self, ast: &'ast mut TopLevel) {
        // Remove type declarations
        // Inline const enums
        // Preserve value namespaces
    }
}
```

#### Phase 2.2: Dead Code Elimination via Types (Week 7-8)

**Insight**: Types reveal dead code that control flow analysis misses

**Examples**:
```typescript
// 1. Impossible type guards
function f(x: string) {
    if (typeof x === "number") {  // DEAD! x is always string
        console.log("unreachable");
    }
}

// 2. Exhaustive switch (TS knows it's complete)
type Action = { type: 'A' } | { type: 'B' };
function handle(a: Action) {
    switch (a.type) {
        case 'A': return 1;
        case 'B': return 2;
        // No default needed! TS knows it's exhaustive
    }
    console.log("unreachable");  // DEAD
}

// 3. Never-returning functions
function fail(msg: string): never {
    throw new Error(msg);
}
function test() {
    fail("oops");
    console.log("unreachable");  // DEAD
}
```

**Lightweight Type Inference**:
```rust
/// Minimal type representation for DCE
#[derive(Debug, Clone)]
enum SimpleType {
    String,
    Number,
    Boolean,
    Never,  // Function never returns
    Union(Vec<SimpleType>),
    Unknown,  // Fallback
}

pub struct DeadCodeEliminator {
    /// Type for each expression (computed on demand)
    expr_types: HashMap<NodeId, SimpleType>,
}

impl DeadCodeEliminator {
    /// Infer type from type annotation or literal
    fn infer_simple_type(&mut self, expr: &Expr) -> SimpleType {
        match expr {
            Expr::LitStr(_) => SimpleType::String,
            Expr::LitNum(_) => SimpleType::Number,
            Expr::Call(call) => {
                if let Some(func) = self.resolve_function(&call.callee) {
                    // Check if function return type is `never`
                    if func.return_type.is_never() {
                        return SimpleType::Never;
                    }
                }
                SimpleType::Unknown
            }
            _ => SimpleType::Unknown,
        }
    }

    /// Eliminate dead code in if statements
    fn eliminate_if(&mut self, if_stmt: &mut IfStmt) -> Elimination {
        if let Some(test_type) = self.infer_simple_type(&if_stmt.test) {
            match test_type {
                SimpleType::Never => {
                    // Test never executes, remove entire if
                    Elimination::RemoveStatement
                }
                _ => {
                    // Check typeof guards, etc.
                    self.eliminate_type_guards(if_stmt)
                }
            }
        } else {
            Elimination::Keep
        }
    }
}
```

**Benchmark**: Measure reduction in bundle size on real projects

#### Phase 2.3: Type-Directed Inlining (Week 9-10)

**Insight**: Types tell us when inlining is safe

```typescript
// 1. Pure function (type indicates no side effects)
function add(a: number, b: number): number {
    return a + b;
}
const x = add(1, 2);  // Inline to: const x = 3;

// 2. Const assertion
const config = {
    apiUrl: "https://api.example.com",
    timeout: 5000,
} as const;

fetch(config.apiUrl);
// Inline to: fetch("https://api.example.com");

// 3. Type-indexed access
type T = { a: 1, b: 2 };
type A = T['a'];  // Evaluates to: 1
const x: A = 1;   // Can infer x is always 1
```

**Implementation**:
```rust
pub struct TypeDirectedInliner {
    /// Const values that can be inlined
    const_values: HashMap<SymbolId, ConstValue>,
}

#[derive(Clone)]
enum ConstValue {
    Number(f64),
    String(String),
    Boolean(bool),
    Object(HashMap<String, ConstValue>),
}

impl TypeDirectedInliner {
    fn inline_member_access(&mut self, member: &MemberExpr) -> Option<Expr> {
        // config.apiUrl where config is `as const`
        if let Some(obj_value) = self.const_values.get(&member.object) {
            if let ConstValue::Object(fields) = obj_value {
                if let Some(field) = fields.get(&member.property) {
                    return Some(field.to_expr());
                }
            }
        }
        None
    }
}
```

---

### TIER 3: Full Type Checking (Moonshot: 6-12 months)

**Goal**: Build a complete, production-ready TypeScript type checker in Rust

**Why Consider This**:
1. **Ecosystem gap**: No Rust-native TypeScript type checker exists
2. **IDE integration**: rust-analyzer could use it for .ts files
3. **Tooling**: Enable linting, refactoring, code generation
4. **Learning**: Deep understanding of type systems
5. **Performance**: 10-100x faster than tsc could change the game

**Reality Check**: This is ~50,000-100,000 lines of complex code. TypeScript team has 12 years of headstart. BUT: We can learn from their mistakes.

#### Phase 3.1: Binder (Scope & Symbol Resolution)

**What**: Associate names with declarations

```rust
#[derive(Debug)]
pub struct Binder<'ast> {
    /// Symbol table: name -> all declarations
    symbols: HashMap<&'ast str, Symbol<'ast>>,

    /// Scope tree
    scopes: Vec<Scope<'ast>>,
    current_scope: ScopeId,

    /// Exports from modules
    exports: HashMap<&'ast str, Vec<Export<'ast>>>,
}

#[derive(Debug)]
pub struct Symbol<'ast> {
    name: &'ast str,
    declarations: Vec<&'ast Node<Declaration>>,
    flags: SymbolFlags,
}

bitflags! {
    struct SymbolFlags: u32 {
        const VALUE = 1 << 0;
        const TYPE = 1 << 1;
        const NAMESPACE = 1 << 2;
        const ENUM = 1 << 3;
        const CONST_ENUM = 1 << 4;
        // ...
    }
}

impl<'ast> Binder<'ast> {
    /// Main entry point: bind all declarations in a source file
    pub fn bind(&mut self, source: &'ast SourceFile) {
        self.visit_statements(&source.statements);
    }

    fn visit_var_decl(&mut self, decl: &'ast VarDecl) {
        for declarator in &decl.declarators {
            // Extract names from pattern
            let names = self.extract_binding_names(&declarator.pattern);
            for name in names {
                self.declare_symbol(name, SymbolFlags::VALUE);
            }
        }
    }

    fn visit_type_alias(&mut self, alias: &'ast TypeAlias) {
        self.declare_symbol(&alias.name, SymbolFlags::TYPE);
    }

    fn visit_interface(&mut self, iface: &'ast Interface) {
        // Interface can be both type and value (if it merges with namespace)
        self.declare_symbol(&iface.name, SymbolFlags::TYPE);
    }
}
```

**Complexity**: Namespaces, module merging, declaration merging

#### Phase 3.2: Type Representation

**What**: Data structures to represent types

```rust
#[derive(Debug, Clone)]
pub enum Type {
    /// Primitive types
    String,
    Number,
    Boolean,
    Null,
    Undefined,
    Void,
    Any,
    Unknown,
    Never,

    /// Object type (anonymous)
    Object(ObjectType),

    /// Reference to named type
    Reference(TypeReference),

    /// Union: A | B | C
    Union(Vec<Type>),

    /// Intersection: A & B & C
    Intersection(Vec<Type>),

    /// Function type
    Function(FunctionType),

    /// Conditional: T extends U ? X : Y
    Conditional(Box<ConditionalType>),

    /// Indexed access: T[K]
    IndexedAccess { object: Box<Type>, index: Box<Type> },

    /// Type variable (generic parameter)
    TypeParameter(TypeParameter),
}

#[derive(Debug, Clone)]
pub struct ObjectType {
    /// { x: string, y: number }
    properties: Vec<Property>,

    /// [key: string]: any
    index_signatures: Vec<IndexSignature>,

    /// (): void
    call_signatures: Vec<Signature>,

    /// new (): Foo
    construct_signatures: Vec<Signature>,
}

#[derive(Debug, Clone)]
pub struct FunctionType {
    type_parameters: Vec<TypeParameter>,
    parameters: Vec<Parameter>,
    return_type: Box<Type>,
}

/// Type checker state
pub struct TypeChecker<'ast> {
    /// Symbol table from binder
    symbols: &'ast HashMap<String, Symbol<'ast>>,

    /// Cache: Type for each expression
    type_cache: HashMap<NodeId, Type>,

    /// Cache: Signature for each call
    signature_cache: HashMap<NodeId, Signature>,

    /// Inference context (for generics)
    inference_context: Vec<InferenceContext>,
}
```

**Optimization**: Interning, hash-consing for structural equality

#### Phase 3.3: Bidirectional Type Checking

**What**: Core type checking algorithm

```rust
impl<'ast> TypeChecker<'ast> {
    /// Synthesis (⇒): Compute type of expression
    pub fn synth(&mut self, expr: &Expr) -> Result<Type, TypeError> {
        match expr {
            Expr::LitStr(_) => Ok(Type::String),
            Expr::LitNum(_) => Ok(Type::Number),

            Expr::Id(id) => {
                // Look up symbol
                let symbol = self.resolve_symbol(&id.name)?;
                Ok(self.get_type_of_symbol(symbol))
            }

            Expr::Call(call) => {
                // Synth callee type
                let callee_type = self.synth(&call.callee)?;

                // Extract call signature
                let sig = self.get_call_signature(&callee_type)?;

                // Check arguments against parameters
                self.check_arguments(&call.arguments, &sig.parameters)?;

                Ok(sig.return_type.clone())
            }

            Expr::Binary(bin) => {
                // Synth left and right
                let left_type = self.synth(&bin.left)?;
                let right_type = self.synth(&bin.right)?;

                // Type check operator
                self.check_binary_op(bin.operator, &left_type, &right_type)
            }

            // ... many more cases
        }
    }

    /// Checking (⇐): Verify expression has expected type
    pub fn check(&mut self, expr: &Expr, expected: &Type) -> Result<(), TypeError> {
        match expr {
            // Lambda: use expected type for parameter inference
            Expr::ArrowFunc(arrow) => {
                // Extract function type from expected
                let func_type = self.as_function_type(expected)?;

                // Infer parameter types from expected
                for (param, expected_param) in arrow.parameters.iter()
                    .zip(&func_type.parameters)
                {
                    if param.type_annotation.is_none() {
                        self.infer_param_type(param, &expected_param.type_);
                    }
                }

                // Check body against expected return type
                self.check(&arrow.body, &func_type.return_type)
            }

            // Default: synth then verify subtype
            _ => {
                let actual = self.synth(expr)?;
                self.check_assignable(&actual, expected)
            }
        }
    }

    /// Subtyping: Is `source` assignable to `target`?
    fn check_assignable(&mut self, source: &Type, target: &Type) -> Result<(), TypeError> {
        match (source, target) {
            (_, Type::Any) | (Type::Any, _) => Ok(()),
            (Type::Never, _) => Ok(()),
            (_, Type::Unknown) => Ok(()),

            (Type::Union(sources), target) => {
                // A | B <: T  iff  A <: T and B <: T
                for s in sources {
                    self.check_assignable(s, target)?;
                }
                Ok(())
            }

            (source, Type::Union(targets)) => {
                // S <: A | B  iff  S <: A or S <: B
                for t in targets {
                    if self.check_assignable(source, t).is_ok() {
                        return Ok(());
                    }
                }
                Err(TypeError::NotAssignable {
                    source: source.clone(),
                    target: target.clone(),
                })
            }

            (Type::Object(s), Type::Object(t)) => {
                self.check_object_assignable(s, t)
            }

            // ... structural comparison for objects, functions, etc.

            _ => {
                if source == target {
                    Ok(())
                } else {
                    Err(TypeError::NotAssignable {
                        source: source.clone(),
                        target: target.clone(),
                    })
                }
            }
        }
    }
}
```

#### Phase 3.4: Control Flow Analysis

**What**: Track type narrowing through branches

```rust
#[derive(Debug, Clone)]
pub struct FlowNode {
    /// Type of flow node
    kind: FlowKind,

    /// Previous flow node(s)
    antecedents: Vec<FlowNodeRef>,
}

#[derive(Debug, Clone)]
pub enum FlowKind {
    /// Entry point (function start)
    Start,

    /// Assignment: x = expr
    Assignment { variable: SymbolId, value: ExprId },

    /// Type guard: typeof x === "string"
    TypeGuard { variable: SymbolId, narrowed_type: Type },

    /// Condition: if (test) { consequent } else { alternate }
    Condition { test: ExprId, consequent: FlowNodeRef, alternate: FlowNodeRef },

    /// Merge point (join after branch)
    Label { antecedents: Vec<FlowNodeRef> },
}

impl<'ast> TypeChecker<'ast> {
    /// Get type of variable at a specific flow node
    fn get_flow_type(&mut self, symbol: SymbolId, flow: FlowNodeRef) -> Type {
        // Walk backwards through flow graph
        match self.flow_nodes[flow].kind {
            FlowKind::Start => {
                // Use declared type
                self.get_declared_type(symbol)
            }

            FlowKind::Assignment { variable, value } if variable == symbol => {
                // Variable was assigned, use type of value
                self.synth_expr(value)
            }

            FlowKind::TypeGuard { variable, ref narrowed_type } if variable == symbol => {
                // Type was narrowed by guard
                narrowed_type.clone()
            }

            FlowKind::Condition { consequent, alternate, .. } => {
                // Union of types in both branches
                let consequent_type = self.get_flow_type(symbol, consequent);
                let alternate_type = self.get_flow_type(symbol, alternate);
                Type::Union(vec![consequent_type, alternate_type])
            }

            FlowKind::Label { ref antecedents } => {
                // Union of types from all incoming flows
                let types: Vec<Type> = antecedents.iter()
                    .map(|&ant| self.get_flow_type(symbol, ant))
                    .collect();
                Type::Union(types)
            }

            _ => {
                // Unrelated flow node, recurse to antecedent
                self.get_flow_type(symbol, self.flow_nodes[flow].antecedents[0])
            }
        }
    }

    /// Check typeof guard
    fn check_typeof_guard(&mut self, test: &BinaryExpr) -> Option<(SymbolId, Type)> {
        // typeof x === "string"
        if test.operator == Operator::EqualsEqualsEquals {
            if let Expr::Unary(unary) = &*test.left {
                if unary.operator == Operator::Typeof {
                    if let Expr::Id(id) = &*unary.argument {
                        if let Expr::LitStr(s) = &*test.right {
                            let narrowed_type = match s.value.as_str() {
                                "string" => Type::String,
                                "number" => Type::Number,
                                "boolean" => Type::Boolean,
                                "undefined" => Type::Undefined,
                                "object" => Type::Object(ObjectType::any()),
                                "function" => Type::Function(FunctionType::any()),
                                _ => return None,
                            };

                            let symbol = self.resolve_symbol(&id.name).ok()?;
                            return Some((symbol, narrowed_type));
                        }
                    }
                }
            }
        }
        None
    }
}
```

**Example**:
```typescript
function example(x: string | number) {
    // FlowNode: Start, x: string | number

    if (typeof x === "string") {
        // FlowNode: TypeGuard, x: string
        console.log(x.toUpperCase());  // OK
    } else {
        // FlowNode: !TypeGuard, x: number
        console.log(x.toFixed(2));  // OK
    }

    // FlowNode: Label (merge of branches), x: string | number
}
```

#### Phase 3.5: Type Inference for Generics

**What**: Infer type arguments from usage

```rust
impl<'ast> TypeChecker<'ast> {
    /// Infer type arguments for generic function call
    fn infer_type_arguments(
        &mut self,
        type_params: &[TypeParameter],
        params: &[Parameter],
        args: &[Expr],
    ) -> Result<Vec<Type>, TypeError> {
        // Create inference context
        let mut ctx = InferenceContext::new(type_params);

        // Infer from each argument
        for (param, arg) in params.iter().zip(args) {
            self.infer_from_types(&mut ctx, &param.type_, &self.synth(arg)?);
        }

        // Resolve inferred types
        let mut result = Vec::new();
        for tp in type_params {
            let inferred = ctx.resolve(&tp.name)?;
            result.push(inferred);
        }

        Ok(result)
    }

    /// Infer type parameter from source and target types
    fn infer_from_types(&mut self, ctx: &mut InferenceContext, source: &Type, target: &Type) {
        match (source, target) {
            // T <: string  =>  T = string
            (Type::TypeParameter(tp), target) => {
                ctx.infer(tp, target.clone());
            }

            // string <: T  =>  T >: string (contravariant)
            (source, Type::TypeParameter(tp)) => {
                ctx.infer_contravariant(tp, source.clone());
            }

            // [T] <: [string]  =>  T = string
            (Type::Array(s), Type::Array(t)) => {
                self.infer_from_types(ctx, &s.element, &t.element);
            }

            // {x: T} <: {x: string}  =>  T = string
            (Type::Object(s), Type::Object(t)) => {
                for t_prop in &t.properties {
                    if let Some(s_prop) = s.get_property(&t_prop.name) {
                        self.infer_from_types(ctx, &s_prop.type_, &t_prop.type_);
                    }
                }
            }

            _ => {
                // No inference
            }
        }
    }
}

struct InferenceContext {
    /// Type parameter -> inferred candidates
    candidates: HashMap<String, Vec<Type>>,

    /// Type parameter -> contravariant candidates
    contravariant_candidates: HashMap<String, Vec<Type>>,
}

impl InferenceContext {
    fn infer(&mut self, tp: &str, candidate: Type) {
        self.candidates.entry(tp.to_string())
            .or_default()
            .push(candidate);
    }

    fn resolve(&self, tp: &str) -> Result<Type, TypeError> {
        let candidates = self.candidates.get(tp)
            .ok_or_else(|| TypeError::CannotInferTypeParameter(tp.to_string()))?;

        // Simplify: just use first candidate
        // Reality: compute common supertype / common subtype
        Ok(candidates[0].clone())
    }
}
```

**Example**:
```typescript
function map<T, U>(arr: T[], f: (x: T) => U): U[] {
    return arr.map(f);
}

const result = map([1, 2, 3], x => x.toString());
//                  ^^^^^^^^^  ^^^^^^^^^^^^^^^^
//                  T = number U = string (inferred)
```

---

## IV. PERFORMANCE ENGINEERING

### A. Parsing Performance

**Target**: Match or exceed oxc (3x faster than swc)

**Techniques**:

1. **Bump Allocation**
   ```rust
   use bumpalo::Bump;

   pub struct Parser<'src, 'ast> {
       arena: &'ast Bump,
       // All AST nodes allocated in arena
   }

   impl<'src, 'ast> Parser<'src, 'ast> {
       fn parse_type_expr(&mut self) -> &'ast TypeExpr {
           let type_expr = TypeExpr::String;
           self.arena.alloc(type_expr)  // Fast!
       }
   }
   ```

2. **Inline Small Strings**
   ```rust
   use compact_str::CompactString;

   pub struct TypeReference {
       pub name: CompactString,  // Inline if <= 24 bytes
   }
   ```

3. **Zero-Copy Parsing**
   ```rust
   pub struct Parser<'src> {
       source: &'src str,
   }

   pub struct Identifier<'src> {
       // Point into source, don't allocate
       pub name: &'src str,
   }
   ```

4. **SIMD Token Scanning**
   ```rust
   use std::simd::*;

   fn skip_whitespace_simd(s: &[u8]) -> usize {
       let spaces = u8x16::splat(b' ');
       let tabs = u8x16::splat(b'\t');
       let newlines = u8x16::splat(b'\n');

       for chunk in s.chunks_exact(16) {
           let v = u8x16::from_slice(chunk);
           let mask = v.simd_eq(spaces) | v.simd_eq(tabs) | v.simd_eq(newlines);
           if !mask.all() {
               return mask.first_false();
           }
       }
       // Fallback for remainder
   }
   ```

### B. Type Checking Performance

**Target**: 10x faster than tsc (like typescript-go)

**Techniques**:

1. **Lazy Evaluation**
   ```rust
   pub struct TypeChecker {
       /// Only compute types when asked
       type_cache: RefCell<HashMap<NodeId, Lazy<Type>>>,
   }

   impl TypeChecker {
       fn get_type(&self, node: NodeId) -> Type {
           self.type_cache.borrow_mut()
               .entry(node)
               .or_insert_with(|| Lazy::new(|| self.compute_type(node)))
               .force()
               .clone()
       }
   }
   ```

2. **Parallelization**
   ```rust
   use rayon::prelude::*;

   pub fn type_check_program(files: &[SourceFile]) -> Vec<Diagnostic> {
       // Parse files in parallel
       let asts: Vec<_> = files.par_iter()
           .map(|f| parse(f.source))
           .collect();

       // Bind files in parallel (independent)
       let symbols: Vec<_> = asts.par_iter()
           .map(|ast| bind(ast))
           .collect();

       // Merge symbol tables
       let global_symbols = merge_symbols(symbols);

       // Type check files in parallel (read-only access to global symbols)
       files.par_iter()
           .zip(&asts)
           .flat_map(|(file, ast)| type_check(ast, &global_symbols))
           .collect()
   }
   ```

3. **Structural Sharing (Hash-Consing)**
   ```rust
   pub struct TypeTable {
       /// Deduplicate identical types
       intern: HashMap<Type, TypeId>,
       types: Vec<Type>,
   }

   impl TypeTable {
       pub fn intern(&mut self, ty: Type) -> TypeId {
           if let Some(&id) = self.intern.get(&ty) {
               return id;
           }

           let id = TypeId(self.types.len());
           self.types.push(ty.clone());
           self.intern.insert(ty, id);
           id
       }
   }

   // Now Type comparisons are just integer comparisons!
   #[derive(Copy, Clone, PartialEq, Eq, Hash)]
   pub struct TypeId(usize);
   ```

4. **Incremental Type Checking**
   ```rust
   pub struct IncrementalTypeChecker {
       /// Hash of each file's source
       file_hashes: HashMap<PathBuf, u64>,

       /// Cached type info per file
       file_types: HashMap<PathBuf, FileTypeInfo>,

       /// Dependency graph
       dependencies: HashMap<PathBuf, Vec<PathBuf>>,
   }

   impl IncrementalTypeChecker {
       pub fn check_changed_files(&mut self, changed: &[PathBuf]) {
           // Compute transitive dependencies
           let to_check = self.compute_transitive_deps(changed);

           // Only re-check affected files
           for file in to_check {
               self.check_file(file);
           }
       }
   }
   ```

### C. Memory Efficiency

**Target**: <100MB for stdlib, <1GB for large projects

**Techniques**:

1. **Compact AST Representation**
   ```rust
   // Before: 32 bytes per node (8-byte pointers)
   pub struct Node<T> {
       pub loc: Loc,      // 8 bytes
       pub value: T,      // variable
   }

   // After: 16 bytes per node (use indices)
   pub struct CompactNode {
       pub loc: u32,      // 4 bytes (offset into source)
       pub kind: u16,     // 2 bytes (node type discriminant)
       pub data: u16,     // 2 bytes (inline data or index)
       pub extra: u32,    // 4 bytes (index into extra data array)
   }
   ```

2. **Deduplicate Strings**
   ```rust
   pub struct StringInterner {
       strings: Vec<String>,
       map: HashMap<String, StringId>,
   }

   #[derive(Copy, Clone)]
   pub struct StringId(u32);
   ```

3. **Compress Source Locations**
   ```rust
   // Before: 16 bytes per location
   pub struct Loc {
       start: usize,  // 8 bytes
       end: usize,    // 8 bytes
   }

   // After: 8 bytes per location
   pub struct CompactLoc {
       start: u32,  // 4 bytes (offsets, not absolute)
       len: u16,    // 2 bytes (length, max 64KB)
       file: u16,   // 2 bytes (file ID)
   }
   ```

---

## V. TESTING STRATEGY

### A. Conformance Testing

**Goal**: Pass TypeScript's own test suite

```bash
# Run TypeScript conformance tests
cargo test --release conformance_runner

# Target: >95% pass rate
# Currently: ~80-90% estimated (need to run to verify)
```

**Test Categories**:
- `tests/cases/conformance/types/` - Type system tests
- `tests/cases/conformance/parser/` - Parser tests
- `tests/cases/conformance/expressions/` - Expression tests
- `tests/cases/compiler/` - Compiler tests

### B. Differential Testing

**Technique**: Compare output with TypeScript

```rust
#[test]
fn differential_test_types() {
    let samples = load_real_world_types();

    for sample in samples {
        // Parse with our parser
        let our_ast = parse_js::parse(&sample.source).unwrap();

        // Parse with TypeScript (via Node.js FFI)
        let ts_ast = typescript_parse(&sample.source).unwrap();

        // Compare ASTs (modulo formatting differences)
        assert_ast_equivalent(&our_ast, &ts_ast);
    }
}
```

### C. Fuzzing

**Technique**: Generate random TypeScript code

```rust
use arbitrary::Arbitrary;

#[derive(Arbitrary, Debug)]
pub enum TypeExpr {
    String,
    Number,
    Union(Box<TypeExpr>, Box<TypeExpr>),
    // ...
}

#[test]
fn fuzz_type_parser() {
    bolero::check!()
        .with_type::<TypeExpr>()
        .for_each(|type_expr| {
            let source = type_expr.to_source();

            // Should not panic
            let _ = parse_js::parse(&source);
        });
}
```

### D. Property-Based Testing

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn roundtrip_type_expr(type_expr in any::<TypeExpr>()) {
        // Generate source
        let source = type_expr.to_source();

        // Parse
        let parsed = parse_js::parse(&source).unwrap();

        // Re-generate source
        let source2 = parsed.to_source();

        // Parse again
        let parsed2 = parse_js::parse(&source2).unwrap();

        // Should be equivalent
        assert_eq!(parsed, parsed2);
    }
}
```

### E. Benchmark Suite

```rust
// benches/parser.rs
fn bench_real_world_files(c: &mut Criterion) {
    let samples = [
        ("react.d.ts", include_str!("samples/react.d.ts")),
        ("typescript.d.ts", include_str!("samples/typescript.d.ts")),
        ("vscode-api.d.ts", include_str!("samples/vscode.d.ts")),
    ];

    for (name, source) in samples {
        c.bench_function(name, |b| {
            b.iter(|| parse_js::parse(black_box(source)))
        });
    }
}
```

---

## VI. CUTTING-EDGE INNOVATIONS

### A. Novel Type Optimizations

**1. Const Propagation Through Types**
```typescript
type Config = { readonly apiUrl: "https://api.com"; };
const config: Config = { apiUrl: "https://api.com" };

fetch(config.apiUrl);
// Minify to: fetch("https://api.com");
```

**2. Type-Guided Tree Shaking**
```typescript
// If a function's return type is `never`, all code after calling it is dead
function fail(): never { throw new Error(); }

function test() {
    fail();
    console.log("unreachable");  // REMOVE
}
```

**3. Nominal Types for Better Optimization**
```typescript
// Brand types prevent accidental mixing
type UserId = string & { __brand: "UserId" };
type OrderId = string & { __brand: "OrderId" };

// Can optimize comparisons: they're structurally the same (string)
// but semantically different (prevent bugs)
```

### B. Zero-Cost Abstractions via Types

**Idea**: Use types to guide monomorphization (like Rust)

```typescript
// Generic function with type parameter
function identity<T>(x: T): T { return x; }

// Calls:
identity<number>(42);
identity<string>("hello");

// Minifier can generate specialized versions:
function identityNumber(x) { return x; }  // Inline everything
function identityString(x) { return x; }
```

### C. Effect System (Experimental)

**Track side effects in types**

```typescript
type Effect = "dom" | "network" | "storage" | "pure";

function readLocalStorage(): string @effect("storage") { ... }
function fetchApi(): Promise<Data> @effect("network") { ... }
function add(a: number, b: number): number @effect("pure") { ... }

// Pure functions can be:
// 1. Inlined aggressively
// 2. Memoized automatically
// 3. Reordered freely
// 4. Dead code eliminated if result unused
```

### D. Gradual Types (for JS minification)

**Infer types from JS code**

```javascript
// No type annotations, but we can infer:
function add(a, b) {
    return a + b;  // Used with +, likely number
}

add(1, 2);  // Confirms: number → number
```

**Use inferred types for optimization**

---

## VII. IMPLEMENTATION ROADMAP

### Month 1-2: Foundation (Tier 1)

**Week 1-2**: Coverage analysis & gap filling
- Run conformance tests, measure pass rate
- Identify missing TypeScript features
- Prioritize by frequency in real code

**Week 3-4**: Parser optimization
- Implement bump allocation
- Add SIMD token scanning
- Benchmark against oxc/swc
- Target: 3x current speed

**Week 5-6**: Type stripping
- Implement type removal preserving behavior
- Handle edge cases (enum inlining, namespace merging)
- Validate on real projects (React, Vue, etc.)

**Deliverable**: Production-ready TypeScript parser + stripper

### Month 3-4: Optimization (Tier 2)

**Week 7-8**: Dead code elimination
- Implement lightweight type inference
- Detect impossible type guards
- Remove unreachable code after `never` functions

**Week 9-10**: Type-directed inlining
- Inline `as const` object properties
- Inline const enum values
- Inline pure functions (detect via types)

**Week 11-12**: Integration & validation
- Test on real-world projects
- Measure bundle size reduction
- Performance profiling & optimization

**Deliverable**: Type-aware minifier outperforming pure JS minifiers

### Month 5-12: Type Checker (Tier 3) [Optional]

**Month 5**: Binder
- Symbol resolution
- Scope analysis
- Declaration merging

**Month 6**: Type representation
- Define Type enum
- Structural comparison
- Type interning

**Month 7-8**: Bidirectional checking
- Synthesis mode
- Checking mode
- Subtyping algorithm

**Month 9**: Control flow analysis
- Flow graph construction
- Type narrowing
- Type guards

**Month 10**: Generic inference
- Inference context
- Constraint solving
- Instantiation

**Month 11-12**: Polish & completeness
- Error messages
- Diagnostics
- IDE integration (LSP)

**Deliverable**: Production-ready TypeScript type checker

---

## VIII. SUCCESS METRICS

### Tier 1 (Parser)
- ✅ Parse all TypeScript conformance tests (>95% pass rate)
- ✅ Match oxc parser speed (within 20%)
- ✅ Memory usage <50MB for stdlib types
- ✅ Zero panics on fuzz testing

### Tier 2 (Minifier)
- ✅ 5-10% smaller bundles vs non-type-aware minifiers
- ✅ Zero runtime behavior changes (differential testing)
- ✅ <2x slowdown vs pure parsing (acceptable for better compression)

### Tier 3 (Type Checker)
- ✅ Pass TypeScript's compiler test suite (>90%)
- ✅ 10x faster than tsc on large projects
- ✅ Incremental checking <100ms for small changes
- ✅ LSP response times <10ms (50ms for large files)

---

## IX. RISK MITIGATION

### Risk 1: Scope Creep
**Mitigation**: Strict tier boundaries, ship Tier 1 before starting Tier 2

### Risk 2: TypeScript Compatibility
**Mitigation**: Conformance testing, differential testing, fuzzing

### Risk 3: Performance Regression
**Mitigation**: Continuous benchmarking, performance budgets

### Risk 4: Maintenance Burden
**Mitigation**: TypeScript evolves rapidly; need automated test suite updates

---

## X. REFERENCES & INSPIRATION

### Papers
- **Bidirectional Type Checking**: "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism" (Dunfield & Krishnaswami, 2013)
- **Flow-Sensitive Typing**: "Control Flow Analysis" (Anders Hejlsberg, TypeScript PR #8010)
- **Effect Systems**: "Eff: Programming with Algebraic Effects and Handlers" (Bauer & Pretnar, 2012)

### Codebases
- **TypeScript**: `src/compiler/checker.ts` (53,960 lines of wisdom)
- **typescript-go**: Architecture decisions, parallelization strategy
- **oxc**: Parser optimization techniques (arena allocation, SIMD)
- **swc**: Early Rust TypeScript parser pioneer

### Blog Posts
- "Flow Nodes: How Type Inference Is Implemented" (effectivetypescript.com)
- "Speeding up the JavaScript ecosystem - Isolated Declarations" (marvinh.dev)
- "A 10x Faster TypeScript" (TypeScript blog)

---

## XI. CONCLUSION

### What We Have
A **strong foundation**: complete type expression AST, full parser, 21K test cases.

### What We Need
**Three paths**:
1. **Complete the parser** (2 months) - evolutionary, safe
2. **Add type-aware optimizations** (2 months more) - innovative, valuable
3. **Build full type checker** (6+ months) - revolutionary, ambitious

### The Opportunity
- **Performance**: Rust + parallelization + modern architecture = 10-100x speedup
- **Innovation**: Type-aware minification is unexplored territory
- **Ecosystem**: Rust needs a native TypeScript type checker
- **Learning**: Deep understanding of type systems, compilers, PL theory

### The Philosophy
- **Simple is better**: Fewer features, better implemented
- **Performance matters**: It's not just about speed, it's about enabling new workflows
- **Stand on giants' shoulders**: Learn from TypeScript's 12 years, don't repeat mistakes
- **Rust is the secret weapon**: Memory safety, zero-cost abstractions, fearless concurrency

**Let's build something beautiful.** 🚀

---

*"Perfection is achieved, not when there is nothing more to add, but when there is nothing left to take away."* - Antoine de Saint-Exupéry

*"The fastest code is the code that never runs."* - Type-aware optimizers everywhere
