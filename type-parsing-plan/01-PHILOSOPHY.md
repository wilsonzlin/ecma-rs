# Philosophy: What IS Type Parsing?

## The Fundamental Question

When we say "add type parsing," what do we actually mean?

This document explores the philosophical and technical foundations of type systems, from syntax to semantics to pragmatics.

---

## I. The Three Dimensions of Types

### 1. Syntax (Form)
**What**: Recognizing type annotations as valid text

```typescript
function f<T extends number>(x: T): T { return x; }
         ^^^^^^^^^^^^^^^^^^    ^^^    ^^^
         Type syntax recognized by parser
```

**Parser's job**:
- Is this string of characters valid TypeScript?
- What's the structure (AST)?
- How do tokens relate?

**Already solved in ecma-rs!** ✅

---

### 2. Semantics (Meaning)
**What**: Understanding what types mean

```typescript
type T = number;
const x: T = "hello";  // ❌ Error: string not assignable to number

// The type checker knows:
// - T is an alias for number
// - "hello" is a string
// - string ⊄ number (not a subtype)
```

**Type checker's job**:
- What does each type mean?
- Are two types compatible?
- Does this program make sense?

**This is the hard part** - TypeScript's checker.ts is 53,960 lines

---

### 3. Pragmatics (Use)
**What**: Using type information for tools

```typescript
// IDE autocomplete: types tell us what methods exist
const s: string = "hello";
s.toUpperCase();  // IDE suggests this based on string type
  ^

// Minifier: types enable optimizations
function f(x: string) {
    if (typeof x === "number") {  // Dead code!
        unreachable();  // Type tells us this never runs
    }
}
```

**Tool's job**:
- How can types improve user experience?
- What optimizations do types enable?
- How to present type information?

**This is our opportunity!** 🚀

---

## II. The Spectrum of Type Systems

```
Parsing ──► Binding ──► Checking ──► Inference ──► Proving
   ▲            ▲            ▲            ▲            ▲
   │            │            │            │            │
   │            │            │            │            │
You are     Scope &      Type       Bidirectional   Formal
here now    Symbols    Relations    Flow Analysis  Verification

~2K LOC    ~5K LOC    ~50K LOC      ~100K LOC       ∞ LOC
```

### Level 0: Parsing
**What you do**: Recognize `x: number` as valid syntax
**AST**: `VarDecl { name: "x", type_annotation: Some(TypeExpr::Number) }`
**Don't**: Understand what `number` means

**Status in ecma-rs**: ✅ DONE

---

### Level 1: Binding
**What you do**: Associate names with declarations

```typescript
type T = number;  // Declaration of T
const x: T = 1;   // Use of T - what does it refer to?
```

**Symbol table**:
```
"T" → TypeAlias { name: "T", type_expr: Number }
"x" → VarDecl { name: "x", type_annotation: TypeRef("T") }
```

**Don't**: Substitute `T` with `number` yet

**Complexity**: ~5,000 lines
- Scope analysis
- Declaration merging (interfaces, namespaces)
- Import/export resolution

---

### Level 2: Type Checking
**What you do**: Verify types are compatible

```typescript
type T = number;
const x: T = "hello";  // Error: string not assignable to T
```

**Steps**:
1. Resolve `T` → `number` (via symbol table)
2. Infer type of `"hello"` → `string`
3. Check `string <: number` → ❌ False
4. Report error

**Complexity**: ~50,000 lines
- Type compatibility (subtyping)
- Structural comparison
- Generic instantiation
- Type narrowing

---

### Level 3: Type Inference
**What you do**: Compute types without annotations

```typescript
function map(arr, f) {  // No type annotations!
    return arr.map(f);
}

map([1, 2, 3], x => x * 2);
//   ^^^^^^^^^  ^^^^^^^^^^
//   Infer: number[]  and (number) => number
```

**Algorithms**:
- Hindley-Milner (Haskell, OCaml): global constraint solving
- Bidirectional (TypeScript): local reasoning with context
- Flow-sensitive (TypeScript): types change based on control flow

**Complexity**: ~100,000+ lines
- Constraint generation
- Unification
- Control flow graph
- Backward analysis

**TypeScript is HERE** 🎯

---

### Level 4: Formal Verification
**What you do**: Prove correctness properties

```typescript
// Prove: if input is non-empty, output is non-empty
function head<T>(arr: NonEmpty<T[]>): T {
    return arr[0];  // Proven safe (no undefined)
}
```

**Tools**: Coq, Agda, Lean, F*
**Complexity**: Research frontier

**Not our concern!** 🙂

---

## III. Where Should ecma-rs Land?

### Current Position: Level 0 ✅
- Complete syntax parsing
- Rich AST with all type information
- Ready to strip types

### Recommended Target: Level 1.5
**Why**: Maximum value for minification

**What we need**:
1. **Basic binding** (Level 1)
   - Resolve type aliases: `type T = number; const x: T` → `T` means `number`
   - Resolve imported types: `import {Foo} from "bar"; const x: Foo`
   - Handle declaration merging: namespaces, interfaces

2. **Lightweight inference** (Level 2-lite)
   - Literal types: `const x = "hello"` → type is `"hello"` (not just `string`)
   - Type guards: `if (typeof x === "string")` → `x` is `string` in block
   - Simple control flow: detect unreachable code after `never` functions

3. **NO full type checking**
   - Don't verify all assignments
   - Don't check function call compatibility
   - Don't resolve complex generics
   - Just enough to optimize!

**Why this level**:
- ✅ Enables dead code elimination
- ✅ Enables const propagation
- ✅ Tractable scope (~10K lines, not 100K)
- ✅ Clear value proposition for minification
- ✅ Foundation for future expansion

---

## IV. The Minifier's Perspective

### What Does a Minifier Need?

**Input**: TypeScript source
```typescript
enum Color { Red = 1, Green = 2 }
const config = { apiUrl: "https://api.com" } as const;

function greet(name: string): void {
    console.log(`Hello ${name}`);
}

type User = { id: number; name: string };
const user: User = { id: 1, name: "Alice" };
```

**Output**: Minified JavaScript
```javascript
const Color={Red:1,Green:2};
const config={apiUrl:"https://api.com"};
function greet(name){console.log(`Hello ${name}`)}
const user={id:1,name:"Alice"}
```

**Type's role**:
1. **Strip**: Remove type annotations, type declarations
2. **Preserve**: Keep runtime values (enums, namespaces with values)
3. **Inline**: Const enums, `as const` objects
4. **Eliminate**: Dead code revealed by types

---

### What Does a Type-Aware Minifier Add?

**Extra optimizations**:

```typescript
// Before: 150 bytes
function f(x: string) {
    if (typeof x === "number") {
        console.log("This never runs!");
    }
    return x.toUpperCase();
}

// After: 50 bytes (dead branch removed)
function f(x){return x.toUpperCase()}
```

**Value**: 5-10% smaller bundles (significant at scale!)

---

## V. Philosophical Principles

### 1. Simple is Better
> "Perfection is achieved, not when there is nothing more to add, but when there is nothing left to take away."

**Applied**:
- Don't implement full type checking if we don't need it
- Prefer lightweight inference over complex constraint solving
- 10,000 lines of focused code > 100,000 lines of complete code

### 2. Performance Matters
> "The fastest code is the code that never runs."

**Applied**:
- Use types to eliminate dead code (it truly never runs!)
- Bump allocation for speed
- Lazy evaluation for efficiency
- Parallelization for scale

### 3. Correctness First, Optimization Second
> "Premature optimization is the root of all evil."

**Applied**:
- Get the parser correct first (Tier 1)
- Then optimize minification (Tier 2)
- Only then consider full type checking (Tier 3)

### 4. Learn from History
> "Those who cannot remember the past are condemned to repeat it."

**Applied**:
- TypeScript made single-threaded decision in 2012 - hard to fix now
- typescript-go learned this lesson - parallel from day 1
- oxc learned from swc - arena allocation from start
- We learn from all of them!

---

## VI. The Beauty of Types

Types are not just error prevention - they're a language for expressing intent.

```typescript
// Types as documentation
function fetchUser(id: UserId): Promise<User>

// Types as guardrails
type NonEmptyArray<T> = [T, ...T[]];

// Types as computation
type Reverse<T> = T extends [infer H, ...infer R]
    ? [...Reverse<R>, H]
    : [];

// Types as proof
function head<T>(arr: NonEmptyArray<T>): T {
    return arr[0];  // Always safe!
}
```

**Our goal**: Harness this beauty for practical value (faster, smaller code).

---

## VII. Conclusion

**Type parsing is not binary** - it's a spectrum from syntax to verification.

**For ecma-rs, we choose pragmatism**:
- Complete syntax (✅ done)
- Lightweight semantics (🎯 target)
- Practical pragmatics (🚀 innovation)

**Not because it's easy, but because it's the right level of complexity for the value we provide.**

---

*Next: [architecture/TYPESCRIPT.md](architecture/TYPESCRIPT.md) - How TypeScript actually works*
