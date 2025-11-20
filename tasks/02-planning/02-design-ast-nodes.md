---
task_id: "02-planning/02-design-ast-nodes"
title: "Design AST Node Extensions and New Nodes"
phase: "planning"
estimated_duration: "4-6 hours"
complexity: "medium"
dependencies:
  - "01-analysis/03-audit-ast-coverage"
  - "01-analysis/04-audit-parser-coverage"
  - "02-planning/01-prioritize-features"
inputs:
  - "../../01-analysis/03-audit-ast-coverage/missing-ast-nodes.md"
  - "../../01-analysis/04-audit-parser-coverage/unreachable-code-analysis.md"
  - "../../02-planning/01-prioritize-features/prioritized-features.json"
outputs:
  - "ast-extensions.md"
  - "new-node-definitions.rs"
  - "migration-plan.md"
  - "ast-design-decisions.md"
skills_required:
  - "Rust programming"
  - "AST design"
  - "TypeScript knowledge"
  - "API design"
---

# Task: Design AST Node Extensions and New Nodes

## Objective

Design modifications to existing AST nodes and new node definitions for missing TypeScript features, ensuring clean API, backward compatibility, and future extensibility.

## Context

### Why This Matters

Before implementing parser changes, need clear AST design:
1. **What fields to add** to existing nodes
2. **What new nodes** to create
3. **How they relate** to existing structures
4. **Backward compatibility** considerations

Good AST design:
- Makes parser implementation straightforward
- Enables future features without breaking changes
- Minimizes memory usage
- Provides clean visitor API

### Input from Analysis

From task 03 (AST audit):
- Missing node types
- Partial nodes needing fields

From task 04 (Parser audit):
- Orphaned nodes (defined but never created)
- Parser expectations

From prioritization:
- Which features to implement first
- Which can be deferred

### Design Principles

1. **Explicit over implicit**: If TypeScript has a keyword, represent it explicitly
2. **Minimal but complete**: Include all information, nothing more
3. **Flat over nested**: Avoid deep nesting where possible
4. **Consistent patterns**: Follow existing AST conventions
5. **Serde-friendly**: Must serialize to JSON cleanly

## Prerequisites

### Files to Read

1. **Current AST** (`parse-js/src/ast/type_expr.rs`)
   - Understand existing patterns
   - Note naming conventions
   - See derive macros used

2. **Analysis Outputs**
   - `missing-ast-nodes.md` - What's missing
   - `unreachable-code-analysis.md` - Orphaned nodes
   - `prioritized-features.json` - What to implement

3. **TypeScript Types**
   - `tests/TypeScript/src/compiler/types.ts` - TypeScript's own AST
   - Reference for complex cases

### TypeScript AST Reference

TypeScript's node types: https://github.com/microsoft/TypeScript/blob/main/src/compiler/types.ts

## Instructions

### Step 1: Review Current AST Patterns

Understand existing design:

```bash
cd /home/user/ecma-rs/parse-js

# Look at TypeExpr enum
awk '/pub enum TypeExpr/,/^}/' src/ast/type_expr.rs

# Look at struct patterns
grep "pub struct Type" src/ast/type_expr.rs -A 5

# Note derive macros
grep "#\[derive" src/ast/type_expr.rs | sort | uniq
```

Document patterns in **ast-design-decisions.md**:

```markdown
# AST Design Patterns

## Existing Conventions

### Naming
- Types: `Type` prefix (TypeString, TypeUnion)
- Enums: PascalCase variants
- Fields: snake_case

### Structure
- Simple types: Empty structs `TypeString {}`
- Complex types: Struct with fields
- Variants: Enum with boxed children

### Derives
```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
```

Standard derives for all AST nodes.

### Optionality
- Optional fields: `Option<T>`
- Required but possibly empty: `Vec<T>` (not `Option<Vec<T>>`)

### Location
- All nodes wrapped in `Node<T>` which includes location
- Don't duplicate location in struct

### Boxing
- Recursive types: `Box<TypeExpr>`
- Large enums: `Box<LargeStruct>`
- Small types: No boxing (copy overhead)
```

### Step 2: Design Node Extensions

For each existing node that needs extension:

**ast-extensions.md**:

```markdown
# AST Node Extensions

## Extensions to Existing Nodes

### 1. TypeParam - Add 'const' Modifier

**Current**:
```rust
pub struct TypeParam {
    pub name: String,
    pub constraint: Option<Node<TypeExpr>>,
    pub default: Option<Node<TypeExpr>>,
    pub variance: Option<Variance>,
}
```

**Extension**:
```rust
pub struct TypeParam {
    pub name: String,
    pub constraint: Option<Node<TypeExpr>>,
    pub default: Option<Node<TypeExpr>>,
    pub variance: Option<Variance>,
    pub is_const: bool,  // NEW: for `<const T>`
}
```

**Rationale**:
- TypeScript 5.0 feature
- Boolean flag sufficient (no modifier details needed)
- Default `false` for backward compatibility

**Migration**: Non-breaking (new field with default)

**Priority**: Medium (423 occurrences in real code)

---

### 2. TypeMapped - Add 'as' Clause

**Current**:
```rust
pub struct TypeMapped {
    pub readonly_modifier: Option<MappedModifier>,
    pub optional_modifier: Option<MappedModifier>,
    pub type_parameter: Node<TypeParam>,
    pub name_type: Option<Node<TypeExpr>>,  // VERIFY if exists
    pub type_expr: Option<Node<TypeExpr>>,
}
```

**Extension** (if `name_type` doesn't exist):
```rust
pub struct TypeMapped {
    pub readonly_modifier: Option<MappedModifier>,
    pub optional_modifier: Option<MappedModifier>,
    pub type_parameter: Node<TypeParam>,
    pub name_type: Option<Node<TypeExpr>>,  // NEW: for `as NewKey<K>`
    pub type_expr: Option<Node<TypeExpr>>,
}
```

**Syntax**:
```typescript
type T = { [K in keyof O as NewKey<K>]: O[K] };
//                          ^^^^^^^^^^^^
//                          name_type
```

**Rationale**:
- TypeScript 4.1 feature
- Key remapping is core use case (Omit, Pick implementation)
- Optional because not always present

**Migration**: Non-breaking if field already exists, check first!

**Priority**: Low-Medium (789 occurrences, but advanced feature)

---

### 3. TypeConstructor - Add 'abstract' Flag

**Current**:
```rust
pub struct TypeConstructor {
    pub type_parameters: Option<Vec<Node<TypeParam>>>,
    pub parameters: Vec<Node<FunctionParam>>,
    pub return_type: Node<TypeExpr>,
}
```

**Extension**:
```rust
pub struct TypeConstructor {
    pub type_parameters: Option<Vec<Node<TypeParam>>>,
    pub parameters: Vec<Node<FunctionParam>>,
    pub return_type: Node<TypeExpr>,
    pub is_abstract: bool,  // NEW: for `abstract new (): T`
}
```

**Rationale**:
- Rare but part of spec
- Boolean flag sufficient
- Default `false`

**Migration**: Non-breaking

**Priority**: Low (3-5 occurrences)

---

### 4. TypeTuple - Verify Readonly Support

**Current**:
```rust
pub struct TypeTuple {
    pub readonly: bool,  // Should exist
    pub elements: Vec<Node<TypeTupleElement>>,
}
```

**Action**: VERIFY this exists and is populated by parser

**If missing**:
```rust
pub struct TypeTuple {
    pub readonly: bool,  // ADD if missing
    pub elements: Vec<Node<TypeTupleElement>>,
}
```

**Priority**: High (892 occurrences of `readonly [T, ...U]`)

---

## Extension Summary Table

| Node | Field to Add | Type | Priority | Breaking? |
|------|--------------|------|----------|-----------|
| TypeParam | is_const | bool | Medium | No |
| TypeMapped | name_type | Option<Node<TypeExpr>> | Low-Med | Verify exists |
| TypeConstructor | is_abstract | bool | Low | No |
| TypeTuple | readonly | bool | High | Verify exists |
```

### Step 3: Design New Nodes

For completely new features:

**new-node-definitions.rs**:

```rust
// This file contains proposed new AST node definitions
// Copy these into parse-js/src/ast/type_expr.rs as needed

use serde::{Serialize, Deserialize};
use crate::ast::Node;

// ========== NEW NODES ==========

/// TypeScript 5.2: using declarations
/// Syntax: using resource = getResource();
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UsingDeclaration {
    pub is_await: bool,  // `await using` vs `using`
    pub declarations: Vec<Node<VarDeclarator>>,
}

// Add to Stmt enum:
// Using(Node<UsingDeclaration>)

// ========== COMBINED CONSTRUCTS ==========

/// typeof import(...) combination
/// Current: TypeTypeOf takes entity name
/// Issue: import() is not an entity name, it's an expression
///
/// Option A: Extend TypeTypeOf
/// Option B: New node TypeOfImport
///
/// Recommendation: Option A (simpler)
///
/// Modify TypeTypeOf:
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeTypeOf {
    // Instead of `entity_name: TypeEntityName`
    // Use more flexible:
    pub operand: TypeOfOperand,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TypeOfOperand {
    /// typeof x.y.z
    EntityName(TypeEntityName),

    /// typeof import('./module')
    Import(Box<Node<TypeImport>>),
}

// Migration: Breaking change to TypeTypeOf
// Alternative: Keep backward compatible with enum

// ========== JSDOC TYPES (if needed) ==========

/// JSDoc type annotation for JavaScript files
/// Syntax: /** @type {string} */
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JSDocType {
    pub type_expr: Node<TypeExpr>,
    pub comment: Option<String>,
}

// Note: Only needed if supporting JS file minification with type info
// Priority: Low

// ========== DECORATOR METADATA (TS 5.2) ==========

/// Decorator with metadata
/// Syntax: @decorator metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecoratorWithMetadata {
    pub decorator: Node<Decorator>,
    pub metadata: Option<Node<Expr>>,  // TS 5.2 feature
}

// Priority: Very Low (156 occurrences, experimental)
```

### Step 4: Document Design Decisions

**ast-design-decisions.md** (continued):

```markdown
## Design Decisions

### Decision 1: Boolean Flags vs Enum for Modifiers

**Question**: `is_const: bool` vs `modifier: Option<ConstModifier>`?

**Decision**: Boolean flags

**Rationale**:
- TypeScript uses keywords, not modifier objects
- Simpler to work with: `if param.is_const`
- Less memory overhead
- Precedent: `is_abstract`, `is_async` in existing code

**Trade-off**: Less extensible if modifier gains parameters later

---

### Decision 2: typeof import() Representation

**Question**: New node vs extend existing TypeTypeOf?

**Decision**: Extend TypeTypeOf with enum operand

**Options**:
```rust
// Option A: Enum operand (CHOSEN)
pub struct TypeTypeOf {
    pub operand: TypeOfOperand,  // EntityName | Import
}

// Option B: New node
pub struct TypeOfImport {
    pub import_type: Box<Node<TypeImport>>,
}

// Option C: Optional import field
pub struct TypeTypeOf {
    pub entity_name: Option<TypeEntityName>,
    pub import_type: Option<Box<Node<TypeImport>>>,
}
```

**Rationale for A**:
- Cleaner API (one field, not two options)
- Type-safe (can't have both)
- Extensible (can add more operand types)
- Migration: Breaking but clean

**Alternative**: If backward compatibility critical, use Option C

---

### Decision 3: Using Declarations - Stmt or Decl?

**Question**: Where does UsingDeclaration live?

**Decision**: Stmt variant

**Rationale**:
- Runtime behavior (resource management)
- Similar to VarDecl (also in Stmt)
- Not purely type-level

**Location**: `parse-js/src/ast/stmt.rs`

---

### Decision 4: Mapped Type 'as' Clause

**Question**: Verify if `name_type` already exists

**Decision**: Check code first, only add if missing

**Process**:
```bash
grep -n "name_type" parse-js/src/ast/type_expr.rs
```

**If exists**: Document, nothing to add
**If missing**: Add as optional field

---

### Decision 5: Const Type Parameters

**Question**: Place in TypeParam or separate node?

**Decision**: Field in TypeParam

**Rationale**:
- Modifies existing concept (type parameter)
- Not a new kind of parameter
- Follows pattern of variance (also field in TypeParam)

---

## Memory Considerations

### Size Impact Analysis

```rust
// Before extensions:
size_of::<TypeParam>() = 48 bytes

// After adding is_const:
size_of::<TypeParam>() = 48 bytes  // Still fits in padding

// TypeMapped with name_type:
// Before: 64 bytes
// After: 72 bytes  // +1 pointer for Option

// Impact: Minimal for most nodes
```

### Optimization Opportunities

- Use bitflags for multiple booleans
- Consider enum packing
- Profile actual memory impact after implementation

---

## Backward Compatibility Strategy

### Non-Breaking Extensions

✅ Add fields with default values:
```rust
pub struct TypeParam {
    // existing fields...
    pub is_const: bool,  // defaults to false
}
```

✅ Add optional fields:
```rust
pub struct TypeMapped {
    // existing fields...
    pub name_type: Option<Node<TypeExpr>>,  // defaults to None
}
```

### Breaking Changes

❌ Changing field types:
```rust
// Before:
pub entity_name: TypeEntityName,

// After:
pub operand: TypeOfOperand,  // BREAKING
```

**Mitigation**:
- Version AST if needed
- Provide migration script
- Document breaking changes

### Migration Strategy

For typeof import():

**Option 1: Breaking (clean)**
- Change TypeTypeOf.entity_name → operand
- Update all parser code
- Version bump

**Option 2: Compatible (ugly)**
- Add new field, deprecate old
- Support both during transition
- Remove old in future version

**Recommendation**: Option 1 (this is pre-1.0, breaking OK)

---

## Testing Strategy

### For Each Extension

1. **Unit tests**: New fields populated correctly
2. **Serialization**: JSON output includes new fields
3. **Visitor**: Visitor pattern still works
4. **Parser**: Parser creates new fields

### Example Test

```rust
#[test]
fn test_const_type_parameter() {
    let ast = TypeParam {
        name: "T".to_string(),
        constraint: None,
        default: None,
        variance: None,
        is_const: true,  // New field
    };

    // Serialize to JSON
    let json = serde_json::to_string(&ast).unwrap();
    assert!(json.contains("is_const"));
    assert!(json.contains("true"));
}
```

---

## Implementation Checklist

For each extension/new node:

- [ ] Design documented
- [ ] Rationale provided
- [ ] Memory impact assessed
- [ ] Backward compatibility considered
- [ ] Test strategy defined
- [ ] Code examples written
- [ ] Migration plan (if breaking)
```

### Step 5: Create Migration Plan

**migration-plan.md**:

```markdown
# AST Migration Plan

## Overview

Plan for implementing AST changes with minimal disruption.

## Phase 1: Non-Breaking Extensions (Week 1)

### Add New Fields to Existing Nodes

1. **TypeParam.is_const**
   - File: `src/ast/type_expr.rs`
   - Change: Add `pub is_const: bool,`
   - Default: `false`
   - Impact: None (non-breaking)

2. **TypeConstructor.is_abstract**
   - File: `src/ast/type_expr.rs`
   - Change: Add `pub is_abstract: bool,`
   - Default: `false`
   - Impact: None (non-breaking)

3. **TypeMapped.name_type** (if missing)
   - File: `src/ast/type_expr.rs`
   - Change: Add `pub name_type: Option<Node<TypeExpr>>,`
   - Default: `None`
   - Impact: None (non-breaking)
   - **Action**: Verify first if exists!

4. **TypeTuple.readonly** (if missing)
   - File: `src/ast/type_expr.rs`
   - Change: Add `pub readonly: bool,`
   - Default: `false`
   - Impact: None (non-breaking)
   - **Action**: Verify first if exists!

### Verification Script

```bash
#!/bin/bash
# verify_ast_fields.sh

check_field() {
    struct=$1
    field=$2
    file="parse-js/src/ast/type_expr.rs"

    if awk "/pub struct $struct/,/^}/" "$file" | grep -q "$field"; then
        echo "✅ $struct.$field EXISTS"
        return 0
    else
        echo "❌ $struct.$field MISSING - need to add"
        return 1
    fi
}

check_field "TypeParam" "is_const"
check_field "TypeMapped" "name_type"
check_field "TypeTuple" "readonly"
check_field "TypeConstructor" "is_abstract"
```

## Phase 2: New Nodes (Week 1-2)

### Add New Enum Variants

1. **Stmt::Using**
   - File: `src/ast/stmt.rs`
   - Add variant: `Using(Node<UsingDeclaration>),`
   - Add struct definition for `UsingDeclaration`

### Add New Structs

1. **UsingDeclaration**
```rust
// In src/ast/stmt.rs
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UsingDeclaration {
    pub is_await: bool,
    pub declarations: Vec<Node<VarDeclarator>>,
}
```

## Phase 3: Breaking Changes (Week 2)

### TypeTypeOf Redesign

**Current**:
```rust
pub struct TypeTypeOf {
    pub entity_name: TypeEntityName,
}
```

**New**:
```rust
pub struct TypeTypeOf {
    pub operand: TypeOfOperand,
}

pub enum TypeOfOperand {
    EntityName(TypeEntityName),
    Import(Box<Node<TypeImport>>),
}
```

**Migration Steps**:

1. Define TypeOfOperand enum
2. Change TypeTypeOf.entity_name → operand
3. Update parser to use new structure
4. Update tests
5. Update visitors if custom visitors exist

**Breaking Mitigation**:

Temporary compatibility:
```rust
impl TypeTypeOf {
    // Deprecated helper
    pub fn entity_name(&self) -> Option<&TypeEntityName> {
        match &self.operand {
            TypeOfOperand::EntityName(name) => Some(name),
            _ => None,
        }
    }
}
```

## Phase 4: Testing & Validation (Week 2)

### Test Checklist

For each changed node:

- [ ] Unit test for new field
- [ ] Serialization test (JSON)
- [ ] Deserialization test
- [ ] Visitor test (if using visitors)
- [ ] Parser test (populate new field)

### Example Tests

```rust
// Test new field
#[test]
fn type_param_const_modifier() {
    let param = TypeParam {
        name: "T".into(),
        constraint: None,
        default: None,
        variance: None,
        is_const: true,
    };

    assert!(param.is_const);

    // Serialization
    let json = serde_json::to_value(&param).unwrap();
    assert_eq!(json["is_const"], true);
}

// Test typeof import
#[test]
fn typeof_import_combination() {
    let import_type = TypeImport { /* ... */ };
    let typeof_node = TypeTypeOf {
        operand: TypeOfOperand::Import(Box::new(import_type)),
    };

    // Should serialize correctly
    let json = serde_json::to_string(&typeof_node).unwrap();
    assert!(json.contains("Import"));
}
```

## Phase 5: Documentation (Week 2)

### Update Documentation

1. **AST Reference** (if exists)
   - Document new fields
   - Document new nodes
   - Update examples

2. **Changelog**
   - List all AST changes
   - Mark breaking changes
   - Provide migration guide

3. **Code Comments**
   - Add doc comments to new fields
   - Reference TypeScript version

Example:
```rust
/// TypeScript 5.0: const type parameter modifier
///
/// Syntax: `<const T extends readonly any[]>`
///
/// When `true`, the type parameter has the `const` modifier,
/// which affects type inference for generic functions.
pub is_const: bool,
```

## Timeline

| Week | Phase | Deliverables |
|------|-------|--------------|
| 1 | Non-breaking extensions | New fields added, tested |
| 1-2 | New nodes | UsingDeclaration added |
| 2 | Breaking changes | TypeTypeOf redesigned |
| 2 | Testing | All tests passing |
| 2 | Documentation | Docs updated |

## Risk Mitigation

### Risk: Field already exists

**Mitigation**: Run verification script first

### Risk: Breaking change impacts users

**Mitigation**:
- Clearly document in changelog
- Provide migration examples
- Version bump (0.x.0 → 0.y.0)

### Risk: Parser changes don't match AST

**Mitigation**:
- Design AST first (this task)
- Design parser next (task 03-plan-parser-extensions)
- Cross-reference both plans

## Rollback Plan

If AST changes cause issues:

1. Revert commits (git)
2. Keep working branch
3. Fix issues
4. Re-apply with fixes

All changes in feature branch until validated.

## Success Criteria

- [ ] All planned extensions documented
- [ ] All new nodes defined
- [ ] Migration plan clear
- [ ] Tests planned
- [ ] No unintended breaking changes
- [ ] Ready for parser implementation
```

## Acceptance Criteria

### Required Outputs

✅ **ast-extensions.md**: All extensions to existing nodes

✅ **new-node-definitions.rs**: Complete new node code

✅ **migration-plan.md**: Step-by-step implementation plan

✅ **ast-design-decisions.md**: Rationale for all decisions

### Quality Checks

- [ ] Every extension has rationale
- [ ] New nodes have complete struct definitions
- [ ] Breaking changes identified
- [ ] Memory impact assessed
- [ ] Test strategy for each change
- [ ] Migration steps clear

### Success Metrics

- AST design complete
- Ready for implementation
- Parser team can start work (task 03)
- No ambiguity in spec

## Common Issues & Solutions

### Issue: Unsure if field already exists

**Solution**:
```bash
grep -A 10 "pub struct TypeName" parse-js/src/ast/type_expr.rs
```

### Issue: Multiple design options

**Solution**: Document all, pick one, note trade-offs

### Issue: TypeScript spec unclear

**Solution**:
- Check TypeScript source code
- Try in TypeScript playground
- Look at test cases

### Issue: Backward compatibility concern

**Solution**:
- Prefer non-breaking (optional fields, defaults)
- If breaking needed, document migration clearly
- Consider compatibility helpers

## Time Estimate Breakdown

- Review current AST: 1 hour
- Design extensions: 2 hours
- Design new nodes: 1 hour
- Document decisions: 1 hour
- Create migration plan: 1 hour
- Review & polish: 30 min

**Total: 4-6 hours**

## Downstream Impact

Critical for:
- **03-plan-parser-extensions**: Parser must populate these nodes
- **04-define-test-strategy**: Tests must cover new nodes
- **03-implementation/***: Actual implementation follows this design

## Notes for Agent

- Be thorough - implementation depends on this
- When unsure, document options and pick one
- Verify existing code before assuming missing
- Memory impact matters for large files
- Your design choices affect months of work

---

**Ready?** Start with Step 1: Review Current AST Patterns
